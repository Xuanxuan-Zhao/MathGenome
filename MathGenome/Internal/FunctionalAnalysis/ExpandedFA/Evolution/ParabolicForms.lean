import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.ParabolicForms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.ParabolicGalerkinExistence
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Uniqueness and the separable measurability bridge complete the
nonautonomous parabolic form theorem. -/
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology
universe u v w
namespace ExpandedFA.Evolution.ParabolicForms
open ParabolicGalerkinSpec HilbertTripleTraceSpec ParabolicGalerkin

/-- A Hilbert-valued version of the separable Pettis measurability implication.
Countably many evaluations on a dense sequence separate points. The continuous
injection into their product is a Borel embedding (Lusin–Souslin). -/
theorem aestronglyMeasurable_of_inner
    {X : Type w} [MeasurableSpace X] {μ : Measure X}
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [SeparableSpace V] (g : X → V)
    (hg : ∀ y, AEMeasurable (fun t => inner ℝ (g t) y) μ) :
    AEStronglyMeasurable g μ := by
  borelize V
  let e : V → (ℕ → ℝ) := fun x n => inner ℝ x (denseSeq V n)
  have he : Continuous e := continuous_pi fun n => continuous_id.inner continuous_const
  have hei : Function.Injective e := by
    intro x y hxy
    exact (denseRange_denseSeq V).eq_of_inner_left ℝ (congrFun hxy)
  have hem : MeasurableEmbedding e := he.measurableEmbedding hei
  apply AEMeasurable.aestronglyMeasurable
  apply hem.aemeasurable_comp_iff.mp
  exact aemeasurable_pi_iff.mpr (fun n => hg (denseSeq V n))

/-- Scalar form measurability gives strong operator trajectories on separable V. -/
theorem separable_operator_measurability :
    ParabolicFormsSpec.SeparableMeasurabilityExpected.{u} := by
  intro V _ _ _ _ T a M hscalar hbound x
  let g : ℝ → V := fun t =>
    (InnerProductSpace.toDual ℝ V).symm (formOperator a M t x)
  have hg : AEStronglyMeasurable g (HilbertTripleSpec.timeMeasureValue T) := by
    apply aestronglyMeasurable_of_inner
    intro y
    apply (hscalar x y).congr
    filter_upwards [hbound] with t ht
    simp only [g, InnerProductSpace.toDual_symm_apply,
      formOperator_apply a M t ht]
  simpa only [g, LinearIsometryEquiv.apply_symm_apply] using
    (InnerProductSpace.toDual ℝ V).continuous.comp_aestronglyMeasurable hg

/-- Subtraction of vector-valued distributional derivatives. -/
theorem hasTimeDerivative_sub {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (T : ℝ) (u v g h : ℝ → E)
    (hu : HasTimeDerivative T u g) (hv : HasTimeDerivative T v h) :
    HasTimeDerivative T (u - v) (g - h) := by
  refine ⟨hu.1.sub hv.1, hu.2.1.sub hv.2.1, ?_⟩
  intro φ hφ
  have hiu := hasTimeDerivative_test_integrable T u g hu φ hφ
  have hiv := hasTimeDerivative_test_integrable T v h hv φ hφ
  simp only [timeMeasure] at hiu hiv
  simp only [Pi.sub_apply, smul_sub]
  rw [integral_sub hiu.1 hiv.1, integral_sub hiu.2 hiv.2,
    hu.2.2 φ hφ, hv.2.2 φ hφ]
  abel

section Uniqueness
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Subtraction in the actual Bochner quotient respects the derivative graph. -/
theorem tripleDerivative_sub (j : HilbertTriple V H) (T : ℝ)
    (u v : HilbertTripleSpec.timeLpValue V 2 T)
    (g h : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
    (hu : HilbertTripleSpec.tripleDerivativeValue j T u g)
    (hv : HilbertTripleSpec.tripleDerivativeValue j T v h) :
    HilbertTripleSpec.tripleDerivativeValue j T (u - v) (g - h) := by
  have hd := hasTimeDerivative_sub T _ _ _ _ hu hv
  apply (hasTimeDerivative_congr T _ _ _ _ ?_ (Lp.coeFn_sub g h).symm).mp hd
  filter_upwards [Lp.coeFn_sub u v] with t ht
  simp only [Pi.sub_apply, ht, map_sub]

/-- Proof fields carry no extra choice of solution once these three data agree. -/
theorem weakSolution_ext {j : HilbertTriple V H} {T : ℝ} {hT : 0 ≤ T}
    {a : BilinearForms V} {M : ℝ}
    {f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T} {u₀ : H}
    (z w : WeakSolution j T hT a M f u₀)
    (hu : z.value = w.value) (hg : z.derivative = w.derivative)
    (hc : z.curve = w.curve) : z = w := by
  cases z
  cases w
  congr

/-- At zero time the equation has no interior constraint, but its initial datum
fixes the entire singleton curve. -/
theorem weakSolution_unique_zero (j : HilbertTriple V H)
    (a : BilinearForms V) (M : ℝ)
    (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 0) (u₀ : H)
    (z w : WeakSolution j 0 le_rfl a M f u₀) : z = w := by
  have hμ : HilbertTripleSpec.timeMeasureValue 0 = 0 := by
    simp [HilbertTripleSpec.timeMeasureValue]
  apply weakSolution_ext z w
  · apply Lp.ext
    simp [hμ, Filter.EventuallyEq]
  · apply Lp.ext
    simp [hμ, Filter.EventuallyEq]
  · ext t
    have ht : t = ⟨0, by simp⟩ := by
      apply Subtype.ext
      exact le_antisymm t.property.2 t.property.1
    simpa only [ht] using z.initial.trans w.initial.symm

/-- Zero forcing and zero initial value force the difference to vanish by the
energy estimate. This uses no compact embedding or countable Hilbert basis. -/
theorem weakSolution_unique_pos (j : HilbertTriple V H) (T : ℝ)
    (hT : 0 ≤ T) (hTpos : 0 < T) (a : BilinearForms V) (M α C : ℝ)
    (ha : FormHypotheses j T a M α C)
    (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H)
    (z w : WeakSolution j T hT a M f u₀) : z = w := by
  let u := z.value - w.value
  let g := z.derivative - w.derivative
  let c := z.curve - w.curve
  have hd : HilbertTripleSpec.tripleDerivativeValue j T u g :=
    tripleDerivative_sub j T _ _ _ _ z.has_derivative w.has_derivative
  have hc : Represents j T u c :=
    triple_represents_sub j T _ _ _ _ z.represents w.represents
  obtain ⟨tr, _, htruniq, _, he⟩ := hilbertTriple_trace j T hTpos
  let q : HilbertTripleSpec.energySpaceValue j T := ⟨(u, g), hd⟩
  have htrace : c = tr q := htruniq q c hc
  have hec : ∀ s t : Set.Icc 0 T,
      ‖c t‖ ^ 2 - ‖c s‖ ^ 2 = 2 * ∫ r in s.val..t.val, g r (u r) := by
    intro s t
    simpa only [← htrace, q, energyDensity] using (he q s t).2
  have hinit : ‖c ⟨0, by simp [hT]⟩‖ ≤ ‖(0 : H)‖ := by
    simp [c, z.initial, w.initial]
  have hge : ∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T,
      g t = (0 : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) t -
        formOperator a M t (u t) := by
    filter_upwards [z.equation, w.equation,
      Lp.coeFn_sub z.value w.value, Lp.coeFn_sub z.derivative w.derivative,
      Lp.coeFn_zero (StrongDual ℝ V) 2 (HilbertTripleSpec.timeMeasureValue T)]
      with t hz hw huv hgh h0
    simp only [u, g, huv, hgh, Pi.sub_apply, hz, hw, h0, Pi.zero_apply, map_sub]
    abel
  obtain ⟨K, _, hK⟩ := parabolic_curve_bound j T hT a M α C ha
  have hb := hK u 0 g c 0 hc hinit hge hec
  have hzero : ‖c‖ + ‖u‖ ≤ 0 := by simpa using hb
  have hu : z.value = w.value := sub_eq_zero.mp
    (norm_eq_zero.mp (le_antisymm (by linarith [norm_nonneg c]) (norm_nonneg u)))
  have hcurve : z.curve = w.curve := sub_eq_zero.mp
    (norm_eq_zero.mp (le_antisymm (by linarith [norm_nonneg u]) (norm_nonneg c)))
  apply weakSolution_ext z w hu ?_ hcurve
  apply Lp.ext
  filter_upwards [z.equation, w.equation] with t hz hw
  rw [hz, hw, hu]

end Uniqueness

/-- Uniqueness of the full solution, including its endpoints and derivative. -/
theorem solution_unique : ParabolicFormsSpec.UniquenessExpected.{u,v} := by
  intro V H _ _ _ _ _ _ j T hT a M α C ha f u₀ z w
  rcases eq_or_lt_of_le hT with hzero | hpos
  · subst T
    exact weakSolution_unique_zero j a M f u₀ z w
  · exact weakSolution_unique_pos j T hT hpos a M α C ha f u₀ z w

/-- The full nonautonomous parabolic form theorem with a parameter-uniform
bound and explicit strong measurability for nonseparable spaces. -/
theorem parabolic_wellposedness : ParabolicFormsSpec.WellposednessExpected.{u,v} := by
  intro V H _ _ _ _ _ _ j T hT M α C
  obtain ⟨K, hK, hex⟩ := galerkin_existence j T hT M α C
  refine ⟨K, hK, ?_⟩
  intro a ha f u₀
  obtain ⟨G, z, _, hb, _⟩ := hex a ha f u₀
  exact ⟨z, hb, fun w => solution_unique j T hT a M α C ha f u₀ w z⟩

/-- On separable V the original scalar form measurability suffices. -/
theorem separable_parabolic_wellposedness :
    ParabolicFormsSpec.SeparableWellposednessExpected.{u,v} := by
  intro V H _ _ _ _ _ _ _ j T hT M α C
  obtain ⟨K, hK, hex⟩ := parabolic_wellposedness j T hT M α C
  refine ⟨K, hK, ?_⟩
  intro a hα hscalar hbound
  apply hex a
  exact ⟨hα, hscalar, hbound,
    separable_operator_measurability T a M hscalar (hbound.mono fun _ ht => ht.1)⟩

end ExpandedFA.Evolution.ParabolicForms
