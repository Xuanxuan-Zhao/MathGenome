import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HilbertTriple
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerIntegral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-! The real dense Hilbert triple and its Bochner/distributional time spaces. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology ContDiff
universe u v w

namespace ExpandedFA.Evolution

section Triple
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def mkHilbertTriple (J : V →L[ℝ] H) (hi : Function.Injective J) (hd : DenseRange J) :
    HilbertTriple V H := ⟨J, hi, hd⟩

def pivotInjection (j : HilbertTriple V H) : H →L[ℝ] StrongDual ℝ V :=
  HilbertTripleSpec.pivotValue j

def intoDual (j : HilbertTriple V H) : V →L[ℝ] StrongDual ℝ V :=
  (pivotInjection j).comp j.embedding

@[simp] theorem pivotInjection_apply (j : HilbertTriple V H) (h : H) (v : V) :
    pivotInjection j h v = inner ℝ h (j.embedding v) := by
  change inner ℝ ((ContinuousLinearMap.adjoint j.embedding) h) v = _
  exact j.embedding.adjoint_inner_left v h

theorem pivotInjection_injective (j : HilbertTriple V H) :
    Function.Injective (pivotInjection j) := by
  intro h k heq
  apply Dense.eq_of_inner_left (𝕜 := ℝ) j.denseRange
  rintro _ ⟨v, rfl⟩
  simpa only [pivotInjection_apply] using congrArg (fun f : StrongDual ℝ V => f v) heq

theorem pivotInjection_denseRange (j : HilbertTriple V H) :
    DenseRange (pivotInjection j) := by
  have hker : j.embedding.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr j.injective
  have hd : DenseRange (ContinuousLinearMap.adjoint j.embedding) := by
    change Dense ((ContinuousLinearMap.adjoint j.embedding).range : Set V)
    rw [Submodule.dense_iff_topologicalClosure_eq_top, ← j.embedding.orthogonal_ker,
      hker]
    simp
  exact (InnerProductSpace.toDual ℝ V).surjective.denseRange.comp hd
    (InnerProductSpace.toDual ℝ V).continuous

theorem intoDual_injective_denseRange (j : HilbertTriple V H) :
    Function.Injective (intoDual j) ∧ DenseRange (intoDual j) :=
  ⟨(pivotInjection_injective j).comp j.injective,
    (pivotInjection_denseRange j).comp j.denseRange (pivotInjection j).continuous⟩

@[simp] theorem intoDual_apply (j : HilbertTriple V H) (u v : V) :
    intoDual j u v = inner ℝ (j.embedding u) (j.embedding v) :=
  pivotInjection_apply j (j.embedding u) v

theorem triple_norm_bounds (j : HilbertTriple V H) (v : V) (h : H)
    (f : StrongDual ℝ V) :
    ‖j.embedding v‖ ≤ ‖j.embedding‖ * ‖v‖ ∧
    ‖pivotInjection j h‖ ≤ ‖j.embedding‖ * ‖h‖ ∧
    ‖f v‖ ≤ ‖f‖ * ‖v‖ := by
  refine ⟨j.embedding.le_opNorm v, ?_, f.le_opNorm v⟩
  change ‖(InnerProductSpace.toDual ℝ V) ((ContinuousLinearMap.adjoint j.embedding) h)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa using (ContinuousLinearMap.adjoint j.embedding).le_opNorm h

end Triple

def timeMeasure := HilbertTripleSpec.timeMeasureValue
abbrev TimeLp : HilbertTripleSpec.TimeLpExpected.{w} := HilbertTripleSpec.timeLpValue

theorem timeLp_strongMeasurable {E : Type w} [NormedAddCommGroup E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : ℝ) (u : TimeLp E p T) :
    FunctionSpaces.StrongMeasurable (timeMeasure T) u :=
  (FunctionSpaces.strongMeasurable_identification _ _).mpr (Lp.aestronglyMeasurable u)

def IsTimeTest := HilbertTripleSpec.testValue

def HasTimeDerivative : HilbertTripleSpec.DerivativeExpected.{w} :=
  HilbertTripleSpec.derivativeValue

abbrev TimeSobolev : HilbertTripleSpec.SobolevExpected.{w} := HilbertTripleSpec.sobolevValue

def timeSobolevNorm : HilbertTripleSpec.SobolevNormExpected.{w} :=
  HilbertTripleSpec.sobolevNormValue

/-- A scalar test supported in the interval can multiply any locally
integrable vector trajectory, without a separability assumption. -/
private theorem test_smul_integrable {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : ℝ} {g : ℝ → E} {φ : ℝ → ℝ}
    (hg : LocallyIntegrableOn g (Set.Ioo 0 T))
    (hφ : IsTimeTest T φ) : Integrable (fun t => φ t • g t) := by
  apply (integrableOn_iff_integrable_of_support_subset (s := tsupport φ) ?_).mp
    ((hg.integrableOn_compact_subset hφ.2.2 hφ.2.1).continuousOn_smul
      hφ.1.continuous.continuousOn hφ.2.1)
  intro t ht
  exact subset_tsupport φ (fun heq => ht (by simp [heq]))

theorem hasTimeDerivative_test_integrable {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (T : ℝ) (u g : ℝ → E) (hd : HasTimeDerivative T u g)
    (φ : ℝ → ℝ) (hφ : IsTimeTest T φ) :
    Integrable (fun t => deriv φ t • u t) (timeMeasure T) ∧
      Integrable (fun t => φ t • g t) (timeMeasure T) := by
  have hdφ : IsTimeTest T (deriv φ) :=
    ⟨hφ.1.deriv', hφ.2.1.deriv, tsupport_deriv_subset.trans hφ.2.2⟩
  exact ⟨(test_smul_integrable hd.1 hdφ).restrict,
    (test_smul_integrable hd.2.1 hφ).restrict⟩

theorem hasTimeDerivative_congr {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (u u' g g' : ℝ → E)
    (hu : u =ᵐ[timeMeasure T] u') (hg : g =ᵐ[timeMeasure T] g') :
    HasTimeDerivative T u g ↔ HasTimeDerivative T u' g' := by
  have forward (u u' g g' : ℝ → E)
      (hu : u =ᵐ[timeMeasure T] u') (hg : g =ᵐ[timeMeasure T] g')
      (hd : HasTimeDerivative T u g) : HasTimeDerivative T u' g' := by
    refine ⟨hd.1.congr hu, hd.2.1.congr hg, ?_⟩
    intro φ hφ
    have h₁ := integral_congr_ae (hu.mono fun t ht => congrArg (deriv φ t • ·) ht)
    have h₂ := integral_congr_ae (hg.mono fun t ht => congrArg (φ t • ·) ht)
    exact h₁.symm.trans ((hd.2.2 φ hφ).trans (congrArg Neg.neg h₂))
  exact ⟨forward u u' g g' hu hg, forward u' u g' g hu.symm hg.symm⟩

theorem hasTimeDerivative_unique {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (T : ℝ) (u g h : ℝ → E)
    (hg : HasTimeDerivative T u g) (hh : HasTimeDerivative T u h) :
    g =ᵐ[timeMeasure T] h := by
  have hz : ∀ᵐ t, t ∈ Set.Ioo 0 T → (g - h) t = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hg.2.1.sub hh.2.1)
    intro φ hdiff hcompact hsupp
    have htest : IsTimeTest T φ := ⟨hdiff, hcompact, hsupp⟩
    have hzero : ∀ t, t ∉ Set.Ioo 0 T → φ t • (g - h) t = 0 := by
      intro t ht
      have htφ : φ t = 0 := by
        by_contra hn
        exact ht (hsupp (subset_tsupport φ hn))
      simp [htφ]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    change (∫ t, φ t • (g t - h t) ∂timeMeasure T) = 0
    simp_rw [smul_sub]
    change (∫ t in Set.Ioo 0 T, φ t • g t - φ t • h t) = 0
    rw [integral_sub ((test_smul_integrable hg.2.1 htest).restrict (s := Set.Ioo 0 T))
      ((test_smul_integrable hh.2.1 htest).restrict (s := Set.Ioo 0 T)), sub_eq_zero]
    exact neg_injective ((hg.2.2 φ htest).symm.trans (hh.2.2 φ htest))
  exact (ae_restrict_iff' measurableSet_Ioo).mpr
    (hz.mono fun t ht hm => sub_eq_zero.mp (ht hm))

theorem timeSobolev_ext {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : ℝ)
    (u v : TimeSobolev E p T) (hu : u.val.1 = v.val.1) : u = v := by
  apply Subtype.ext
  apply Prod.ext hu
  apply Lp.ext
  have hu' := u.property
  rw [hu] at hu'
  exact hasTimeDerivative_unique T _ _ _ hu' v.property

section TripleTime
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def HasTripleTimeDerivative : HilbertTripleSpec.TripleDerivativeExpected (V := V) (H := H) :=
  HilbertTripleSpec.tripleDerivativeValue

abbrev EnergySpace : HilbertTripleSpec.EnergySpaceExpected (V := V) (H := H) :=
  HilbertTripleSpec.energySpaceValue

def energyNorm : HilbertTripleSpec.EnergyNormExpected (V := V) (H := H) :=
  HilbertTripleSpec.energyNormValue

theorem energySpace_ext (j : HilbertTriple V H) (T : ℝ)
    (u v : EnergySpace j T) (hu : u.val.1 = v.val.1) : u = v := by
  apply Subtype.ext
  apply Prod.ext hu
  apply Lp.ext
  have hu' := u.property
  dsimp only [HilbertTripleSpec.tripleDerivativeValue] at hu'
  rw [hu] at hu'
  exact hasTimeDerivative_unique T _ _ _ hu' v.property

theorem tripleDerivative_pairing (j : HilbertTriple V H) (T : ℝ)
    (u : TimeLp V 2 T) (g : TimeLp (StrongDual ℝ V) 2 T)
    (hd : HasTripleTimeDerivative j T u g) (v : V) (φ : ℝ → ℝ)
    (hφ : IsTimeTest T φ) :
    (∫ t, deriv φ t * inner ℝ (j.embedding (u t)) (j.embedding v) ∂timeMeasure T) =
      -(∫ t, φ t * g t v ∂timeMeasure T) := by
  have hi := hasTimeDerivative_test_integrable T _ _ hd φ hφ
  have heq := congrArg (fun f : StrongDual ℝ V => f v) (hd.2.2 φ hφ)
  change (∫ t, deriv φ t • intoDual j (u t) ∂timeMeasure T) v =
    (-(∫ t, φ t • g t ∂timeMeasure T)) v at heq
  have hiu : Integrable (fun t => deriv φ t • intoDual j (u t)) (timeMeasure T) := hi.1
  rw [ContinuousLinearMap.integral_apply hiu, neg_apply,
    ContinuousLinearMap.integral_apply hi.2] at heq
  simpa only [smul_apply, smul_eq_mul, intoDual_apply] using heq

end TripleTime
end ExpandedFA.Evolution
