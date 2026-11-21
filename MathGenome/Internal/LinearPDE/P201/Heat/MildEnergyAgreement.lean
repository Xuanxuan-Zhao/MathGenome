import MathGenome.Internal.LinearPDE.P201Specs.Heat.MildEnergyAgreement
import MathGenome.Internal.LinearPDE.P201.Heat.SpectralSemigroup
import MathGenome.Internal.LinearPDE.P201.Heat.ParabolicForms
import MathGenome.Internal.LinearPDE.P201.Common.IntegratedMild

noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
universe u v
namespace P201.Heat.MildEnergyAgreement
open ExpandedFA.Evolution ExpandedFA.Semigroups
open HilbertTripleSpec HilbertTripleTraceSpec ParabolicGalerkinSpec
open P201.Common.IntegratedMild

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- On the finite time interval the selected L² representative is integrable. -/
theorem timeLp_integrable {E : Type*} [NormedAddCommGroup E]
    (T : ℝ) (q : timeLpValue E 2 T) : Integrable q (timeMeasureValue T) := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo 0 T)))
  exact (Lp.memLp q).integrable (by norm_num)

/-- The weak derivative gives increments of the pivot of the continuous
H representative, including both endpoints. -/
theorem energy_increment (d : CoerciveForm V H) (T : ℝ) (hT : 0 < T)
    (u₀ : H) (f : ℝ → H) (z : EnergySolution d T hT.le u₀ f)
    (s t : Icc 0 T) :
    pivotValue (triple d) (z.curve t) - pivotValue (triple d) (z.curve s) =
      ∫ r in s.val..t.val, z.derivative r := by
  have hu := (intoDual (triple d)).integrable_comp (timeLp_integrable T z.value)
  obtain ⟨P, hPc, hrep, hinc⟩ := hasTimeDerivative_continuous_primitive T
    (fun r => intoDualValue (triple d) (z.value r)) z.derivative
    hu (timeLp_integrable T z.derivative) z.has_derivative
  have heq : (fun r => pivotValue (triple d) (extendCurve z.curve r))
      =ᵐ[timeMeasureValue T] P := by
    filter_upwards [z.represents, hrep] with r hr hp
    rw [hr]
    exact hp
  have hc : ContinuousOn (fun r => pivotValue (triple d) (extendCurve z.curve r))
      (Icc 0 T) :=
    (pivotValue (triple d)).continuous.comp_continuousOn (extendCurve_continuousOn z.curve)
  have hopen : EqOn (fun r => pivotValue (triple d) (extendCurve z.curve r)) P
      (Ioo 0 T) := Measure.eqOn_open_of_ae_eq heq isOpen_Ioo
        (hc.mono Ioo_subset_Icc_self) (hPc.continuousOn)
  have hclosed : EqOn (fun r => pivotValue (triple d) (extendCurve z.curve r)) P
      (Icc 0 T) := by
    apply hopen.of_subset_closure hc hPc.continuousOn Ioo_subset_Icc_self
    rw [closure_Ioo (ne_of_lt hT)]
  simpa only [← hclosed t.property, ← hclosed s.property, extendCurve_apply]
    using hinc s t

/-- Integrating the energy equation places the H primitive in the exact
associated-operator domain. This avoids any compactness hypothesis. -/
theorem energy_primitive_graph (d : CoerciveForm V H) (T : ℝ) (hT : 0 < T)
    (u₀ : H) (f : ℝ → H) (hf : IntegrableOn f (Icc 0 T))
    (z : EnergySolution d T hT.le u₀ f) (t : Icc 0 T) :
    (primitive (𝕜 := ℝ) (extendCurve z.curve) t,
      primitive (𝕜 := ℝ) f t - z.curve t + u₀) ∈ d.operator.graph := by
  let s : Icc 0 T := ⟨0, by simp [hT.le]⟩
  have hvi := timeLp_intervalIntegrable T z.value s t
  have hfi : IntervalIntegrable f volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le t.property.1).mpr
      (hf.mono_set (Icc_subset_Icc le_rfl t.property.2))
  let v : V := ∫ r in (0 : ℝ)..t.val, z.value r
  have hv : d.j v = primitive (𝕜 := ℝ) (extendCurve z.curve) t := by
    change d.j (∫ r in (0 : ℝ)..t.val, z.value r) = _
    rw [← d.j.intervalIntegral_comp_comm hvi]
    exact time_integral_congr_ae T z.represents.symm s t
  have hint := energy_increment d T hT u₀ f z s t
  rw [z.initial] at hint
  have heq := time_integral_congr_ae T z.equation s t
  have hpi : IntervalIntegrable (fun r => pivotValue (triple d) (f r)) volume 0 t :=
    ⟨(pivotValue (triple d)).integrable_comp hfi.1,
      (pivotValue (triple d)).integrable_comp hfi.2⟩
  have hai : IntervalIntegrable (fun r => d.a (z.value r)) volume 0 t :=
    ⟨d.a.integrable_comp hvi.1, d.a.integrable_comp hvi.2⟩
  rw [heq, intervalIntegral.integral_sub hpi hai,
    (pivotValue (triple d)).intervalIntegral_comp_comm hfi,
    d.a.intervalIntegral_comp_comm hvi] at hint
  have ha : d.a v = pivotValue (triple d)
      (primitive (𝕜 := ℝ) f t - z.curve t + u₀) := by
    simp only [map_add, map_sub]
    change d.a v = pivotValue (triple d) (∫ r in (0 : ℝ)..t.val, f r) -
      pivotValue (triple d) (z.curve t) + pivotValue (triple d) u₀
    change pivotValue (triple d) (z.curve t) - pivotValue (triple d) u₀ =
      pivotValue (triple d) (∫ r in (0 : ℝ)..t.val, f r) - d.a v at hint
    calc
      d.a v = pivotValue (triple d) (∫ r in (0 : ℝ)..t.val, f r) -
          (pivotValue (triple d) (∫ r in (0 : ℝ)..t.val, f r) - d.a v) := by abel
      _ = _ := by rw [← hint]; abel
  rw [← hv]
  apply (d.mem_graph_at v _).mpr
  intro w
  have hw := congrArg (fun ℓ : StrongDual ℝ V => ℓ w) ha
  change d.a v w = pivotInjection (triple d)
    (primitive (𝕜 := ℝ) f t - z.curve t + u₀) w at hw
  rw [pivotInjection_apply] at hw
  exact hw.trans (real_inner_comm _ _)

/-- An energy solution satisfies the common integrated generator equation. -/
theorem energy_isIntegrated (d : CoerciveForm V H) (S : C0Semigroup ℝ H)
    (hS : C0SemigroupSpec.generatorValue S = -d.operator)
    (T : ℝ≥0) (hT : 0 < (T : ℝ)) (u₀ : H) (f : ℝ → H)
    (hf : IntegrableOn f (Icc 0 (T : ℝ)))
    (z : EnergySolution d T T.coe_nonneg u₀ f) :
    IsIntegratedSolution S T u₀ f (extendCurve z.curve) := by
  refine ⟨extendCurve_continuousOn z.curve, ?_⟩
  intro t ht
  have hg := energy_primitive_graph d T hT u₀ f hf z ⟨t, ht⟩
  obtain ⟨x, hx, hBx⟩ := (LinearPMap.mem_graph_iff d.operator).mp hg
  change (x : H) = primitive (𝕜 := ℝ) (extendCurve z.curve) t at hx
  change d.operator x = primitive (𝕜 := ℝ) f t - z.curve ⟨t, ht⟩ + u₀ at hBx
  have hm : primitive (𝕜 := ℝ) (extendCurve z.curve) t ∈ (Generator S).domain := by
    rw [show Generator S = -d.operator from hS, LinearPMap.neg_domain, ← hx]
    exact x.property
  refine ⟨hm, ?_⟩
  have hgen : Generator S ⟨primitive (𝕜 := ℝ) (extendCurve z.curve) t, hm⟩ =
      -(primitive (𝕜 := ℝ) f t - z.curve ⟨t, ht⟩ + u₀) := by
    have hgneg : (primitive (𝕜 := ℝ) (extendCurve z.curve) t,
        -(primitive (𝕜 := ℝ) f t - z.curve ⟨t, ht⟩ + u₀)) ∈ (Generator S).graph := by
      rw [show Generator S = -d.operator from hS]
      apply (LinearPMap.mem_graph_iff (-d.operator)).mpr
      exact ⟨x, hx, by simpa only [LinearPMap.neg_apply] using congrArg Neg.neg hBx⟩
    exact (Generator S).mem_graph_snd_inj ((Generator S).mem_graph _) hgneg rfl
  rw [hgen, extendCurve_apply z.curve ⟨t, ht⟩]
  abel

/-- Pointwise agreement follows by the already proved integrated uniqueness
for L¹ data; no energy existence for general L¹ data is claimed. -/
theorem energy_agrees (d : CoerciveForm V H) (S : C0Semigroup ℝ H)
    (hS : C0SemigroupSpec.generatorValue S = -d.operator)
    (T : ℝ≥0) (hT : 0 < (T : ℝ)) (u₀ : H) (f : ℝ → H)
    (hf : IntegrableOn f (Icc 0 (T : ℝ)))
    (z : EnergySolution d T T.coe_nonneg u₀ f) (t : Icc 0 (T : ℝ)) :
    z.curve t = mildSolution S u₀ f t := by
  have hi := energy_isIntegrated d S hS T hT u₀ f hf z
  have hm := ((P201.Common.IntegratedMild.integrated_well_posedness S T hT u₀ f hf).2.2.2
    (extendCurve z.curve)).mp hi
  simpa only [extendCurve_apply] using hm.2 t.property

/-- All H-valued mild conclusions for any semigroup with generator -B. -/
theorem mild_conclusion (d : CoerciveForm V H) (S : C0Semigroup ℝ H)
    (hS : C0SemigroupSpec.generatorValue S = -d.operator)
    (T : ℝ≥0) (hT : 0 < (T : ℝ)) (u₀ : H) (f : ℝ → H)
    (hf : IntegrableOn f (Icc 0 (T : ℝ))) : Expected.MildConclusion d S T u₀ f := by
  obtain ⟨hconv, hzero, hint, hequiv⟩ :=
    P201.Common.IntegratedMild.integrated_well_posedness S T hT u₀ f hf
  exact ⟨hconv, hzero, (hequiv _).mp hint, hint, hequiv,
    fun z t => energy_agrees d S hS T hT u₀ f hf z t⟩

/-- The full L¹ conditional agreement proposition for the spectral heat
semigroup on every dense Hilbert injection. -/
theorem mild_energy_agreement : Expected.MildEnergyTheorem (V := V) (H := H) := by
  intro d
  obtain ⟨S, hS⟩ := P201.Heat.spectral_semigroup d
  exact ⟨S, hS, fun T hT u₀ f hf => mild_conclusion d S hS.2.2.2.1 T hT u₀ f hf⟩

omit [CompleteSpace H] in
/-- The bounded autonomous form operator in H05 is exactly the original a. -/
theorem autonomous_formOperator (d : CoerciveForm V H) (t : ℝ) :
    formOperator (fun _ => algebraicForm d) ‖d.a‖ t = d.a := by
  ext x y
  exact ParabolicGalerkin.formOperator_apply (fun _ => algebraicForm d) ‖d.a‖ t
    (fun x y => d.a.le_opNorm₂ x y) x y

/-- H05 applied to the original injection and original form. -/
theorem dual_energy_existence : Expected.DualEnergyExistence (V := V) (H := H) := by
  intro d T hT
  obtain ⟨c, hc, hcoerc⟩ := d.coercive
  obtain ⟨K, hK, hex⟩ := P201.Heat.ParabolicForms.parabolic_forms.2.1 T ‖d.a‖ c hT hc
  exact ⟨K, hK, fun f u₀ => hex (triple d) (algebraicForm d)
    (d.a.le_opNorm₂) hcoerc f u₀⟩

/-- The actual continuous pivot induces the inclusion L²(H) → L²(V'). -/
def pivotLp (d : CoerciveForm V H) (T : ℝ) :
    timeLpValue H 2 T →L[ℝ] timeLpValue (StrongDual ℝ V) 2 T :=
  (pivotValue (triple d)).compLpL 2 (timeMeasureValue T)

/-- The H05 solution for pivot-valued L² data belongs to the conditional
energy class, with the same derivative and continuous curve. -/
def energySolutionOfWeak (d : CoerciveForm V H) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : H) (f : timeLpValue H 2 T)
    (z : WeakSolution (triple d) T hT (fun _ => algebraicForm d) ‖d.a‖
      (pivotLp d T f) u₀) : EnergySolution d T hT u₀ f where
  value := z.value
  derivative := z.derivative
  curve := z.curve
  represents := z.represents
  has_derivative := z.has_derivative
  equation := by
    have hf : (pivotLp d T f : ℝ → StrongDual ℝ V) =ᵐ[timeMeasureValue T]
        fun t => pivotValue (triple d) (f t) :=
      (pivotValue (triple d)).coeFn_compLp' f
    filter_upwards [z.equation, hf] with t ht hft
    rw [hft, autonomous_formOperator] at ht
    exact ht
  initial := z.initial

/-- In particular, L²(H) forcing admits an energy solution, which is the
H-valued variation-of-constants formula at every time. -/
theorem l2_agreement : Expected.L2Agreement (V := V) (H := H) := by
  intro d S hS T hT u₀ f
  have hf : IntegrableOn (f : ℝ → H) (Icc 0 (T : ℝ)) := by
    simpa only [IntegrableOn, timeMeasureValue, restrict_Ioo_eq_restrict_Icc]
      using timeLp_integrable T f
  obtain ⟨K, _, hex⟩ := dual_energy_existence d T hT
  obtain ⟨z, _, _, _⟩ := hex (pivotLp d T f) u₀
  let w := energySolutionOfWeak d T T.coe_nonneg u₀ f z
  exact ⟨hf, w, fun t => energy_agrees d S hS.2.2.2.1 T hT u₀ f hf w t⟩

end P201.Heat.MildEnergyAgreement
