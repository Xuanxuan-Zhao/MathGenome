import MathGenome.Internal.LinearPDE.P201Specs.Heat.WeakDirichlet
import MathGenome.Internal.LinearPDE.P201.Heat.ParabolicForms
import MathGenome.Internal.LinearPDE.P201.Elliptic.WeakDirichlet

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology InnerProductSpace
namespace P201.Heat.WeakDirichlet
open ExpandedFA.Evolution HilbertTripleSpec HilbertTripleTraceSpec ParabolicGalerkinSpec
open P201Specs.Heat.WeakDirichlet

/-- Smooth compact tests occur in the actual full-H¹ closure. -/
theorem test_in_range {n : ℕ} (Ω : Domain n) (φ : Test ℝ Ω) :
    ∃ u : H10 ℝ Ω, hZeroUnderlying Ω u = P102.U4.testToDomainLp Ω 2 φ := by
  obtain ⟨w, hw⟩ := P102.U4.zeroExtension_smoothInclusion Ω 1 2 φ
  let v := (hToW ℝ Ω 1).symm w
  have hv : v ∈ P201Specs.hZeroSubmodule ℝ Ω := by
    apply Submodule.le_topologicalClosure
    change ∃ ψ, P102.U4.testToDomainLp Ω 2 ψ =
      P102.U4.sobolevUnderlying (hToW ℝ Ω 1 v)
    exact ⟨φ, by simpa [v] using hw.symm⟩
  refine ⟨⟨v, hv⟩, ?_⟩
  change P102.U4.sobolevUnderlying (hToW ℝ Ω 1 v) = _
  simpa [v] using hw

/-- Density in L² follows from orthogonality to compact smooth tests and
uniqueness of regular distributions. It requires no boundary regularity. -/
theorem zeroUnderlying_dense {n : ℕ} (Ω : Domain n) :
    DenseRange (hZeroUnderlying (𝕜 := ℝ) Ω) := by
  change Dense ((hZeroUnderlying (𝕜 := ℝ) Ω).range : Set (Lp ℝ Ω 2))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  change f = 0
  apply P102.U4.regularLp_injective Ω 2
  ext φ
  rw [P102.U4.regularLp_pairing, P102.U4.regularLp_pairing, map_zero,
    P102.U4.lpTestPairing_eq_integral]
  obtain ⟨u, hu⟩ := test_in_range Ω φ
  have hz : inner ℝ (hZeroUnderlying Ω u) f = 0 := hf _ ⟨u, rfl⟩
  rw [L2.inner_def] at hz
  convert hz using 1
  apply integral_congr_ae
  have hh : (hZeroUnderlying Ω u : Space n → ℝ) =ᵐ[domainMeasure Ω] φ := by
    rw [hu]
    exact P102.U4.testToDomainLp_ae Ω 2 φ
  filter_upwards [hh] with x hx
  simp [RCLike.inner_apply, hx]

/-- The concrete Hilbert triple uses the canonical L² inclusion. -/
def triple {n : ℕ} (Ω : Domain n) : HilbertTriple (H10 ℝ Ω) (Lp ℝ Ω 2) where
  embedding := hZeroUnderlying Ω
  injective := fun _ _ huv => Subtype.ext (hilbertUnderlyingInjective Ω 1 huv)
  denseRange := zeroUnderlying_dense Ω

/-- Its abstract Riesz/adjoint pivot is exactly the shared L² pivot. -/
theorem triple_pivot {n : ℕ} (Ω : Domain n) : pivotValue (triple Ω) = pivot Ω := by
  ext f v
  change ExpandedFA.Evolution.pivotInjection (triple Ω) f v = _
  rw [ExpandedFA.Evolution.pivotInjection_apply]
  rfl

/-- The weak gradient with values in spatial L², continuous in the full norm. -/
def gradientMap {n : ℕ} (Ω : Domain n) :
    H10 ℝ Ω →L[ℝ] MeasureTheory.Lp (Space n) 2 (domainMeasure Ω) :=
  (P201.Dirichlet.gradientCLM Ω).comp (P201Specs.hZeroSubmodule ℝ Ω).subtypeL

@[simp] theorem gradientMap_apply {n : ℕ} (Ω : Domain n) (u : H10 ℝ Ω) :
    gradientMap Ω u = hGradient u.val := P201.Dirichlet.gradientCLM_apply Ω u.val

/-- The autonomous form is the spatial dot-product integral. -/
def form {n : ℕ} (Ω : Domain n) : H10 ℝ Ω →L[ℝ] H10 ℝ Ω →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (gradientMap Ω) (gradientMap Ω)

@[simp] theorem form_apply {n : ℕ} (Ω : Domain n) (u v : H10 ℝ Ω) :
    form Ω u v = heatEnergy Ω u v := by
  simp [form, heatEnergy]

/-- In particular the diagonal is the exact squared spatial gradient norm. -/
theorem form_self {n : ℕ} (Ω : Domain n) (u : H10 ℝ Ω) :
    form Ω u u = ‖hGradient u.val‖ ^ 2 := by
  rw [form_apply, heatEnergy, real_inner_self_eq_norm_sq]


/-- Specify the canonical operator norm explicitly to avoid instance inference
through the two nested continuous-map spaces. -/
local instance formNorm {n : ℕ} (Ω : Domain n) :
    Norm (H10 ℝ Ω →L[ℝ] H10 ℝ Ω →L[ℝ] ℝ) := by
  exact ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := H10 ℝ Ω) (F := H10 ℝ Ω →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

abbrev forms {n : ℕ} (Ω : Domain n) : BilinearForms (H10 ℝ Ω) :=
  fun _ => (form Ω).toLinearMap₁₂

theorem form_bound {n : ℕ} (Ω : Domain n) (t : ℝ) :
    BoundedAt (V := H10 ℝ Ω) (forms Ω) ‖form Ω‖ t := fun u v => (form Ω).le_opNorm₂ u v

@[simp] theorem operator_apply {n : ℕ} (Ω : Domain n) (t : ℝ) (u v : H10 ℝ Ω) :
    formOperator (V := H10 ℝ Ω) (forms Ω) ‖form Ω‖ t u v = heatEnergy Ω u v := by
  rw [ParabolicGalerkin.formOperator_apply _ _ _ (form_bound Ω t)]
  exact form_apply Ω u v

/-- Poincaré supplies coercivity in the original full H¹ norm. -/
theorem form_coercivity {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (Space n))) :
    ∃ α : ℝ, 0 < α ∧ ∀ u : H10 ℝ Ω, α * ‖u‖ ^ 2 ≤ form Ω u u := by
  obtain ⟨C, hC, hbound⟩ := P201.Dirichlet.full_norm_le_gradient hn Ω hΩ
  refine ⟨1 / C ^ 2, by positivity, fun u => ?_⟩
  rw [form_self, div_mul_eq_mul_div, one_mul]
  apply (div_le_iff₀ (sq_pos_of_pos hC)).mpr
  have h := pow_le_pow_left₀ (norm_nonneg u) (hbound u) 2
  nlinarith

/-- Conversion retains both Bochner classes and the entire continuous curve. -/
def ofAbstract {n : ℕ} {Ω : Domain n} {T : ℝ} {hT : 0 ≤ T}
    {f : timeLpValue (Hminus1 ℝ Ω) 2 T} {u₀ : Lp ℝ Ω 2}
    (z : WeakSolution (triple Ω) T hT (forms Ω) ‖form Ω‖ f u₀) :
    Solution Ω T hT f u₀ where
  value := z.value
  derivative := z.derivative
  curve := z.curve
  represents := z.represents
  has_derivative := by
    have hd := z.has_derivative
    change derivativeValue T
      (fun t => pivotValue (triple Ω) (hZeroUnderlying Ω (z.value t))) z.derivative at hd
    rw [triple_pivot] at hd
    exact hd
  equation := by
    filter_upwards [z.equation] with t ht
    intro v
    have hv := congrArg (fun q : Hminus1 ℝ Ω => q v) ht
    simpa only [sub_apply, operator_apply, eq_sub_iff_add_eq] using hv
  initial := z.initial

/-- Conversely, the simultaneous spatial testing equation is an equality in
H⁻¹, not a collection of assertions with test-dependent exceptional sets. -/
def toAbstract {n : ℕ} {Ω : Domain n} {T : ℝ} {hT : 0 ≤ T}
    {f : timeLpValue (Hminus1 ℝ Ω) 2 T} {u₀ : Lp ℝ Ω 2}
    (z : Solution Ω T hT f u₀) :
    WeakSolution (triple Ω) T hT (forms Ω) ‖form Ω‖ f u₀ where
  value := z.value
  derivative := z.derivative
  curve := z.curve
  represents := z.represents
  has_derivative := by
    change derivativeValue T
      (fun t => pivotValue (triple Ω) (hZeroUnderlying Ω (z.value t))) z.derivative
    rw [triple_pivot]
    exact z.has_derivative
  equation := by
    filter_upwards [z.equation] with t ht
    ext v
    simpa only [sub_apply, operator_apply, eq_sub_iff_add_eq] using ht v
  initial := z.initial

@[simp] theorem of_toAbstract {n : ℕ} {Ω : Domain n} {T : ℝ} {hT : 0 ≤ T}
    {f : timeLpValue (Hminus1 ℝ Ω) 2 T} {u₀ : Lp ℝ Ω 2}
    (z : Solution Ω T hT f u₀) : ofAbstract (toAbstract z) = z := by
  cases z
  rfl

/-- The complete Dirichlet heat theorem, in every positive spatial dimension,
with the source's full-H¹ and continuous-dual norms. -/
theorem weak_dirichlet : TheoremStatement := by
  intro m Ω hΩ
  obtain ⟨Tr, _, hsm, _, _, hker⟩ := P201.Trace.exact_trace m Ω hΩ
  refine ⟨Tr, hsm, hker, ?_⟩
  intro T hT
  obtain ⟨α, hα, hcoerc⟩ := form_coercivity (by omega : 1 ≤ m + 1) Ω
    (P201.Dirichlet.lipschitz_isBounded Ω hΩ)
  obtain ⟨K, hK, hsolve⟩ := P201.Heat.ParabolicForms.parabolic_forms.2.1 T ‖form Ω‖ α hT hα
  obtain hsolve := hsolve (triple Ω) (form Ω).toLinearMap₁₂ (form_bound Ω 0) hcoerc
  refine ⟨K, hK, fun f u₀ => ?_⟩
  obtain ⟨z, he, hb, hu⟩ := hsolve f u₀
  refine ⟨ofAbstract z, ?_, hb, ?_, ?_⟩
  · intro t
    have h := he t
    change IntervalIntegrable (fun s => form Ω (z.value s) (z.value s)) volume 0 t.val ∧
      IntervalIntegrable (fun s => f s (z.value s)) volume 0 t.val ∧
      (1 / 2 : ℝ) * ‖z.curve t‖ ^ 2 +
        (∫ s in 0..t.val, form Ω (z.value s) (z.value s)) =
      (1 / 2 : ℝ) * ‖u₀‖ ^ 2 + (∫ s in 0..t.val, f s (z.value s)) at h
    simpa only [form_self, ofAbstract] using h
  · exact Filter.Eventually.of_forall fun t => hker.symm.le (z.value t).property
  · intro w
    have hw := congrArg ofAbstract (hu (toAbstract w))
    simpa only [of_toAbstract] using hw

end P201.Heat.WeakDirichlet
