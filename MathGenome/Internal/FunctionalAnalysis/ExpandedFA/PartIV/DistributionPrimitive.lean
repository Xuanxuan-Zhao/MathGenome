import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.DistributionPrimitive
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions ContDiff Topology

namespace ExpandedFA.PartIV.DistributionPrimitive
variable {𝕜 : Type} [RCLike 𝕜] {Ω : Opens ℝ}

/-- Integration from minus infinity; used only for smooth compactly supported
functions. Its definition imposes no endpoint values on the distribution. -/
noncomputable def lowerPrimitive (f : ℝ → 𝕜) (x : ℝ) : 𝕜 := ∫ t in Iic x, f t

theorem lowerPrimitive_hasDerivAt {f : ℝ → 𝕜} (hf : Continuous f)
    (hi : Integrable f) (x : ℝ) : HasDerivAt (lowerPrimitive f) (f x) x := by
  have heq : lowerPrimitive f = fun y => (∫ t in (0 : ℝ)..y, f t) + lowerPrimitive f 0 := by
    funext y
    have h := intervalIntegral.integral_Iic_sub_Iic
      (hi.integrableOn (s := Iic 0)) (hi.integrableOn (s := Iic y))
    dsimp [lowerPrimitive]
    exact sub_eq_iff_eq_add.mp h
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    (hf.stronglyMeasurableAtFilter volume _) hf.continuousAt).add_const _

theorem lowerPrimitive_contDiff {f : ℝ → 𝕜} (hf : ContDiff ℝ ∞ f)
    (hi : Integrable f) : ContDiff ℝ ∞ (lowerPrimitive f) := by
  have hd := lowerPrimitive_hasDerivAt hf.continuous hi
  apply contDiff_infty_iff_deriv.mpr
  exact ⟨fun x => (hd x).differentiableAt, by simpa only [funext fun x => (hd x).deriv] using hf⟩

theorem lineDeriv_apply (φ : LineTests 𝕜 Ω) (x : ℝ) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ x = deriv φ x := by
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp)]
  rfl

/-- Compact support makes the integral of a test derivative zero. -/
theorem integral_lineDeriv (φ : LineTests 𝕜 Ω) :
    (∫ x : ℝ, TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ x) = 0 := by
  simp_rw [lineDeriv_apply]
  apply integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => (φ.contDiff.differentiable (by simp) x).hasDerivAt)
  · exact (φ.contDiff.continuous_deriv (by simp)).integrable_of_hasCompactSupport
      φ.hasCompactSupport.deriv
  · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

/-- FTC on the half-line recovers a test exactly. -/
theorem lowerPrimitive_lineDeriv (φ : LineTests 𝕜 Ω) :
    lowerPrimitive (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ) = φ := by
  funext x
  simp only [lowerPrimitive, lineDeriv_apply]
  exact φ.hasCompactSupport.integral_Iic_deriv_eq (φ.contDiff.of_le (by simp)) x

/-- Integrating a zero-mean function supported in a compact interval creates
no support outside that same interval. -/
theorem lowerPrimitive_zero_off_interval {f : ℝ → 𝕜} {a b : ℝ}
    (hf : ∀ x ∉ Icc a b, f x = 0) (_hi : Integrable f) (hz : (∫ x, f x) = 0) :
    ∀ x ∉ Icc a b, lowerPrimitive f x = 0 := by
  intro x hx
  by_cases hxa : x < a
  · apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact hf y (fun h => (not_lt_of_ge (h.1.trans hy)) hxa)
  · have hbx : b < x := lt_of_not_ge ((not_and_or.mp hx).resolve_left (not_not.mpr (le_of_not_gt hxa)))
    rw [lowerPrimitive, ← hz]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    exact hf y (fun h => hy (h.2.trans hbx.le))

/-- A compact subset of an interval lies in a compact subinterval of it.
Adding a chosen point handles the empty compact without an exception. -/
theorem compact_subinterval (hΩ : OrdConnected (Ω : Set ℝ))
    (hne : (Ω : Set ℝ).Nonempty) (K : Compacts ℝ) (hK : (K : Set ℝ) ⊆ Ω) :
    ∃ a b : ℝ, a ≤ b ∧ Icc a b ⊆ Ω ∧ (K : Set ℝ) ⊆ Icc a b := by
  obtain ⟨c, hc⟩ := hne
  let S : Set ℝ := (K : Set ℝ) ∪ {c}
  have hS : IsCompact S := K.isCompact.union isCompact_singleton
  have hSc : c ∈ S := Or.inr rfl
  obtain ⟨a, ha⟩ := hS.exists_isLeast ⟨c, hSc⟩
  obtain ⟨b, hb⟩ := hS.exists_isGreatest ⟨c, hSc⟩
  have hsub : S ⊆ Ω := union_subset hK (singleton_subset_iff.mpr hc)
  exact ⟨a, b, ha.2 hb.1, hΩ.out (hsub ha.1) (hsub hb.1),
    fun x hx => ⟨ha.2 (Or.inl hx), hb.2 (Or.inl hx)⟩⟩

/-- There is a normalized test inside every nonempty open domain. -/
theorem exists_normalized_test (hne : (Ω : Set ℝ).Nonempty) :
    ∃ ρ : LineTests 𝕜 Ω, (∫ x : ℝ, ρ x) = 1 := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds hc)
  let b : ContDiffBump c := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let f : ℝ → 𝕜 := fun x => (b.normed volume x : 𝕜)
  have hsmooth : ContDiff ℝ ∞ f :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp b.contDiff_normed
  have hcompact : HasCompactSupport f := b.hasCompactSupport_normed.comp_left (by simp)
  have hs : tsupport f ⊆ Ω := by
    apply subset_trans (tsupport_comp_subset (g := fun t : ℝ => (t : 𝕜)) RCLike.ofReal_zero (b.normed volume))
    rw [b.tsupport_normed_eq]
    exact hsub
  refine ⟨⟨f, hsmooth, hcompact, hs⟩, ?_⟩
  change (∫ x : ℝ, (b.normed volume x : 𝕜)) = 1
  rw [integral_ofReal, b.integral_normed, RCLike.ofReal_one]

/-- The compactly supported integral of a zero-mean test on an interval. -/
noncomputable def zeroMeanPrimitiveTest (hΩ : OrdConnected (Ω : Set ℝ))
    (hne : (Ω : Set ℝ).Nonempty) (φ : LineTests 𝕜 Ω) (hz : (∫ x : ℝ, φ x) = 0) :
    LineTests 𝕜 Ω := by
  have hi : Integrable (φ : ℝ → 𝕜) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hs : HasCompactSupport (lowerPrimitive φ) ∧ tsupport (lowerPrimitive φ) ⊆ Ω := by
    obtain ⟨a, b, _, hI, hs⟩ := compact_subinterval hΩ hne
      ⟨tsupport φ, φ.hasCompactSupport⟩ φ.tsupport_subset
    have hzero : ∀ x ∉ Icc a b, lowerPrimitive φ x = 0 :=
      lowerPrimitive_zero_off_interval (fun x hx => image_eq_zero_of_notMem_tsupport
        (fun h => hx (hs h))) hi hz
    have hsupp : tsupport (lowerPrimitive φ) ⊆ Icc a b :=
      closure_minimal (by
        intro x hx
        by_contra h
        exact hx (hzero x h)) isClosed_Icc
    exact ⟨isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hI⟩
  exact ⟨lowerPrimitive φ, lowerPrimitive_contDiff φ.contDiff hi, hs.1, hs.2⟩

@[simp] theorem zeroMeanPrimitiveTest_apply (hΩ : OrdConnected (Ω : Set ℝ))
    (hne : (Ω : Set ℝ).Nonempty) (φ : LineTests 𝕜 Ω) (hz : (∫ x : ℝ, φ x) = 0) (x : ℝ) :
    zeroMeanPrimitiveTest hΩ hne φ hz x = lowerPrimitive φ x := rfl

/-- A zero-mean test is the derivative of another test in the same interval. -/
theorem exists_test_antiderivative (hΩ : OrdConnected (Ω : Set ℝ))
    (hne : (Ω : Set ℝ).Nonempty) (φ : LineTests 𝕜 Ω) (hz : (∫ x : ℝ, φ x) = 0) :
    ∃ ψ : LineTests 𝕜 Ω,
      TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) ψ = φ := by
  refine ⟨zeroMeanPrimitiveTest hΩ hne φ hz, ?_⟩
  ext x
  rw [lineDeriv_apply]
  exact (lowerPrimitive_hasDerivAt φ.continuous
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport) x).deriv

theorem test_integrable (φ : LineTests 𝕜 Ω) : Integrable (φ : ℝ → 𝕜) :=
  φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

/-- The kernel consists exactly of the ordinary constant distributions. -/
theorem kernel : Specs.ExpandedFA.PartIV.DistributionPrimitive.kernelType := by
  intro 𝕜 _ Ω hne hΩ u
  constructor
  · intro hu
    obtain ⟨ρ, hρ⟩ := exists_normalized_test (𝕜 := 𝕜) hne
    refine ⟨u ρ, fun φ => ?_⟩
    let η : LineTests 𝕜 Ω := φ - (∫ x : ℝ, φ x) • ρ
    have hη : (∫ x : ℝ, η x) = 0 := by
      change (∫ x : ℝ, φ x - (∫ t : ℝ, φ t) * ρ x) = 0
      rw [integral_sub (test_integrable φ) ((test_integrable ρ).const_mul (∫ t : ℝ, φ t)),
        integral_const_mul, hρ, mul_one, sub_self]
    obtain ⟨ψ, hψ⟩ := exists_test_antiderivative hΩ hne η hη
    have huψ := congrArg (fun v : LineDistribution 𝕜 Ω => v ψ) hu
    change -u (TestFunction.lineDerivCLM 𝕜 (1 : ℝ) ψ) = 0 at huψ
    rw [hψ, neg_eq_zero, show u η = u φ - (∫ t : ℝ, φ t) * u ρ by
      simp [η]] at huψ
    exact (sub_eq_zero.mp huψ).trans (mul_comm _ _)
  · rintro ⟨c, hc⟩
    ext φ
    change -u (TestFunction.lineDerivCLM 𝕜 (1 : ℝ) φ) = 0
    rw [hc, integral_lineDeriv, mul_zero, neg_zero]

theorem uniqueness : Specs.ExpandedFA.PartIV.DistributionPrimitive.uniquenessType := by
  intro 𝕜 _ Ω hne hΩ u v w hv hw
  apply (kernel 𝕜 Ω hne hΩ (v - w)).mp
  ext φ
  have hv' := congrArg (fun z : LineDistribution 𝕜 Ω => z φ) hv
  have hw' := congrArg (fun z : LineDistribution 𝕜 Ω => z φ) hw
  change -v (TestFunction.lineDerivCLM 𝕜 (1 : ℝ) φ) = u φ at hv'
  change -w (TestFunction.lineDerivCLM 𝕜 (1 : ℝ) φ) = u φ at hw'
  change -((v - w) (TestFunction.lineDerivCLM 𝕜 (1 : ℝ) φ)) = 0
  simp only [sub_apply]
  linear_combination hv' - hw'

/-- Compact intervals regarded as compact subsets of the line. -/
def intervalCompact (a b : ℝ) : Compacts ℝ := ⟨Icc a b, isCompact_Icc⟩

local instance compact_restrict_finite (K : Compacts ℝ) :
    IsFiniteMeasure (volume.restrict (K : Set ℝ)) :=
  ⟨by simpa using K.isCompact.measure_lt_top (μ := volume)⟩

/-- The integral on a compact test step is a continuous scalar-linear map. -/
noncomputable def compactIntegralCLM (K : Compacts ℝ) :
    ContDiffMapSupportedIn ℝ 𝕜 ⊤ K →L[𝕜] 𝕜 :=
  ContDiffMapSupportedIn.integralAgainstBilinCLM (ContinuousLinearMap.mul 𝕜 𝕜)
    volume (fun _ => (1 : 𝕜))

@[simp] theorem compactIntegralCLM_apply (K : Compacts ℝ)
    (φ : ContDiffMapSupportedIn ℝ 𝕜 ⊤ K) : compactIntegralCLM K φ = ∫ x : ℝ, φ x := by
  rw [compactIntegralCLM, ContDiffMapSupportedIn.integralAgainstBilinCLM_eq_integral
    (integrableOn_const (C := (1 : 𝕜)) K.isCompact.measure_lt_top.ne)]
  simp

/-- Subtracting a fixed normalized test times the integral is continuous. -/
noncomputable def meanZeroCLM {K : Compacts ℝ} (ρ : ContDiffMapSupportedIn ℝ 𝕜 ⊤ K) :
    ContDiffMapSupportedIn ℝ 𝕜 ⊤ K →L[𝕜] ContDiffMapSupportedIn ℝ 𝕜 ⊤ K :=
  ContinuousLinearMap.id 𝕜 _ - (compactIntegralCLM K).smulRight ρ

@[simp] theorem meanZeroCLM_apply {K : Compacts ℝ} (ρ φ : ContDiffMapSupportedIn ℝ 𝕜 ⊤ K) :
    meanZeroCLM ρ φ = φ - (∫ t : ℝ, φ t) • ρ := by
  simp [meanZeroCLM]

theorem integral_meanZero {K : Compacts ℝ} (ρ φ : ContDiffMapSupportedIn ℝ 𝕜 ⊤ K)
    (hρ : (∫ x : ℝ, ρ x) = 1) : (∫ x : ℝ, meanZeroCLM ρ φ x) = 0 := by
  simp only [meanZeroCLM_apply, sub_apply, smul_apply, smul_eq_mul]
  rw [integral_sub φ.integrable (ρ.integrable.const_mul _), integral_const_mul, hρ,
    mul_one, sub_self]

/-- A bound for integration from minus infinity, valid uniformly in the upper endpoint. -/
theorem lowerPrimitive_step_bound {K : Compacts ℝ}
    (φ : ContDiffMapSupportedIn ℝ 𝕜 ⊤ K) (x : ℝ) :
    ‖lowerPrimitive φ x‖ ≤ volume.real (K : Set ℝ) *
      ContDiffMapSupportedIn.seminorm 𝕜 ℝ 𝕜 ⊤ K 0 φ := by
  let p := ContDiffMapSupportedIn.seminorm 𝕜 ℝ 𝕜 ⊤ K 0
  calc
    ‖lowerPrimitive φ x‖ ≤ ∫ t in Iic x, ‖φ t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖φ t‖ := setIntegral_le_integral φ.integrable.norm
      (Eventually.of_forall fun _ => norm_nonneg _)
    _ = ∫ t in (K : Set ℝ), ‖φ t‖ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht => by rw [φ.zero_on_compl ht, Pi.zero_apply, norm_zero])).symm
    _ ≤ p φ * volume.real (K : Set ℝ) := by
      calc
        _ ≤ ‖∫ t in (K : Set ℝ), ‖φ t‖‖ := le_abs_self _
        _ ≤ p φ * volume.real (K : Set ℝ) :=
          norm_setIntegral_le_of_norm_le_const_ae K.isCompact.measure_lt_top
            (Eventually.of_forall fun t => by simpa using
              (ContDiffMapSupportedIn.norm_apply_le_seminorm 𝕜 (f := φ) (x := t)))
    _ = _ := mul_comm _ _

/-- Positive-order derivative bounds reduce to derivatives of the integrand. -/
theorem lowerPrimitive_derivative_bound {K : Compacts ℝ}
    (φ : ContDiffMapSupportedIn ℝ 𝕜 ⊤ K) (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ (n + 1) (lowerPrimitive φ) x‖ ≤
      ContDiffMapSupportedIn.seminorm 𝕜 ℝ 𝕜 ⊤ K n φ := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ']
  have hd : deriv (lowerPrimitive φ) = φ :=
    funext fun t => (lowerPrimitive_hasDerivAt φ.continuous φ.integrable t).deriv
  rw [hd, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜

/-- The corrected antiderivative is continuous between fixed compact steps.
The finite bounds used below follow from the genuine continuous projection onto
zero-mean tests; continuity of the antiderivative itself is proved here. -/
noncomputable def intervalPrimitiveCLM (a b : ℝ)
    (ρ : ContDiffMapSupportedIn ℝ 𝕜 ⊤ (intervalCompact a b))
    (hρ : (∫ x : ℝ, ρ x) = 1) :
    ContDiffMapSupportedIn ℝ 𝕜 ⊤ (intervalCompact a b) →L[𝕜]
      ContDiffMapSupportedIn ℝ 𝕜 ⊤ (intervalCompact a b) := by
  classical
  let K := intervalCompact a b
  let Q := meanZeroCLM ρ
  let p := ContDiffMapSupportedIn.seminorm 𝕜 ℝ 𝕜 ⊤ K
  have hp := ContDiffMapSupportedIn.withSeminorms 𝕜 ℝ 𝕜 ⊤ K
  refine ContDiffMapSupportedIn.mkCLM 𝕜 (fun φ => lowerPrimitive (Q φ))
    (fun φ ψ x => ?_) (fun c φ x => ?_)
    (fun φ => lowerPrimitive_contDiff (Q φ).contDiff (Q φ).integrable)
    (fun φ x hx => ?_) (fun i _ => ?_)
  · rw [map_add]
    exact integral_add (Q φ).integrable.integrableOn (Q ψ).integrable.integrableOn
  · change lowerPrimitive (Q (c • φ)) x = _
    rw [map_smul]
    exact integral_smul c _
  · exact lowerPrimitive_zero_off_interval (Q φ).zero_on_compl (Q φ).integrable
      (integral_meanZero ρ φ hρ) x hx
  · cases i with
    | zero =>
      let q := (p 0).comp Q.toLinearMap
      have hq : Continuous q := (hp.continuous_seminorm 0).comp Q.continuous
      obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous hp q hq
      refine ⟨s, volume.real (K : Set ℝ) * C,
        mul_nonneg ENNReal.toReal_nonneg C.coe_nonneg, fun φ x _ => ?_⟩
      rw [norm_iteratedFDeriv_zero]
      exact (lowerPrimitive_step_bound (Q φ) x).trans
        ((mul_le_mul_of_nonneg_left (hC φ) ENNReal.toReal_nonneg).trans_eq (mul_assoc _ _ _).symm)
    | succ n =>
      let q := (p n).comp Q.toLinearMap
      have hq : Continuous q := (hp.continuous_seminorm n).comp Q.continuous
      obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous hp q hq
      exact ⟨s, C, C.coe_nonneg, fun φ x _ =>
        (lowerPrimitive_derivative_bound (Q φ) n x).trans (hC φ)⟩

@[simp] theorem intervalPrimitiveCLM_apply (a b : ℝ)
    (ρ φ : ContDiffMapSupportedIn ℝ 𝕜 ⊤ (intervalCompact a b))
    (hρ : (∫ x : ℝ, ρ x) = 1) (x : ℝ) :
    intervalPrimitiveCLM a b ρ hρ φ x = lowerPrimitive (meanZeroCLM ρ φ) x := rfl

/-- Integration of tests on the whole open domain. -/
noncomputable def lineIntegralCLM : LineTests 𝕜 Ω →L[𝕜] 𝕜 :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul 𝕜 𝕜) volume
    (fun _ => (1 : 𝕜))

@[simp] theorem lineIntegralCLM_apply (φ : LineTests 𝕜 Ω) :
    lineIntegralCLM φ = ∫ x : ℝ, φ x := by
  rw [lineIntegralCLM, TestFunction.integralAgainstBilinCLM_eq_integral
    (locallyIntegrableOn_const (1 : 𝕜))]
  simp

/-- Scalar multiples of a fixed test depend continuously on the scalar.
Factoring through its compact step avoids imposing a scalar topology by fiat. -/
noncomputable def testScalarCLM (ρ : LineTests 𝕜 Ω) : 𝕜 →L[𝕜] LineTests 𝕜 Ω :=
  let K : Compacts ℝ := ⟨tsupport ρ, ρ.hasCompactSupport⟩
  let ρK : ContDiffMapSupportedIn ℝ 𝕜 ⊤ K :=
    .of_support_subset ρ.contDiff subset_closure
  (TestFunction.ofSupportedInCLM 𝕜 ρ.tsupport_subset).comp
    (ContinuousLinearMap.toSpanSingleton 𝕜 ρK)

@[simp] theorem testScalarCLM_apply (ρ : LineTests 𝕜 Ω) (c : 𝕜) :
    testScalarCLM ρ c = c • ρ := by ext x; rfl

/-- The continuous zero-mean correction on the LF space. -/
noncomputable def testMeanZeroCLM (ρ : LineTests 𝕜 Ω) : LineTests 𝕜 Ω →L[𝕜] LineTests 𝕜 Ω :=
  ContinuousLinearMap.id 𝕜 _ - (testScalarCLM ρ).comp lineIntegralCLM

@[simp] theorem testMeanZeroCLM_apply (ρ φ : LineTests 𝕜 Ω) :
    testMeanZeroCLM ρ φ = φ - (∫ t : ℝ, φ t) • ρ := by
  simp [testMeanZeroCLM]

theorem integral_testMeanZero (ρ φ : LineTests 𝕜 Ω) (hρ : (∫ x : ℝ, ρ x) = 1) :
    (∫ x : ℝ, testMeanZeroCLM ρ φ x) = 0 := by
  simp only [testMeanZeroCLM_apply, sub_apply, smul_apply, smul_eq_mul]
  rw [integral_sub (test_integrable φ) ((test_integrable ρ).const_mul _),
    integral_const_mul, hρ, mul_one, sub_self]

noncomputable def correctedTest (hΩ : OrdConnected (Ω : Set ℝ))
    (hne : (Ω : Set ℝ).Nonempty) (ρ : LineTests 𝕜 Ω) (hρ : (∫ x : ℝ, ρ x) = 1)
    (φ : LineTests 𝕜 Ω) : LineTests 𝕜 Ω :=
  zeroMeanPrimitiveTest hΩ hne (testMeanZeroCLM ρ φ) (integral_testMeanZero ρ φ hρ)

@[simp] theorem correctedTest_apply (hΩ : OrdConnected (Ω : Set ℝ))
    (hne : (Ω : Set ℝ).Nonempty) (ρ : LineTests 𝕜 Ω) (hρ : (∫ x : ℝ, ρ x) = 1)
    (φ : LineTests 𝕜 Ω) (x : ℝ) :
    correctedTest hΩ hne ρ hρ φ x = lowerPrimitive (testMeanZeroCLM ρ φ) x := rfl

/-- The compact-step operators agree with the global integral formula.
This proves LF continuity, without an assumed continuity certificate. -/
noncomputable def correctedTestCLM (hΩ : OrdConnected (Ω : Set ℝ))
    (hne : (Ω : Set ℝ).Nonempty) (ρ : LineTests 𝕜 Ω) (hρ : (∫ x : ℝ, ρ x) = 1) :
    LineTests 𝕜 Ω →L[𝕜] LineTests 𝕜 Ω := by
  refine TestFunction.mkCLM 𝕜 (correctedTest hΩ hne ρ hρ) ?_ ?_ ?_
  · intro φ ψ
    ext x
    simp only [correctedTest_apply, add_apply]
    rw [map_add]
    exact integral_add (test_integrable (testMeanZeroCLM ρ φ)).integrableOn
      (test_integrable (testMeanZeroCLM ρ ψ)).integrableOn
  · intro c φ
    ext x
    simp only [correctedTest_apply, smul_apply]
    rw [map_smul]
    exact integral_smul c _
  · intro K hK
    let S : Compacts ℝ := ⟨(K : Set ℝ) ∪ tsupport ρ, K.isCompact.union ρ.hasCompactSupport⟩
    obtain ⟨a, b, _, hL, hS⟩ := compact_subinterval hΩ hne S (union_subset hK ρ.tsupport_subset)
    let L := intervalCompact a b
    have hKL : K ≤ L := fun x hx => hS (Or.inl hx)
    have hρL : tsupport ρ ⊆ L := fun x hx => hS (Or.inr hx)
    let ρL : ContDiffMapSupportedIn ℝ 𝕜 ⊤ L :=
      .of_support_subset ρ.contDiff (subset_closure.trans hρL)
    have hρLnorm : (∫ x : ℝ, ρL x) = 1 := hρ
    let J : ContDiffMapSupportedIn ℝ 𝕜 ⊤ K →L[𝕜]
        ContDiffMapSupportedIn ℝ 𝕜 ⊤ L := ContDiffMapSupportedIn.monoCLM 𝕜
    have hJ (φ : ContDiffMapSupportedIn ℝ 𝕜 ⊤ K) : (J φ : ℝ → 𝕜) = φ := by
      change (ContDiffMapSupportedIn.monoLM 𝕜 φ : ℝ → 𝕜) = φ
      rw [ContDiffMapSupportedIn.monoLM_apply]
      simp [hKL]
    let T := (TestFunction.ofSupportedInCLM 𝕜 hL).comp
      ((intervalPrimitiveCLM a b ρL hρLnorm).comp J)
    apply T.continuous.congr
    intro φ
    ext x
    change intervalPrimitiveCLM a b ρL hρLnorm (J φ) x =
      correctedTest hΩ hne ρ hρ (TestFunction.ofSupportedIn hK φ) x
    rw [intervalPrimitiveCLM_apply, correctedTest_apply]
    congr 1
    funext y
    simp only [meanZeroCLM_apply, testMeanZeroCLM_apply, sub_apply, smul_apply]
    change J φ y - (∫ t : ℝ, J φ t) • ρ y = φ y - (∫ t : ℝ, φ t) • ρ y
    rw [hJ]

@[simp] theorem correctedTestCLM_apply (hΩ : OrdConnected (Ω : Set ℝ))
    (hne : (Ω : Set ℝ).Nonempty) (ρ : LineTests 𝕜 Ω) (hρ : (∫ x : ℝ, ρ x) = 1)
    (φ : LineTests 𝕜 Ω) (x : ℝ) :
    correctedTestCLM hΩ hne ρ hρ φ x = lowerPrimitive (testMeanZeroCLM ρ φ) x := rfl

/-- The correction vanishes on test derivatives, so integration is a left inverse. -/
theorem correctedTestCLM_lineDeriv (hΩ : OrdConnected (Ω : Set ℝ))
    (hne : (Ω : Set ℝ).Nonempty) (ρ : LineTests 𝕜 Ω) (hρ : (∫ x : ℝ, ρ x) = 1)
    (φ : LineTests 𝕜 Ω) :
    correctedTestCLM hΩ hne ρ hρ
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ) = φ := by
  ext x
  rw [correctedTestCLM_apply, testMeanZeroCLM_apply, integral_lineDeriv,
    zero_smul, sub_zero, lowerPrimitive_lineDeriv]

/-- Every scalar-linear distribution on an arbitrary nonempty open interval
has a primitive, without any endpoint prescription. -/
theorem interval_existence : Specs.ExpandedFA.PartIV.DistributionPrimitive.intervalExistenceType := by
  intro 𝕜 _ Ω hne hΩ u
  obtain ⟨ρ, hρ⟩ := exists_normalized_test (𝕜 := 𝕜) hne
  let A := correctedTestCLM hΩ hne ρ hρ
  refine ⟨-u.comp A, ?_⟩
  ext φ
  change -(-u (A (TestFunction.lineDerivCLM 𝕜 (1 : ℝ) φ))) = u φ
  rw [neg_neg, correctedTestCLM_lineDeriv]

/-- The real-line assertion is the full-domain specialization of the interval theorem. -/
theorem line_existence : Specs.ExpandedFA.PartIV.DistributionPrimitive.lineExistenceType := by
  intro 𝕜 _ u
  exact interval_existence 𝕜 ⊤ (by exact Set.univ_nonempty) (by exact Set.ordConnected_univ) u

end ExpandedFA.PartIV.DistributionPrimitive
