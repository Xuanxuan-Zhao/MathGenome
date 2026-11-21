import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.TemperedExamples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.PointSupportedDistributions
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory Set TopologicalSpace Function
open scoped SchwartzMap FourierTransform ContDiff Topology

set_option maxHeartbeats 1200000

noncomputable section
namespace ExpandedFA.SingularIntegrals
open ExpandedFA.Distributions ExpandedFA.Fourier ExpandedFA.Fourier.Examples

@[simp] theorem dilateTest_apply {d : ℕ} (r : ℝ) (hr : r ≠ 0)
    (φ : Tests ℂ (⊤ : Opens (Domain d))) (x : Domain d) :
    dilateTest r hr φ x = φ (r⁻¹ • x) := rfl

@[simp] theorem testSchwartz_apply {d : ℕ}
    (φ : Tests ℂ (⊤ : Opens (Domain d))) (x : Euclidean d) :
    testSchwartz ℂ φ x = φ ((EuclideanSpace.equiv (Fin d) ℝ) x) := rfl

/-- Scalar-linear transposition and inversion give the exact inverse-transform
pairing. In particular no conjugation enters the multiplier identity. -/
theorem represented_pairing {d : ℕ} (U : Tempered ℂ d) (m : Euclidean d → ℂ)
    (hm : FourierRepresentedBy U m) (φ : Schwartz ℂ d) :
    U φ = ∫ x, m x * (𝓕⁻ φ : Schwartz ℂ d) x := by
  have h := (hm (𝓕⁻ φ)).2
  simpa [temperedFourier, schwartzFourier] using h

theorem bounded_fourier_pairing :
    Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence.boundedFourierPairingType := by
  intro d U m M hM hm hrep φ
  rw [represented_pairing U m hrep φ]
  calc
    ‖∫ x, m x * (𝓕⁻ φ : Schwartz ℂ d) x‖ ≤
        ∫ x, ‖m x * (𝓕⁻ φ : Schwartz ℂ d) x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, M * ‖(𝓕⁻ φ : Schwartz ℂ d) x‖ := by
      apply integral_mono (hrep (𝓕⁻ φ)).1.norm ((𝓕⁻ φ : Schwartz ℂ d).integrable.norm.const_mul M)
      intro x
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hm x) (norm_nonneg _)
    _ = M * ∫ x, ‖(𝓕⁻ φ : Schwartz ℂ d) x‖ := integral_const_mul _ _
    _ = M * ∫ x, ‖schwartzFourier φ x‖ := by
      congr 1
      have heq (x : Euclidean d) :
          (𝓕⁻ φ : Schwartz ℂ d) x = schwartzFourier φ (-x) := by
        rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
        rfl
      simp_rw [heq]
      exact integral_neg_eq_self (fun x => ‖schwartzFourier φ x‖) volume

/-- Outside the unit ball all derivatives vanish; inside it every polynomial
weight has modulus at most one. -/
theorem bump_seminorm :
    Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence.bumpSeminormType := by
  intro d N k n φ hφ hn
  apply SchwartzMap.seminorm_le_bound ℂ k n _ zero_le_one
  intro x
  by_cases hx : x ∈ tsupport (testSchwartz ℂ φ)
  · have hnorm : ‖x‖ ≤ 1 := by simpa using hφ.1 hx
    exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) hnorm) (hφ.2 n hn x)
      (norm_nonneg _) zero_le_one).trans (by simp)
  · have hd : iteratedFDeriv ℝ n (testSchwartz ℂ φ) x = 0 := by
      apply Function.notMem_support.mp
      exact fun h => hx (support_iteratedFDeriv_subset n h)
    simp [hd]

/-- The continuous map S → S → L¹ controls the Fourier L¹ norm by finitely
many input seminorms. On unit-ball bumps these are Cᴺ bounds. -/
theorem bump_fourier_l1 :
    Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence.bumpFourierL1Type := by
  intro d
  let T : Schwartz ℂ d →L[ℂ] Lp ℂ 1 (volume : Measure (Euclidean d)) :=
    (SchwartzMap.toLpCLM ℂ ℂ 1 volume).comp schwartzFourier
  let q : Seminorm ℂ (Schwartz ℂ d) := (normSeminorm ℂ _).comp T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ (Euclidean d) ℂ) q hq
  let N := max (d + 1) (s.sup Prod.snd)
  refine ⟨N, lt_of_lt_of_le (Nat.lt_succ_self d) (le_max_left _ _), C, C.coe_nonneg, ?_⟩
  intro φ hφ
  have hs : (s.sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ)) (testSchwartz ℂ φ) ≤ 1 := by
    apply Seminorm.finset_sup_apply_le zero_le_one
    intro i hi
    exact bump_seminorm d N i.1 i.2 φ hφ
      ((Finset.le_sup (f := Prod.snd) hi).trans (le_max_right _ _))
  calc
    ∫ x, ‖schwartzFourier (testSchwartz ℂ φ) x‖ = q (testSchwartz ℂ φ) := by
      exact SchwartzMap.norm_toLp_one.symm
    _ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ))
        (testSchwartz ℂ φ) := hC _
    _ ≤ C := by simpa using mul_le_mul_of_nonneg_left hs C.coe_nonneg

/-- The amplitude-one dilation formula, with the manuscript's Fourier sign. -/
theorem fourier_dilate {d : ℕ} (f : Euclidean d → ℂ) (r : ℝ) (hr : 0 < r)
    (ξ : Euclidean d) :
    𝓕 (fun x => f (r⁻¹ • x)) ξ = (r ^ d : ℝ) • 𝓕 f (r • ξ) := by
  have he (x : Euclidean d) :
      inner ℝ (r⁻¹ • x) (r • ξ) = inner ℝ x ξ := by
    simp only [real_inner_smul_left, real_inner_smul_right]
    field_simp
  have h := Measure.integral_comp_inv_smul_of_nonneg volume
    (f := fun x : Euclidean d => Real.fourierChar (-inner ℝ x (r • ξ)) • f x) hr.le
  simpa only [Real.fourier_eq, he, finrank_euclideanSpace_fin] using h

/-- The Fourier L¹ norm is unchanged by amplitude-one dilation. -/
theorem fourier_l1_dilate {d : ℕ} (φ : Tests ℂ (⊤ : Opens (Domain d)))
    (r : ℝ) (hr : 0 < r) :
    (∫ x, ‖schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' φ)) x‖) =
      ∫ x, ‖schwartzFourier (testSchwartz ℂ φ) x‖ := by
  have hd (ξ : Euclidean d) :
      schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' φ)) ξ =
        (r ^ d : ℝ) • schwartzFourier (testSchwartz ℂ φ) (r • ξ) := by
    change (𝓕 (testSchwartz ℂ (dilateTest r hr.ne' φ)) : Schwartz ℂ d) ξ = _
    rw [SchwartzMap.fourier_coe]
    have hfun : (⇑(testSchwartz ℂ (dilateTest r hr.ne' φ))) =
        fun x : Euclidean d => testSchwartz ℂ φ (r⁻¹ • x) := by
      funext x
      simp only [testSchwartz_apply, dilateTest_apply, map_smul]
    rw [hfun, fourier_dilate _ r hr]
    rfl
  simp_rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr d)]
  rw [integral_const_mul]
  have h := Measure.integral_comp_smul_of_nonneg volume
    (fun x : Euclidean d => ‖schwartzFourier (testSchwartz ℂ φ) x‖) r (hR := hr.le)
  rw [finrank_euclideanSpace_fin] at h
  rw [h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hr.ne'), one_mul]

/-- A bounded Fourier transform supplies the uniform bump estimate at all
positive scales. Physical kernel estimates are unnecessary for this direction. -/
theorem bounded_to_bumps :
    Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence.boundedToBumpsType := by
  intro d K hK
  obtain ⟨U, m, hU, hm, hrep⟩ := hK
  obtain ⟨M, hM, hbound⟩ := hm.2
  obtain ⟨N, hN, C, hC, hCbump⟩ := bump_fourier_l1 d
  refine ⟨N, hN, M * C, mul_nonneg hM hC, ?_⟩
  intro φ hφ r hr
  rw [← hU]
  calc
    ‖U (testSchwartz ℂ (dilateTest r hr.ne' φ))‖ ≤ M *
        ∫ x, ‖schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' φ)) x‖ :=
      bounded_fourier_pairing d U m M hM hbound hrep _
    _ = M * ∫ x, ‖schwartzFourier (testSchwartz ℂ φ) x‖ := by
      rw [fourier_l1_dilate φ r hr]
    _ ≤ M * C := mul_le_mul_of_nonneg_left (hCbump φ hφ) hM

/-- Bounded measurable functions define regular tempered distributions. -/
theorem bounded_regular_tempered {d : ℕ} (f : Euclidean d → ℂ)
    (hf : AEStronglyMeasurable f volume) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, ‖f x‖ ≤ M) :
    ∃ U : Tempered ℂ d, ∀ φ : Schwartz ℂ d,
      Integrable (fun x => f x * φ x) ∧ U φ = ∫ x, f x * φ x := by
  have hi (φ : Schwartz ℂ d) : Integrable (fun x => f x * φ x) := by
    apply (φ.integrable.norm.const_mul M).mono (hf.mul φ.continuous.aestronglyMeasurable)
    filter_upwards [] with x
    change ‖f x * φ x‖ ≤ ‖M * ‖φ x‖‖
    rw [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg (φ x))).trans (le_abs_self _)
  obtain ⟨k, C, hC, hCbound⟩ := SchwartzMap.norm_toLp_le_seminorm ℂ ℂ 1
    (volume : Measure (Euclidean d))
  let U : Tempered ℂ d := SchwartzMap.mkCLMtoNormedSpace
    (fun φ : Schwartz ℂ d => ∫ x, f x * φ x)
    (fun φ ψ => by
      simp only [add_apply, mul_add]
      exact integral_add (hi φ) (hi ψ))
    (fun c φ => by
      simp only [smul_apply, smul_eq_mul]
      simp_rw [show ∀ x, f x * (c * φ x) = c * (f x * φ x) by intro x; ring]
      exact integral_const_mul c _)
    (by
      refine ⟨Finset.Iic (k, 0), M * C, mul_nonneg hM hC, ?_⟩
      intro φ
      calc
        ‖∫ x, f x * φ x‖ ≤ ∫ x, ‖f x * φ x‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ x, M * ‖φ x‖ := by
          apply integral_mono (hi φ).norm (φ.integrable.norm.const_mul M)
          intro x
          dsimp only
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
        _ = M * ‖φ.toLp 1 volume‖ := by rw [integral_const_mul, SchwartzMap.norm_toLp_one]
        _ ≤ (M * C) * _ := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hCbound φ) hM)
  exact ⟨U, fun φ => ⟨hi φ, rfl⟩⟩

/-- Multiplication by a compactly supported smooth function has compact
support on the actual LF distribution, even if the original support is unbounded. -/
theorem compact_support_multiply {d : ℕ} (K : KernelDistribution d)
    (a : Domain d → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a) :
    IsCompact (distributionSupport (K.comp (multiplyTest a ha))) := by
  let u := K.comp (multiplyTest a ha)
  have hs : distributionSupport u ⊆ tsupport a := by
    intro x hx
    by_contra hxa
    apply hx.2
    apply Set.mem_sUnion.mpr
    refine ⟨(tsupport a)ᶜ, ⟨(isClosed_tsupport a).isOpen_compl, subset_univ _, ?_⟩, hxa⟩
    intro φ hφ
    have hzero : multiplyTest a ha φ = 0 := by
      apply DFunLike.ext
      intro y
      change φ y * a y = 0
      by_cases hy : y ∈ tsupport φ
      · rw [image_eq_zero_of_notMem_tsupport (hφ hy), mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    change K (multiplyTest a ha φ) = 0
    rw [hzero, map_zero]
  have hclosed : IsClosed (distributionSupport u) := by
    change IsClosed (Set.univ \ vanishingRegion u)
    rw [← Set.compl_eq_univ_sdiff]
    exact (ExpandedFA.Distributions.support_vanishing ℂ d ⊤ u).1.isClosed_compl
  exact hc.of_isClosed_subset hclosed hs

/-- The source's cutoff argument for unconditional temperedness. Only the
order-zero size estimate is needed in this step. -/
theorem kernel_temperedness :
    Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence.temperednessType := by
  intro d K k hk
  let b : ContDiffBump (0 : Euclidean d) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let e := EuclideanSpace.equiv (Fin d) ℝ
  let a : Domain d → ℂ := fun x => (b (e.symm x) : ℂ)
  have ha : ContDiff ℝ (⊤ : ℕ∞) a :=
    Complex.ofRealCLM.contDiff.comp (b.contDiff.comp e.symm.contDiff)
  have hac : HasCompactSupport a :=
    (b.hasCompactSupport.comp_homeomorph e.symm.toHomeomorph).comp_left (g := Complex.ofReal) (by simp)
  obtain ⟨A, hA⟩ := compact_support_tempered ℂ d (K.comp (multiplyTest a ha))
    (compact_support_multiply K a ha hac)
  let f : Euclidean d → ℂ := fun x => (1 - (b x : ℂ)) * k x
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      apply (continuousAt_const : ContinuousAt (fun _ : Euclidean d => (0 : ℂ)) 0).congr
      filter_upwards [b.eventuallyEq_one] with y hy
      simp [f, hy]
    · exact (continuous_const.sub (Complex.continuous_ofReal.comp b.continuous)).continuousAt.mul
        (hk.2.1.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hx))
  obtain ⟨C, hC, hsize⟩ := hk.2.2 0 (fun i => Fin.elim0 i)
  have hbound : ∀ x, ‖f x‖ ≤ C := by
    intro x
    by_cases hx : ‖x‖ ≤ 1
    · have hb : b x = 1 := b.one_of_mem_closedBall (by simpa [b] using hx)
      simpa [f, hb] using hC
    · have hxn : x ≠ 0 := by intro h; simp [h] at hx
      have hkp : ‖k x‖ ≤ C := by
        have hpow : 1 ≤ ‖x‖ ^ d := one_le_pow₀ (le_of_not_ge hx)
        have hi : (‖x‖ ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpow
        have h := hsize x hxn
        simp only [iteratedFDeriv_zero_apply, Nat.add_zero] at h
        exact h.trans ((mul_le_mul_of_nonneg_left hi hC).trans_eq (mul_one C))
      have hb : ‖1 - (b x : ℂ)‖ ≤ 1 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr b.le_one)]
        linarith [b.nonneg (x := x)]
      calc
        ‖f x‖ = ‖1 - (b x : ℂ)‖ * ‖k x‖ := norm_mul _ _
        _ ≤ 1 * C := mul_le_mul hb hkp (norm_nonneg _) zero_le_one
        _ = C := one_mul C
  obtain ⟨F, hF⟩ := bounded_regular_tempered f hf.aestronglyMeasurable C hC hbound
  refine ⟨A + F, ?_⟩
  intro φ
  let ψ := multiplyTest (fun x => 1 - a x) (contDiff_const.sub ha) φ
  have hψ : 0 ∉ tsupport (testSchwartz ℂ ψ) := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [b.eventuallyEq_one] with x hx
    change φ (e x) * (1 - (b (e.symm (e x)) : ℂ)) = 0
    simp [hx]
  have heq : multiplyTest a ha φ + ψ = φ := by
    apply DFunLike.ext
    intro x
    change φ x * a x + φ x * (1 - a x) = φ x
    ring
  calc
    (A + F) (testSchwartz ℂ φ) =
        K (multiplyTest a ha φ) + ∫ x, f x * testSchwartz ℂ φ x := by
      rw [add_apply, hA, (hF _).2]
      rfl
    _ = K (multiplyTest a ha φ) + K ψ := by
      rw [(hk.1 ψ hψ).2]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      change (1 - (b x : ℂ)) * k x * φ (e x) =
        k x * (φ (e x) * (1 - (b (e.symm (e x)) : ℂ)))
      rw [e.symm_apply_apply]
      ring
    _ = K φ := by rw [← map_add, heq]

/-- In dimension zero every test is a scalar multiple of the constant one
and every distribution is a scalar multiple of evaluation at the singleton. -/
theorem zero_dimension_multiplier :
    Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence.zeroDimensionType := by
  intro K
  let e : Tests ℂ (⊤ : Opens (Domain 0)) :=
    ⟨fun _ => 1, contDiff_const, HasCompactSupport.of_compactSpace _, subset_univ _⟩
  let c : ℂ := K e
  let U : Tempered ℂ 0 := c • delta ℂ 0
  refine ⟨U, fun _ => c, ?_, ?_, ?_, ?_⟩
  · intro φ
    have hφ : φ = φ 0 • e := by
      apply DFunLike.ext
      intro x
      change φ x = φ 0 * 1
      rw [Subsingleton.elim x 0, mul_one]
    change c * φ ((EuclideanSpace.equiv (Fin 0) ℝ) 0) = K φ
    simp only [map_zero]
    rw [hφ, map_smul]
    change c * (φ 0 * 1) = φ 0 * c
    ring
  · exact ⟨aestronglyMeasurable_const, ‖c‖, norm_nonneg c, fun _ => le_rfl⟩
  · intro φ
    refine ⟨φ.integrable.const_mul c, ?_⟩
    change temperedFourier (c • delta ℂ 0) φ = _
    rw [temperedFourier_smul, (basic_fourier 0).2]
    change c * (∫ x, φ x) = ∫ x, c * φ x
    exact (integral_const_mul _ _).symm
  · refine ⟨contDiff_const.contDiffOn, ?_⟩
    intro n w
    exact ⟨0, le_rfl, fun x hx => (hx (Subsingleton.elim x 0)).elim⟩

@[simp] theorem testSchwartz_smul {d : ℕ} (c : ℂ)
    (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    testSchwartz ℂ (c • φ) = c • testSchwartz ℂ φ := by
  ext x
  rfl

@[simp] theorem dilateTest_smul {d : ℕ} (r : ℝ) (hr : r ≠ 0) (c : ℂ)
    (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    dilateTest r hr (c • φ) = c • dilateTest r hr φ := by
  apply DFunLike.ext
  intro x
  rfl

/-- Amplitude normalization of a test makes the uniform bump hypothesis a
quantitative Cᴺ estimate with the same constant at every positive scale. -/
theorem bump_pairing_bound :
    Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence.bumpPairingBoundType := by
  intro d N K hK
  obtain ⟨C, hC, hbound⟩ := hK
  refine ⟨C, hC, ?_⟩
  intro φ B hB hs hder r hr
  let ψ := (B⁻¹ : ℂ) • φ
  have hψ : NormalizedBump N ψ := by
    constructor
    · rw [show testSchwartz ℂ ψ = (B⁻¹ : ℂ) • testSchwartz ℂ φ by simp [ψ]]
      exact (tsupport_smul_subset_right (fun _ : Euclidean d => (B⁻¹ : ℂ))
        (testSchwartz ℂ φ)).trans hs
    · intro n hn x
      change ‖iteratedFDeriv ℝ n ((B⁻¹ : ℂ) • (⇑(testSchwartz ℂ φ))) x‖ ≤ 1
      rw [iteratedFDeriv_const_smul_apply ((testSchwartz ℂ φ).smooth n).contDiffAt, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hB]
      calc
        B⁻¹ * ‖iteratedFDeriv ℝ n (testSchwartz ℂ φ) x‖ ≤ B⁻¹ * B :=
          mul_le_mul_of_nonneg_left (hder n hn x) (inv_nonneg.mpr hB.le)
        _ = 1 := inv_mul_cancel₀ hB.ne'
  have h := hbound ψ hψ r hr
  have heq : dilateTest r hr.ne' φ = (B : ℂ) • dilateTest r hr.ne' ψ := by
    simp [ψ, smul_smul, hB.ne']
  rw [heq, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left h hB.le

/-- A polynomial in a real scale whose norm tends to zero is identically
zero. Complex coefficients do not require a real leading coefficient. -/
theorem polynomial_eq_zero_of_real_ray_limit (p : Polynomial ℂ)
    (hp : Filter.Tendsto (fun t : ℝ => ‖p.eval (t : ℂ)‖)
      Filter.atTop (𝓝 0)) : p = 0 := by
  have hd : p.degree ≤ 0 := by
    by_contra h
    have hz : Filter.Tendsto (fun t : ℝ => ‖(t : ℂ)‖) Filter.atTop Filter.atTop := by
      simpa using (Filter.tendsto_abs_atTop_atTop :
        Filter.Tendsto (fun t : ℝ => |t|) Filter.atTop Filter.atTop)
    exact (not_tendsto_atTop_of_tendsto_nhds hp) (p.tendsto_norm_atTop (lt_of_not_ge h) hz)
  have heq := Polynomial.eq_C_of_degree_le_zero hd
  have hpc (t : ℝ) : ‖p.eval (t : ℂ)‖ = ‖p.coeff 0‖ := by
    rw [heq, Polynomial.eval_C, Polynomial.coeff_C_zero]
  simp_rw [hpc] at hp
  have hc : ‖p.coeff 0‖ = 0 := tendsto_const_nhds_iff.mp hp
  rw [heq, norm_eq_zero.mp hc, Polynomial.C_0]

/-- Coordinate word monomials have their actual homogeneous degree under
real dilation. This includes the empty word in every dimension. -/
theorem wordMonomial_smul {d : ℕ} (w : List (Fin d)) (t : ℝ) (x : Euclidean d) :
    wordMonomial w (t • x) = (t : ℂ) ^ w.length * wordMonomial w x := by
  induction w with
  | nil => simp [wordMonomial]
  | cons i w ih =>
    simp only [wordMonomial, List.length_cons, pow_succ, ih, PiLp.smul_apply,
      smul_eq_mul, Complex.ofReal_mul]
    ring

/-- A finite coordinate polynomial cannot have the physical decay required
of a kernel in positive dimension. This is the algebraic elimination step
for inverse transforms of distributions supported at frequency zero. -/
theorem polynomial_decay_zero {d : ℕ} (hd : 0 < d)
    (s : Finset (List (Fin d))) (c : List (Fin d) → ℂ) (C : ℝ) (_hC : 0 ≤ C)
    (hdecay : ∀ x : Euclidean d, x ≠ 0 →
      ‖∑ w ∈ s, c w * wordMonomial w x‖ ≤ C * (‖x‖ ^ d)⁻¹) :
    ∀ x : Euclidean d, ∑ w ∈ s, c w * wordMonomial w x = 0 := by
  classical
  let f : Euclidean d → ℂ := fun x => ∑ w ∈ s, c w * wordMonomial w x
  have hnonzero : ∀ x : Euclidean d, x ≠ 0 → f x = 0 := by
    intro x hx
    let p : Polynomial ℂ := ∑ w ∈ s,
      Polynomial.C (c w * wordMonomial w x) * Polynomial.X ^ w.length
    have hp (t : ℝ) : p.eval (t : ℂ) = f (t • x) := by
      simp only [p, f, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, wordMonomial_smul]
      apply Finset.sum_congr rfl
      intro w hw
      ring
    have hnorm : Filter.Tendsto (fun t : ℝ => ‖t • x‖ ^ d)
        Filter.atTop Filter.atTop := by
      have ht : Filter.Tendsto (fun t : ℝ => ‖t • x‖) Filter.atTop Filter.atTop := by
        simp only [norm_smul, Real.norm_eq_abs]
        exact Filter.tendsto_abs_atTop_atTop.atTop_mul_const (norm_pos_iff.mpr hx)
      exact (Filter.tendsto_pow_atTop hd.ne').comp ht
    have hlim : Filter.Tendsto (fun t : ℝ => ‖p.eval (t : ℂ)‖)
        Filter.atTop (𝓝 0) := by
      apply squeeze_zero' (Filter.Eventually.of_forall (fun t => norm_nonneg _))
        (g := fun t : ℝ => C * (‖t • x‖ ^ d)⁻¹)
      · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
        rw [hp]
        exact hdecay (t • x) (smul_ne_zero ht.ne' hx)
      · simpa using (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnorm) :
          Filter.Tendsto (fun t : ℝ => C * (‖t • x‖ ^ d)⁻¹) Filter.atTop (𝓝 (C * 0)))
    have hz := polynomial_eq_zero_of_real_ray_limit p hlim
    have hz1 : p.eval ((1 : ℝ) : ℂ) = 0 := by rw [hz, Polynomial.eval_zero]
    rw [hp, one_smul] at hz1
    exact hz1
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro w hw
    apply continuous_const.mul
    clear hw
    induction w with
    | nil => exact continuous_const
    | cons i w ih =>
      exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous).mul ih
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  intro x
  exact (show EqOn f (fun _ => 0) ({0}ᶜ : Set (Euclidean d)) from
    fun y hy => hnonzero y hy).closure hf continuous_const
      (dense_compl_singleton (0 : Euclidean d) x)

/-- Transport a compact smooth function on Euclidean space to the original
coordinate LF test space. This is inverse to the accepted `testSchwartz` bridge
on underlying functions. -/
def euclideanTest {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : Tests ℂ (⊤ : Opens (Domain d)) :=
  ⟨fun x => f ((EuclideanSpace.equiv (Fin d) ℝ).symm x),
    hf.comp (EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff,
    hc.comp_homeomorph (EuclideanSpace.equiv (Fin d) ℝ).symm.toHomeomorph,
    subset_univ _⟩

@[simp] theorem testSchwartz_euclideanTest {d : ℕ} (f : Euclidean d → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ⇑(testSchwartz ℂ (euclideanTest f hf hc)) = f := by
  funext x
  change f ((EuclideanSpace.equiv (Fin d) ℝ).symm
    ((EuclideanSpace.equiv (Fin d) ℝ) x)) = f x
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- A continuous off-zero function is determined pointwise by its LF test
pairings. No local integrability at the origin is assumed. -/
theorem continuous_offZero_zero_of_test_pairings {d : ℕ} (f : Euclidean d → ℂ)
    (hf : ContinuousOn f ({0}ᶜ : Set (Euclidean d)))
    (hzero : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      0 ∉ tsupport (testSchwartz ℂ φ) → ∫ x, f x * testSchwartz ℂ φ x = 0) :
    ∀ x : Euclidean d, x ≠ 0 → f x = 0 := by
  have hae : ∀ᵐ x : Euclidean d, x ∈ ({0}ᶜ : Set (Euclidean d)) → f x = 0 := by
    apply isOpen_compl_singleton.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrableOn isOpen_compl_singleton.measurableSet)
    intro g hg hc hs
    let q : Euclidean d → ℂ := fun x => (g x : ℂ)
    have hq : ContDiff ℝ ∞ q := Complex.ofRealCLM.contDiff.comp hg
    have hqc : HasCompactSupport q := hc.comp_left (g := Complex.ofReal) (by simp)
    have hqs : tsupport q ⊆ ({0}ᶜ : Set (Euclidean d)) :=
      (tsupport_comp_subset (g := Complex.ofReal) (by simp) g).trans hs
    have hz : 0 ∉ tsupport (testSchwartz ℂ (euclideanTest q hq hqc)) := by
      rw [testSchwartz_euclideanTest]
      exact fun h => hqs h (Set.mem_singleton 0)
    have h := hzero (euclideanTest q hq hqc) hz
    simp only [testSchwartz_euclideanTest] at h
    simpa only [q, Complex.real_smul, mul_comm] using h
  have hae' : f =ᵐ[volume.restrict ({0}ᶜ : Set (Euclidean d))] (fun _ => 0) :=
    (ae_restrict_iff' isOpen_compl_singleton.measurableSet).mpr hae
  exact fun x hx => Measure.eqOn_open_of_ae_eq hae' isOpen_compl_singleton hf
    continuousOn_const hx

/-- Word monomials are continuous on the whole Euclidean space. -/
theorem continuous_wordMonomial {d : ℕ} (w : List (Fin d)) : Continuous (wordMonomial w) := by
  induction w with
  | nil => exact continuous_const
  | cons i w ih =>
    exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous).mul ih

/-- Two decaying physical kernels cannot differ by a regular polynomial.
The equality is on every original LF test and the conclusion is equality of
the original distributions, including their possible terms supported at zero. -/
theorem polynomial_kernel_discrepancy_zero {d : ℕ} (hd : 0 < d)
    (K L : KernelDistribution d) (k l : Euclidean d → ℂ)
    (hk : KernelBounds K k) (hl : KernelBounds L l)
    (s : Finset (List (Fin d))) (c : List (Fin d) → ℂ)
    (hpoly : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      Integrable (fun x => (∑ w ∈ s, c w * wordMonomial w x) * testSchwartz ℂ φ x) ∧
      K φ - L φ = ∫ x, (∑ w ∈ s, c w * wordMonomial w x) * testSchwartz ℂ φ x) :
    K = L := by
  classical
  let p : Euclidean d → ℂ := fun x => ∑ w ∈ s, c w * wordMonomial w x
  have hp : Continuous p := continuous_finsetSum _
    (fun w _ => continuous_const.mul (continuous_wordMonomial w))
  have heq : ∀ x : Euclidean d, x ≠ 0 → k x - l x - p x = 0 := by
    apply continuous_offZero_zero_of_test_pairings _
      ((hk.2.1.continuousOn.sub hl.2.1.continuousOn).sub hp.continuousOn)
    intro φ hφ
    obtain ⟨hki, hK⟩ := hk.1 φ hφ
    obtain ⟨hli, hL⟩ := hl.1 φ hφ
    obtain ⟨hpi, hP⟩ := hpoly φ
    change Integrable (fun x => p x * testSchwartz ℂ φ x) at hpi
    change K φ - L φ = ∫ x, p x * testSchwartz ℂ φ x at hP
    change (∫ x, (k x - l x - p x) * testSchwartz ℂ φ x) = 0
    simp_rw [sub_mul]
    have hsub : Integrable (fun x => k x * testSchwartz ℂ φ x - l x * testSchwartz ℂ φ x) :=
      hki.sub hli
    rw [integral_sub hsub hpi, integral_sub hki hli, ← hK, ← hL, ← hP, sub_self]
  obtain ⟨C, hC, hkb⟩ := hk.2.2 0 (fun i => Fin.elim0 i)
  obtain ⟨D, hD, hlb⟩ := hl.2.2 0 (fun i => Fin.elim0 i)
  have hz : ∀ x : Euclidean d, p x = 0 := by
    apply polynomial_decay_zero hd s c (C + D) (add_nonneg hC hD)
    intro x hx
    change ‖p x‖ ≤ _
    have hpx : p x = k x - l x := by linear_combination -(heq x hx)
    rw [hpx]
    have h1 := hkb x hx
    have h2 := hlb x hx
    simp only [iteratedFDeriv_zero_apply, Nat.add_zero] at h1 h2
    exact (norm_sub_le _ _).trans (by nlinarith)
  ext φ
  have h := (hpoly φ).2
  change K φ - L φ = ∫ x, p x * testSchwartz ℂ φ x at h
  simp only [hz, zero_mul, integral_zero, sub_eq_zero] at h
  exact h

/-- Fourier transformation sends normalized compact bumps to a family with
uniform bounds for any prescribed weighted derivative. The number of bounded
input derivatives is fixed before the bump is chosen. -/
theorem bump_fourier_decay (d n L : ℕ) : ∃ N : ℕ, d < N ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      NormalizedBump N φ → ∀ ξ : Euclidean d,
      (1 + ‖ξ‖) ^ L * ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ φ)) ξ‖ ≤ C := by
  let qout : Seminorm ℂ (Schwartz ℂ d) :=
    (Finset.Iic (L, n)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ)
  let q : Seminorm ℂ (Schwartz ℂ d) := qout.comp schwartzFourier.toLinearMap
  have hq : Continuous q :=
    (Seminorm.continuous_finsetSup fun i _ =>
      (schwartz_withSeminorms ℂ (Euclidean d) ℂ).continuous_seminorm i).comp
      schwartzFourier.continuous
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ (Euclidean d) ℂ) q hq
  let N := max (d + 1) (s.sup Prod.snd)
  refine ⟨N, lt_of_lt_of_le (Nat.lt_succ_self d) (le_max_left _ _),
    2 ^ L * C, mul_nonneg (by positivity) C.coe_nonneg, ?_⟩
  intro φ hφ ξ
  have hs : (s.sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ)) (testSchwartz ℂ φ) ≤ 1 := by
    apply Seminorm.finset_sup_apply_le zero_le_one
    intro i hi
    exact bump_seminorm d N i.1 i.2 φ hφ
      ((Finset.le_sup (f := Prod.snd) hi).trans (le_max_right _ _))
  have hqC : q (testSchwartz ℂ φ) ≤ C := by
    calc
      q (testSchwartz ℂ φ) ≤ (C : ℝ) *
          (s.sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ)) (testSchwartz ℂ φ) := hC _
      _ ≤ C := by simpa using mul_le_mul_of_nonneg_left hs C.coe_nonneg
  calc
    (1 + ‖ξ‖) ^ L * ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ φ)) ξ‖ ≤
        2 ^ L * q (testSchwartz ℂ φ) :=
      SchwartzMap.one_add_le_sup_seminorm_apply (m := (L, n)) le_rfl le_rfl _ ξ
    _ ≤ 2 ^ L * C := mul_le_mul_of_nonneg_left hqC (by positivity)

/-- Function-level version of the Fourier dilation identity. -/
theorem schwartzFourier_dilateTest {d : ℕ}
    (φ : Tests ℂ (⊤ : Opens (Domain d))) (r : ℝ) (hr : 0 < r) :
    ⇑(schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' φ))) =
      fun ξ => (r ^ d : ℝ) • schwartzFourier (testSchwartz ℂ φ) (r • ξ) := by
  funext ξ
  change (𝓕 (testSchwartz ℂ (dilateTest r hr.ne' φ)) : Schwartz ℂ d) ξ = _
  rw [SchwartzMap.fourier_coe]
  have he : (⇑(testSchwartz ℂ (dilateTest r hr.ne' φ))) =
      fun x : Euclidean d => testSchwartz ℂ φ (r⁻¹ • x) := by
    funext x
    simp only [testSchwartz_apply, dilateTest_apply, map_smul]
  rw [he, fourier_dilate _ r hr]
  rfl

/-- Every frequency derivative has the exact dilation factor r^(d+n). -/
theorem fourier_dilate_derivative_norm {d : ℕ}
    (φ : Tests ℂ (⊤ : Opens (Domain d))) (r : ℝ) (hr : 0 < r) (n : ℕ)
    (ξ : Euclidean d) :
    ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' φ))) ξ‖ =
      r ^ (d + n) * ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ φ)) (r • ξ)‖ := by
  rw [schwartzFourier_dilateTest φ r hr]
  have hs : ContDiffAt ℝ n
      (fun x : Euclidean d => schwartzFourier (testSchwartz ℂ φ) (r • x)) ξ := by
    exact (((schwartzFourier (testSchwartz ℂ φ)).smooth n).comp
      (contDiff_id.const_smul r)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hs]
  rw [iteratedFDeriv_comp_const_smul r ((schwartzFourier (testSchwartz ℂ φ)).smooth n)]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _), pow_add, mul_assoc]

/-- The uniform annular Fourier estimate after rescaling, before the physical
kernel's amplitude factor r^(-d) is applied. -/
theorem dilated_bump_fourier_decay (d n L : ℕ) : ∃ N : ℕ, d < N ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      NormalizedBump N φ → ∀ (r : ℝ) (hr : 0 < r) (ξ : Euclidean d),
      (1 + r * ‖ξ‖) ^ L *
        ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' φ))) ξ‖ ≤
        C * r ^ (d + n) := by
  obtain ⟨N, hN, C, hC, hb⟩ := bump_fourier_decay d n L
  refine ⟨N, hN, C, hC, ?_⟩
  intro φ hφ r hr ξ
  have h := hb φ hφ (r • ξ)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr] at h
  rw [fourier_dilate_derivative_norm φ r hr n ξ]
  calc
    (1 + r * ‖ξ‖) ^ L *
        (r ^ (d + n) * ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ φ)) (r • ξ)‖) =
        r ^ (d + n) * ((1 + r * ‖ξ‖) ^ L *
          ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ φ)) (r • ξ)‖) := by ring
    _ ≤ r ^ (d + n) * C := mul_le_mul_of_nonneg_left h (pow_nonneg hr.le _)
    _ = C * r ^ (d + n) := mul_comm _ _

/-- Coordinate mixed-derivative kernel bounds control the full operator norm. -/
theorem kernel_iteratedFDeriv_bound {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean d, x ≠ 0 →
      ‖iteratedFDeriv ℝ n k x‖ ≤ C * (‖x‖ ^ (d + n))⁻¹ := by
  classical
  choose C hC hbound using hK.2.2 n
  refine ⟨∑ w : Fin n → Fin d, C w,
    Finset.sum_nonneg (fun w _ => hC w), ?_⟩
  intro x hx
  calc
    ‖iteratedFDeriv ℝ n k x‖ ≤
        ∑ w : Fin n → Fin d,
          ‖iteratedFDeriv ℝ n k x (fun j => basisVector (w j))‖ :=
      multilinear_coordinate_sum _
    _ ≤ ∑ w : Fin n → Fin d, C w * (‖x‖ ^ (d + n))⁻¹ :=
      Finset.sum_le_sum fun w _ => hbound w x hx
    _ = _ := (Finset.sum_mul ..).symm

/-- Local scalar chain rule; global regularity at the origin is not required. -/
theorem kernel_iteratedFDeriv_comp_smul {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) {r : ℝ} (hr : r ≠ 0)
    (n : ℕ) {x : Euclidean d} (hx : x ≠ 0) :
    iteratedFDeriv ℝ n (fun y => k (r • y)) x =
      r ^ n • iteratedFDeriv ℝ n k (r • x) := by
  let g : Euclidean d →L[ℝ] Euclidean d := r • ContinuousLinearMap.id ℝ (Euclidean d)
  have hs : IsOpen ({0}ᶜ : Set (Euclidean d)) := isOpen_compl_singleton
  have hpre : IsOpen (g ⁻¹' ({0}ᶜ : Set (Euclidean d))) := hs.preimage g.continuous
  have hgx : g x ∈ ({0}ᶜ : Set (Euclidean d)) := by
    change r • x ≠ 0
    exact smul_ne_zero hr hx
  have h := g.iteratedFDerivWithin_comp_right hK.2.1 hs.uniqueDiffOn
    hpre.uniqueDiffOn hgx (show (n : ℕ∞ω) ≤ ∞ by simp)
  rw [iteratedFDerivWithin_of_isOpen n hpre hgx,
    iteratedFDerivWithin_of_isOpen n hs hgx] at h
  change iteratedFDeriv ℝ n (k ∘ g) x = _
  rw [h]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply]
  change iteratedFDeriv ℝ n k (r • x) (fun j => r • v j) = _
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp


/-- Derivative scaling for the physical family with degree-d amplitude. -/
theorem kernel_rescale_derivative_norm {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) {r : ℝ} (hr : 0 < r)
    (n : ℕ) {x : Euclidean d} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ n (fun y => (r ^ d : ℝ) • k (r • y)) x‖ =
      r ^ (d + n) * ‖iteratedFDeriv ℝ n k (r • x)‖ := by
  have hkAt : ContDiffAt ℝ ∞ k (r • x) :=
    hK.2.1.contDiffAt (isOpen_compl_singleton.mem_nhds (smul_ne_zero hr.ne' hx))
  have hfAt : ContDiffAt ℝ n (fun y => k (r • y)) x :=
    (hkAt.of_le (by simp)).comp x ((contDiff_id.const_smul r).contDiffAt)
  rw [iteratedFDeriv_const_smul_apply' hfAt,
    kernel_iteratedFDeriv_comp_smul hK hr.ne' n hx, smul_smul, ← pow_add]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _)]

/-- The normalized physical rescalings satisfy a common radial estimate. -/
theorem kernel_rescale_derivative_bound {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ x : Euclidean d, x ≠ 0 →
      ‖iteratedFDeriv ℝ n (fun y => (r ^ d : ℝ) • k (r • y)) x‖ ≤
        C * (‖x‖ ^ (d + n))⁻¹ := by
  obtain ⟨C, hC, hb⟩ := kernel_iteratedFDeriv_bound hK n
  refine ⟨C, hC, ?_⟩
  intro r hr x hx
  rw [kernel_rescale_derivative_norm hK hr n hx]
  calc
    r ^ (d + n) * ‖iteratedFDeriv ℝ n k (r • x)‖ ≤
        r ^ (d + n) * (C * (‖r • x‖ ^ (d + n))⁻¹) :=
      mul_le_mul_of_nonneg_left (hb _ (smul_ne_zero hr.ne' hx)) (pow_nonneg hr.le _)
    _ = C * (‖x‖ ^ (d + n))⁻¹ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow, mul_inv_rev]
      field_simp


/-- A fixed inner radius gives a uniform bound on every exterior annulus. -/
theorem kernel_rescale_annular_bound {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (n : ℕ)
    {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ x : Euclidean d, a ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ n (fun y => (r ^ d : ℝ) • k (r • y)) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := kernel_rescale_derivative_bound hK n
  refine ⟨C * (a ^ (d + n))⁻¹, mul_nonneg hC (by positivity), ?_⟩
  intro r hr x hx
  have hax : 0 < ‖x‖ := ha.trans_le hx
  exact (hb r hr x (norm_pos_iff.mp hax)).trans
    (mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le hx _)) hC)

/-- Any prescribed finite list of derivatives admits a common annular bound. -/
theorem kernel_rescale_annular_bounds {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (N : ℕ)
    {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), n ≤ N → ∀ (r : ℝ), 0 < r →
      ∀ x : Euclidean d, a ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ n (fun y => (r ^ d : ℝ) • k (r • y)) x‖ ≤ C := by
  classical
  choose C hC hb using fun n => kernel_rescale_annular_bound hK n ha
  refine ⟨∑ n ∈ Finset.range (N + 1), C n,
    Finset.sum_nonneg (fun n _ => hC n), ?_⟩
  intro n hn r hr x hx
  exact (hb n r hr x hx).trans
    (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

/-- Physical rescaling preserves off-zero smoothness. -/
theorem kernel_rescale_contDiffOn {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) {r : ℝ} (hr : r ≠ 0) :
    ContDiffOn ℝ ∞ (fun y => (r ^ d : ℝ) • k (r • y))
      ({0}ᶜ : Set (Euclidean d)) := by
  apply ContDiffOn.const_smul
  exact hK.2.1.comp (contDiff_id.const_smul r).contDiffOn
    (fun x hx => smul_ne_zero hr hx)


/-- A smooth bounded-derivative multiplier supported outside a large ball
has small product seminorms on every fixed Schwartz function. -/
theorem tail_product_seminorm {d : ℕ} (φ ψ : Schwartz ℂ d)
    (g : Euclidean d → ℂ) (hg : ContDiff ℝ ∞ g)
    (heq : ∀ x, ψ x = g x * φ x) (R : ℝ) (hR : 0 < R)
    (hz : ∀ x, ‖x‖ < R → g x = 0) (B : ℕ → ℝ)
    (hB : ∀ i x, ‖iteratedFDeriv ℝ i g x‖ ≤ B i) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n ψ ≤ R⁻¹ *
      ∑ i ∈ Finset.range (n+1),
        (n.choose i : ℝ) * B i * SchwartzMap.seminorm ℂ (k+1) (n-i) φ := by
  have hB0 (i : ℕ) : 0 ≤ B i := (norm_nonneg _).trans (hB i 0)
  have hconst : 0 ≤ ∑ i ∈ Finset.range (n+1),
      (n.choose i : ℝ) * B i * SchwartzMap.seminorm ℂ (k+1) (n-i) φ := by
    exact Finset.sum_nonneg fun i hi => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hB0 i)) (apply_nonneg _ _)
  apply SchwartzMap.seminorm_le_bound ℂ k n ψ (mul_nonneg (inv_nonneg.mpr hR.le) hconst)
  intro x
  by_cases hx : ‖x‖ < R
  · have hz' : (ψ : Euclidean d → ℂ) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hx] with y hy
      simp only [heq, hz y hy, zero_mul]
    rw [(hz'.iteratedFDeriv ℝ n).self_of_nhds]
    change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (0 : Euclidean d → ℂ) x‖ ≤ _
    simpa only [iteratedFDeriv_zero, norm_zero, mul_zero, Pi.zero_apply] using
      (mul_nonneg (inv_nonneg.mpr hR.le) hconst)
  · have hxR : R ≤ ‖x‖ := le_of_not_gt hx
    have hx0 : 0 < ‖x‖ := hR.trans_le hxR
    have hprod := norm_iteratedFDeriv_mul_le hg (φ.smooth ⊤) x (n := n) (by simp)
    have hf : (ψ : Euclidean d → ℂ) = fun x => g x * φ x := funext heq
    rw [hf]
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => g x * φ x) x‖ ≤
          ‖x‖ ^ k * ∑ i ∈ Finset.range (n+1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ *
              ‖iteratedFDeriv ℝ (n-i) φ x‖ :=
        mul_le_mul_of_nonneg_left hprod (pow_nonneg (norm_nonneg _) _)
      _ ≤ R⁻¹ * ∑ i ∈ Finset.range (n+1),
          (n.choose i : ℝ) * B i * SchwartzMap.seminorm ℂ (k+1) (n-i) φ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hφ := SchwartzMap.le_seminorm ℂ (k+1) (n-i) φ x
        have hs : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n-i) φ x‖ ≤
            R⁻¹ * SchwartzMap.seminorm ℂ (k+1) (n-i) φ := by
          rw [← div_eq_inv_mul]
          apply (le_div_iff₀ hR).mpr
          calc
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n-i) φ x‖ * R ≤
                ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n-i) φ x‖ * ‖x‖ := by gcongr
            _ = ‖x‖ ^ (k+1) * ‖iteratedFDeriv ℝ (n-i) φ x‖ := by rw [pow_succ]; ring
            _ ≤ _ := hφ
        calc
          ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ *
              ‖iteratedFDeriv ℝ (n-i) φ x‖) ≤
              (n.choose i : ℝ) * B i *
                (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n-i) φ x‖) := by
                  have h := mul_le_mul_of_nonneg_left (hB i x)
                    (show 0 ≤ (n.choose i : ℝ) from Nat.cast_nonneg _)
                  have h' := mul_le_mul_of_nonneg_right h
                    (norm_nonneg (iteratedFDeriv ℝ (n-i) φ x))
                  simpa only [mul_assoc, mul_left_comm, mul_comm] using
                    mul_le_mul_of_nonneg_left h' (pow_nonneg (norm_nonneg x) k)
          _ ≤ (n.choose i : ℝ) * B i *
              (R⁻¹ * SchwartzMap.seminorm ℂ (k+1) (n-i) φ) :=
            mul_le_mul_of_nonneg_left hs (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
          _ = _ := by ring

/-- Every derivative of a tail cutoff is uniformly bounded as its radius tends to infinity. -/
theorem tail_cutoff_derivative_bounds {d : ℕ}
    (b : ContDiffBump (0 : Euclidean d)) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ (n : ℕ) (R : ℝ), 1 ≤ R →
      ∀ x : Euclidean d,
      ‖iteratedFDeriv ℝ n (fun y => 1 - (b (R⁻¹ • y) : ℂ)) x‖ ≤ B n := by
  let c : Euclidean d → ℂ := fun x => (b x : ℂ)
  have hc : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hcc : HasCompactSupport c :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  let s : Schwartz ℂ d := hcc.toSchwartzMap hc
  refine ⟨fun n => 1 + SchwartzMap.seminorm ℂ 0 n s, ?_, ?_⟩
  · intro n
    exact add_nonneg zero_le_one (apply_nonneg _ _)
  · intro n R hR x
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hRi : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
    have hRi1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
    have hcR : ContDiff ℝ n (fun y => c (R⁻¹ • y)) :=
      (hc.of_le (by simp)).comp (contDiff_id.const_smul R⁻¹)
    have hconst : ‖iteratedFDeriv ℝ n (fun _ : Euclidean d => (1 : ℂ)) x‖ ≤ 1 := by
      by_cases hn : n = 0
      · subst n
        rw [norm_iteratedFDeriv_zero]
        norm_num
      · simpa only [iteratedFDeriv_const_of_ne hn, Pi.zero_apply, norm_zero] using (zero_le_one : (0:ℝ) ≤ 1)
    have hcBound : ‖iteratedFDeriv ℝ n (fun y => c (R⁻¹ • y)) x‖ ≤
        SchwartzMap.seminorm ℂ 0 n s := by
      rw [iteratedFDeriv_comp_const_smul R⁻¹ (hc.of_le (by simp)), norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hRi _)]
      have hb : ‖iteratedFDeriv ℝ n c (R⁻¹ • x)‖ ≤
          SchwartzMap.seminorm ℂ 0 n s :=
        SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ s n _
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hRi hRi1) (norm_nonneg _)).trans
        (by simpa using hb)
    change ‖iteratedFDeriv ℝ n
      ((fun _ : Euclidean d => (1 : ℂ)) - (fun y => c (R⁻¹ • y))) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply contDiffAt_const hcR.contDiffAt]
    exact (norm_sub_le _ _).trans (add_le_add hconst hcBound)

/-- A tail cutoff vanishes throughout the correspondingly expanded inner ball. -/
theorem tail_cutoff_eq_zero {d : ℕ}
    (b : ContDiffBump (0 : Euclidean d)) {R : ℝ} (hR : 1 ≤ R)
    {x : Euclidean d} (hx : ‖x‖ ≤ R * b.rIn) :
    1 - (b (R⁻¹ • x) : ℂ) = 0 := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have harg : ‖R⁻¹ • x‖ ≤ b.rIn := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
    calc
      R⁻¹ * ‖x‖ ≤ R⁻¹ * (R * b.rIn) :=
        mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hRpos.le)
      _ = b.rIn := by field_simp
  have hb : b (R⁻¹ • x) = 1 := b.one_of_mem_closedBall (by simpa using harg)
  simp [hb]

/-- Radius-one version used by compact approximation of Schwartz functions. -/
theorem tail_cutoff_eq_zero_of_norm_lt {d : ℕ}
    (b : ContDiffBump (0 : Euclidean d)) (hb : b.rIn = 1)
    {R : ℝ} (hR : 1 ≤ R) {x : Euclidean d} (hx : ‖x‖ < R) :
    1 - (b (R⁻¹ • x) : ℂ) = 0 := by
  apply tail_cutoff_eq_zero b hR
  simpa [hb] using hx.le

/-- Compact original LF tests approximate every Schwartz function in its full
Schwartz topology, using an expanding amplitude-one cutoff. -/
theorem exists_testSchwartz_tendsto {d : ℕ} (φ : Schwartz ℂ d) :
    ∃ ψ : ℕ → Tests ℂ (⊤ : Opens (Domain d)),
      Filter.Tendsto (fun j => testSchwartz ℂ (ψ j)) Filter.atTop (𝓝 φ) := by
  let b : ContDiffBump (0 : Euclidean d) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let R : ℕ → ℝ := fun j => j + 1
  have hR (j : ℕ) : 1 ≤ R j := by dsimp [R]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  let f : ℕ → Euclidean d → ℂ := fun j x => (b ((R j)⁻¹ • x) : ℂ) * φ x
  have hf (j : ℕ) : ContDiff ℝ ∞ (f j) :=
    (Complex.ofRealCLM.contDiff.comp (b.contDiff.comp
      (contDiff_id.const_smul (R j)⁻¹))).mul (φ.smooth ⊤)
  have hfc (j : ℕ) : HasCompactSupport (f j) := by
    have hc := b.hasCompactSupport.comp_homeomorph
      (Homeomorph.smulOfNeZero (R j)⁻¹ (inv_ne_zero (ne_of_gt (zero_lt_one.trans_le (hR j)))))
    exact (hc.comp_left (g := Complex.ofReal) (by simp)).mul_right
  let ψ : ℕ → Tests ℂ (⊤ : Opens (Domain d)) :=
    fun j => euclideanTest (f j) (hf j) (hfc j)
  obtain ⟨B, hB0, hB⟩ := tail_cutoff_derivative_bounds b
  refine ⟨ψ, ?_⟩
  apply (schwartz_withSeminorms ℂ (Euclidean d) ℂ).tendsto_nhds_atTop _ _ |>.mpr
  rintro ⟨k,n⟩ ε hε
  let C : ℝ := ∑ i ∈ Finset.range (n+1),
    (n.choose i : ℝ) * B i * SchwartzMap.seminorm ℂ (k+1) (n-i) φ
  have hlim : Filter.Tendsto (fun j : ℕ => (R j)⁻¹ * C) Filter.atTop (𝓝 0) := by
    have hRlim : Filter.Tendsto R Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa using (tendsto_inv_atTop_zero.comp hRlim).mul_const C
  obtain ⟨j₀, hj₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp hlim).2 ε hε)
  refine ⟨j₀, fun j hj => ?_⟩
  have hbnd := tail_product_seminorm φ (φ - testSchwartz ℂ (ψ j))
    (fun x => 1 - (b ((R j)⁻¹ • x) : ℂ))
    (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp
      (b.contDiff.comp (contDiff_id.const_smul (R j)⁻¹))))
    (by
      intro x
      change φ x - testSchwartz ℂ (euclideanTest (f j) (hf j) (hfc j)) x = _
      rw [testSchwartz_euclideanTest]
      dsimp [f]
      ring)
    (R j) (zero_lt_one.trans_le (hR j))
    (fun x hx => tail_cutoff_eq_zero_of_norm_lt b rfl (hR j) hx)
    B (fun i x => hB i (R j) (hR j) x) k n
  have hneg : SchwartzMap.seminorm ℂ k n (testSchwartz ℂ (ψ j) - φ) =
      SchwartzMap.seminorm ℂ k n (φ - testSchwartz ℂ (ψ j)) := by
    rw [← neg_sub, map_neg_eq_map]
  change SchwartzMap.seminorm ℂ k n (testSchwartz ℂ (ψ j) - φ) < ε
  rw [hneg]
  exact hbnd.trans_lt (hj₀ j hj)

/-- Original compact test pairings determine a tempered distribution globally. -/
theorem tempered_ext_of_testSchwartz {d : ℕ} {U V : Tempered ℂ d}
    (h : ∀ ψ : Tests ℂ (⊤ : Opens (Domain d)),
      U (testSchwartz ℂ ψ) = V (testSchwartz ℂ ψ)) : U = V := by
  ext φ
  obtain ⟨ψ, hψ⟩ := exists_testSchwartz_tendsto φ
  have hu := U.continuous.tendsto φ |>.comp hψ
  simp only [Function.comp_def, h] at hu
  exact tendsto_nhds_unique hu (V.continuous.tendsto φ |>.comp hψ)


/-- The compact-step inclusion into Schwartz space is continuous. -/
def stepToSchwartz {d : ℕ} (K : Compacts (Domain d)) :
    Step ℂ K →L[ℂ] SchwartzMap (Domain d) ℂ := by
  let L : Step ℂ K →ₗ[ℂ] SchwartzMap (Domain d) ℂ :=
    { toFun f := f.hasCompactSupport.toSchwartzMap f.contDiff
      map_add' f g := by ext; rfl
      map_smul' c f := by ext; rfl }
  refine { toLinearMap := L, cont := ?_ }
  obtain ⟨R, hR, hKR⟩ := K.isCompact.isBounded.subset_closedBall_lt 0 (0 : Domain d)
  refine WithSeminorms.continuous_of_isBounded
    (ContDiffMapSupportedIn.withSeminorms ℂ (Domain d) ℂ ⊤ K)
    (schwartz_withSeminorms ℂ (Domain d) ℂ) L fun q => ?_
  refine ⟨{q.2}, ⟨R ^ q.1, by positivity⟩, fun f => ?_⟩
  simp only [Finset.sup_singleton]
  apply SchwartzMap.seminorm_le_bound ℂ q.1 q.2 _ (by positivity)
  intro x
  change ‖x‖ ^ q.1 * ‖iteratedFDeriv ℝ q.2 f x‖ ≤ _
  by_cases hx : x ∈ K
  · have hxR : ‖x‖ ≤ R := by simpa using hKR hx
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxR _)
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ)
      (norm_nonneg _) (pow_nonneg hR.le _)
  · have hz : iteratedFDeriv ℝ q.2 f x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => hx (f.tsupport_subset (tsupport_iteratedFDeriv_subset q.2 h))
    rw [hz, norm_zero, mul_zero]
    positivity

/-- Canonical continuous embedding of the original LF test space into Schwartz. -/
def testSchwartzCLM {d : ℕ} :
    Tests ℂ (⊤ : Opens (Domain d)) →L[ℂ] Schwartz ℂ d :=
  TestFunction.limitCLM ℂ (testSchwartz ℂ)
    (fun K _ => (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (EuclideanSpace.equiv (Fin d) ℝ)).comp (stepToSchwartz K))
    (fun _ _ _ => by ext; rfl)

/-- Restriction of a tempered distribution to the original LF tests. -/
def temperedRestriction {d : ℕ} (U : Tempered ℂ d) : KernelDistribution d :=
  U.comp testSchwartzCLM

@[simp] theorem temperedRestriction_apply {d : ℕ} (U : Tempered ℂ d)
    (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    temperedRestriction U φ = U (testSchwartz ℂ φ) := rfl

/-- Off-zero annihilation gives actual singleton support on the LF distribution. -/
theorem support_restriction_subset_zero {d : ℕ} (U : Tempered ℂ d)
    (hU : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      0 ∉ tsupport (testSchwartz ℂ φ) → U (testSchwartz ℂ φ) = 0) :
    distributionSupport (temperedRestriction U) ⊆ {0} := by
  intro x hx
  by_contra hx0
  apply hx.2
  apply Set.mem_sUnion.mpr
  refine ⟨{0}ᶜ, ⟨isOpen_compl_singleton, subset_univ _, ?_⟩, hx0⟩
  intro φ hφ
  apply hU φ
  intro hz
  have hz' : (0 : Domain d) ∈ tsupport φ := by
    have he := tsupport_comp_eq_preimage (⇑φ)
      (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph
    change tsupport (⇑(testSchwartz ℂ φ)) = _ at he
    rw [he] at hz
    simpa using hz
  exact hφ hz' (by simp)

/-- The LF jet and Euclidean jet under the canonical coordinate identification agree. -/
theorem coordinateJet_testSchwartz {d n : ℕ} (w : Fin n → Fin d)
    (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    iteratedFDeriv ℝ n (testSchwartz ℂ φ) 0 (fun j => basisVector (w j)) =
      coordinateJet ℂ ⊤ 0 w φ := by
  change iteratedFDeriv ℝ n (⇑φ ∘ (EuclideanSpace.equiv (Fin d) ℝ)) 0 _ = _
  have he := (EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap.iteratedFDeriv_comp_right
    φ.contDiff (0 : Euclidean d) (i := n)
      (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
  change iteratedFDeriv ℝ n (⇑φ ∘ (EuclideanSpace.equiv (Fin d) ℝ)) 0 = _ at he
  rw [he]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero,
    coordinateJet_apply]
  congr 1

/-- Reverse word order accounts for transposition of the derivative operators. -/
theorem deltaDerivative_reverse_ofFn_apply {d n : ℕ} (w : Fin n → Fin d)
    (φ : Schwartz ℂ d) :
    deltaDerivative (List.ofFn w).reverse φ =
      (-1 : ℂ) ^ n * iteratedFDeriv ℝ n φ 0 (fun j => basisVector (w j)) := by
  rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  induction n generalizing φ with
  | zero => simp [deltaDerivative, delta_apply]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat, deltaDerivative]
    change -(deltaDerivative (List.ofFn (Fin.init w)).reverse
      (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector (w (Fin.last n))) φ)) = _
    rw [ih]
    rw [LineDeriv.iteratedLineDerivOp_succ_right]
    simp only [Fin.init_def, LineDeriv.lineDerivOpCLM_apply]
    rw [pow_succ]
    ring

/-- Accepted LF point-support classification, expressed with the compatible
actual tempered delta derivatives on every original test. -/
theorem point_supported_tempered_on_tests {d : ℕ} (U : Tempered ℂ d)
    (hU : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      0 ∉ tsupport (testSchwartz ℂ φ) → U (testSchwartz ℂ φ) = 0) :
    ∃ (m : ℕ) (c : JetIndex d m → ℂ),
      ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
        U (testSchwartz ℂ φ) =
          (∑ i, c i • deltaDerivative (List.ofFn i.2).reverse) (testSchwartz ℂ φ) := by
  obtain ⟨m, c, hc⟩ := point_supported_distributions ℂ d ⊤ 0 (by trivial)
    (temperedRestriction U) (support_restriction_subset_zero U hU)
  refine ⟨m, c, ?_⟩
  intro φ
  have h := congrArg (fun T : KernelDistribution d => T φ) hc
  change U (testSchwartz ℂ φ) = _ at h
  rw [h]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [deltaDerivative_reverse_ofFn_apply, coordinateJet_testSchwartz]
  rfl


/-- A smooth cutoff supported away from the exceptional point removes the
singularity without changing the distribution's off-zero function. -/
theorem contDiff_cutoff_mul_offZero {d : ℕ} (a f : Euclidean d → ℂ)
    (ha : ContDiff ℝ ∞ a) (ha0 : 0 ∉ tsupport a)
    (hf : ContDiffOn ℝ ∞ f ({0}ᶜ : Set (Euclidean d))) :
    ContDiff ℝ ∞ (fun x => a x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have haev : a =ᶠ[nhds 0] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds ha0] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hev : (fun x => a x * f x) =ᶠ[nhds 0] (fun _ => (0 : ℂ)) := by
      filter_upwards [haev] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact ha.contDiffAt.mul (hf.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hx)))

/-- The local Leibniz estimate applies to a function smooth away from zero,
without imposing a false global regularity hypothesis on the raw kernel. -/
theorem cutoff_mul_derivative_bound {d n : ℕ} (a f : Euclidean d → ℂ)
    (ha : ContDiff ℝ ∞ a)
    (hf : ContDiffOn ℝ ∞ f ({0}ᶜ : Set (Euclidean d)))
    (x : Euclidean d) (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ n (fun y => a y * f y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i a x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖ := by
  have hx' : x ∈ ({0}ᶜ : Set (Euclidean d)) := by simpa using hx
  have h := norm_iteratedFDerivWithin_mul_le ha.contDiffOn hf
    isOpen_compl_singleton.uniqueDiffOn hx' (n := n) (by simp)
  simpa only [iteratedFDerivWithin_of_isOpen _ isOpen_compl_singleton hx'] using h

/-- Uniform finite derivative bounds for an annular family survive a fixed
cutoff. The single constant is independent of the family parameter. -/
theorem cutoff_family_derivative_bound {d : ℕ} {I : Type*} (N : ℕ)
    (a : Euclidean d → ℂ) (f : I → Euclidean d → ℂ)
    (ha : ContDiff ℝ ∞ a) (ha0 : 0 ∉ tsupport a)
    (hf : ∀ t, ContDiffOn ℝ ∞ (f t) ({0}ᶜ : Set (Euclidean d)))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha_bound : ∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n a x‖ ≤ A)
    (hf_bound : ∀ t, ∀ n ≤ N, ∀ x ∈ tsupport a,
      ‖iteratedFDeriv ℝ n (f t) x‖ ≤ B) :
    ∀ t, ∀ n ≤ N, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => a y * f t y) x‖ ≤ (2 : ℝ)^N * A * B := by
  intro t n hn x
  by_cases hx : x ∈ tsupport a
  · have hx0 : x ≠ 0 := fun he => ha0 (he ▸ hx)
    calc
      ‖iteratedFDeriv ℝ n (fun y => a y * f t y) x‖ ≤
          ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i a x‖ * ‖iteratedFDeriv ℝ (n-i) (f t) x‖ :=
        cutoff_mul_derivative_bound a (f t) ha (hf t) x hx0
      _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * A * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ N := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (ha_bound i hi' x) (by positivity))
          (hf_bound t (n-i) (le_trans (Nat.sub_le _ _) hn) x hx)
          (norm_nonneg _) (mul_nonneg (by positivity) hA)
      _ = (2 : ℝ)^n * A * B := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose n
      _ ≤ (2 : ℝ)^N * A * B :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn) hA) hB
  · have hzero : iteratedFDeriv ℝ n (fun y => a y * f t y) x = 0 := by
      apply Function.notMem_support.mp
      intro h
      exact hx (tsupport_mul_subset_left (support_iteratedFDeriv_subset n h))
    rw [hzero, norm_zero]
    positivity

/-- The Fourier decay bound is linear in any common Cᴺ bound. -/
theorem dilated_test_fourier_decay_bound (d n L : ℕ) : ∃ N : ℕ, d < N ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      tsupport (testSchwartz ℂ φ) ⊆ Metric.closedBall 0 1 →
      ∀ B : ℝ, 0 < B →
      (∀ i ≤ N, ∀ x : Euclidean d,
        ‖iteratedFDeriv ℝ i (testSchwartz ℂ φ) x‖ ≤ B) →
      ∀ (r : ℝ) (hr : 0 < r) (ξ : Euclidean d),
      (1 + r * ‖ξ‖) ^ L *
        ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' φ))) ξ‖ ≤
        C * B * r ^ (d + n) := by
  obtain ⟨N, hN, C, hC, hb⟩ := dilated_bump_fourier_decay d n L
  refine ⟨N, hN, C, hC, ?_⟩
  intro φ hs B hB hder r hr ξ
  let ψ := (B⁻¹ : ℂ) • φ
  have hψ : NormalizedBump N ψ := by
    constructor
    · rw [show testSchwartz ℂ ψ = (B⁻¹ : ℂ) • testSchwartz ℂ φ by simp [ψ]]
      exact (tsupport_smul_subset_right (fun _ : Euclidean d => (B⁻¹ : ℂ))
        (testSchwartz ℂ φ)).trans hs
    · intro i hi x
      change ‖iteratedFDeriv ℝ i ((B⁻¹ : ℂ) • (⇑(testSchwartz ℂ φ))) x‖ ≤ 1
      rw [iteratedFDeriv_const_smul_apply ((testSchwartz ℂ φ).smooth i).contDiffAt,
        norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
      calc
        B⁻¹ * ‖iteratedFDeriv ℝ i (testSchwartz ℂ φ) x‖ ≤ B⁻¹ * B :=
          mul_le_mul_of_nonneg_left (hder i hi x) (inv_nonneg.mpr hB.le)
        _ = 1 := inv_mul_cancel₀ hB.ne'
  have heq : dilateTest r hr.ne' φ = (B : ℂ) • dilateTest r hr.ne' ψ := by
    simp [ψ, smul_smul, hB.ne']
  rw [heq]
  rw [show testSchwartz ℂ ((B : ℂ) • dilateTest r hr.ne' ψ) =
    (B : ℂ) • testSchwartz ℂ (dilateTest r hr.ne' ψ) by ext x; rfl]
  rw [map_smul]
  change (1 + r * ‖ξ‖)^L * ‖iteratedFDeriv ℝ n
    ((B : ℂ) • (⇑(schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' ψ))))) ξ‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply
    ((schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' ψ))).smooth n).contDiffAt,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
  calc
    (1 + r * ‖ξ‖)^L * (B *
      ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' ψ))) ξ‖) =
        B * ((1 + r * ‖ξ‖)^L *
      ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' ψ))) ξ‖) := by ring
    _ ≤ B * (C * r ^ (d+n)) := mul_le_mul_of_nonneg_left (hb ψ hψ r hr ξ) hB.le
    _ = C * B * r ^ (d+n) := by ring

/-- A fixed annular cutoff of the kernel has the Fourier derivative estimates
claimed in the source, uniformly in the physical radius. -/
theorem annular_kernel_fourier_decay {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k)
    (a : Euclidean d → ℂ) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ Metric.closedBall 0 1)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hinner : ∀ x ∈ tsupport a, ρ ≤ ‖x‖)
    (n L : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r →
      ∃ φ : Tests ℂ (⊤ : Opens (Domain d)),
        ⇑(testSchwartz ℂ φ) = (fun x => a (r⁻¹ • x) * k x) ∧
        ∀ ξ : Euclidean d,
          (1 + r * ‖ξ‖)^L * ‖iteratedFDeriv ℝ n
            (schwartzFourier (testSchwartz ℂ φ)) ξ‖ ≤ C * r^n := by
  obtain ⟨N, hN, C, hC, hfourier⟩ := dilated_test_fourier_decay_bound d n L
  obtain ⟨A, hA, hab⟩ := hc.exists_bound_iteratedFDeriv ha N
  obtain ⟨B, hB, hfb⟩ := kernel_rescale_annular_bounds hK N hρ
  have ha0 : 0 ∉ tsupport a := by
    intro hx
    have h := hinner 0 hx
    exact hρ.not_ge (by simpa using h)
  let f : Set.Ioi (0 : ℝ) → Euclidean d → ℂ :=
    fun r x => (r.val ^ d : ℝ) • k (r.val • x)
  have hf (r : Set.Ioi (0 : ℝ)) :
      ContDiffOn ℝ ∞ (f r) ({0}ᶜ : Set (Euclidean d)) :=
    kernel_rescale_contDiffOn hK r.property.ne'
  have hder := cutoff_family_derivative_bound N a f ha ha0 hf A B hA hB hab
    (fun r i hi x hx => hfb i hi r.val r.property x (hinner x hx))
  let D : ℝ := 1 + (2 : ℝ)^N * A * B
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨C * D, mul_nonneg hC hD.le, ?_⟩
  intro r hr
  let q : Euclidean d → ℂ := fun x => a x * f ⟨r, hr⟩ x
  have hq : ContDiff ℝ ∞ q := contDiff_cutoff_mul_offZero a (f ⟨r, hr⟩) ha ha0 (hf _)
  have hqc : HasCompactSupport q := hc.mul_right
  let ψ := euclideanTest q hq hqc
  have hψs : tsupport (testSchwartz ℂ ψ) ⊆ Metric.closedBall 0 1 := by
    rw [testSchwartz_euclideanTest]
    exact tsupport_mul_subset_left.trans hs
  have hψder : ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i (testSchwartz ℂ ψ) x‖ ≤ D := by
    rw [testSchwartz_euclideanTest]
    intro i hi x
    exact (hder ⟨r, hr⟩ i hi x).trans (by dsimp [D]; linarith)
  let φ := ((r^d)⁻¹ : ℂ) • dilateTest r hr.ne' ψ
  refine ⟨φ, ?_, ?_⟩
  · funext x
    change ((r^d)⁻¹ : ℂ) * q (r⁻¹ • x) = a (r⁻¹ • x) * k x
    dsimp [q, f]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [Complex.ofReal_pow]
    have hrd : (r^d : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero d hr.ne'
    field_simp
  · intro ξ
    have h := hfourier ψ hψs D hD hψder r hr ξ
    have heq : testSchwartz ℂ φ =
        ((r^d)⁻¹ : ℂ) • testSchwartz ℂ (dilateTest r hr.ne' ψ) := by ext x; rfl
    rw [heq, map_smul]
    change (1 + r * ‖ξ‖)^L * ‖iteratedFDeriv ℝ n
      (((r^d)⁻¹ : ℂ) • (⇑(schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' ψ))))) ξ‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply
      ((schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' ψ))).smooth n).contDiffAt,
      norm_smul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
    calc
      (1 + r * ‖ξ‖)^L * ((r^d)⁻¹ *
          ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' ψ))) ξ‖) =
          (r^d)⁻¹ * ((1 + r * ‖ξ‖)^L *
          ‖iteratedFDeriv ℝ n (schwartzFourier (testSchwartz ℂ (dilateTest r hr.ne' ψ))) ξ‖) := by ring
      _ ≤ (r^d)⁻¹ * (C * D * r^(d+n)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = C * D * r^n := by rw [pow_add]; field_simp

/-- Exact amplitude-one dilation pairing for a finite coordinate polynomial. -/
theorem polynomial_pairing_dilate {d : ℕ} (s : Finset (List (Fin d)))
    (c : List (Fin d) → ℂ) (φ : Tests ℂ (⊤ : Opens (Domain d)))
    (r : ℝ) (hr : 0 < r) :
    (∫ x : Euclidean d, (∑ w ∈ s, c w * wordMonomial w x) *
      testSchwartz ℂ (dilateTest r hr.ne' φ) x) =
      (r ^ d : ℝ) • (∑ w ∈ s, (c w * (r : ℂ) ^ w.length) *
        ∫ x : Euclidean d, wordMonomial w x * testSchwartz ℂ φ x) := by
  classical
  let g : Euclidean d → ℂ := fun x =>
    (∑ w ∈ s, c w * wordMonomial w (r • x)) * testSchwartz ℂ φ x
  have heq (x : Euclidean d) :
      (∑ w ∈ s, c w * wordMonomial w x) *
        testSchwartz ℂ (dilateTest r hr.ne' φ) x = g (r⁻¹ • x) := by
    simp [g, testSchwartz_apply, dilateTest_apply, smul_smul, hr.ne', map_smul]
  simp_rw [heq]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume g hr.le,
    finrank_euclideanSpace_fin]
  congr 1
  simp only [g, wordMonomial_smul, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro w hw
    simp_rw [show ∀ x, c w * ((r : ℂ) ^ w.length * wordMonomial w x) *
      testSchwartz ℂ φ x = (c w * (r : ℂ) ^ w.length) *
        (wordMonomial w x * testSchwartz ℂ φ x) by intro x; ring]
    exact integral_const_mul _ _
  · intro w hw
    convert ((monomial_pairing d w (testSchwartz ℂ φ)).1.const_mul
      (c w * (r : ℂ) ^ w.length)) using 1
    ext x
    ring


/-- A cancellation estimate for normalized unit bumps controls dilations of
any fixed compact smooth test, with a constant depending on that test. -/
theorem bump_cancellation_fixed_test {d N : ℕ} (K : KernelDistribution d)
    (hK : BumpCancellation K N) (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (hr : 0 < r),
      ‖K (dilateTest r hr.ne' φ)‖ ≤ C := by
  have hc : HasCompactSupport (⇑(testSchwartz ℂ φ)) :=
    φ.hasCompactSupport.comp_homeomorph (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph
  obtain ⟨R, hR, hsR⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Euclidean d)
  let ψ := dilateTest R⁻¹ (inv_ne_zero hR.ne') φ
  have hψfun : ⇑(testSchwartz ℂ ψ) =
      (⇑(testSchwartz ℂ φ)) ∘ (Homeomorph.smulOfNeZero R hR.ne') := by
    funext x
    simp [ψ, testSchwartz_apply, dilateTest_apply, map_smul]
  have hsψ : tsupport (testSchwartz ℂ ψ) ⊆ Metric.closedBall 0 1 := by
    rw [hψfun, tsupport_comp_eq_preimage]
    intro x hx
    have hb := hsR hx
    simp only [Metric.mem_closedBall, dist_zero_right, Homeomorph.smulOfNeZero_apply,
      norm_smul, Real.norm_eq_abs, abs_of_pos hR] at hb ⊢
    nlinarith
  obtain ⟨C, hC, hb⟩ := bump_pairing_bound d N K hK
  let B := 1 + ∑ n ∈ Finset.range (N + 1), SchwartzMap.seminorm ℂ 0 n (testSchwartz ℂ ψ)
  have hsum : 0 ≤ ∑ n ∈ Finset.range (N + 1),
      SchwartzMap.seminorm ℂ 0 n (testSchwartz ℂ ψ) :=
    Finset.sum_nonneg fun n hn => apply_nonneg _ _
  have hB : 0 < B := by dsimp [B]; linarith
  have hder (n : ℕ) (hn : n ≤ N) (x : Euclidean d) :
      ‖iteratedFDeriv ℝ n (testSchwartz ℂ ψ) x‖ ≤ B := by
    apply (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (testSchwartz ℂ ψ) n x).trans
    apply le_trans (Finset.single_le_sum
      (fun j hj => apply_nonneg (SchwartzMap.seminorm ℂ 0 j) _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))
    dsimp [B]
    linarith
  refine ⟨C * B, mul_nonneg hC hB.le, ?_⟩
  intro r hr
  have heq : dilateTest r hr.ne' φ = dilateTest (r * R) (mul_pos hr hR).ne' ψ := by
    ext x
    simp [ψ, dilateTest_apply, smul_smul, hR.ne']
  rw [heq]
  exact hb ψ B hB hsψ hder (r * R) (mul_pos hr hR)


/-- A regular polynomial with uniform amplitude-one bump cancellation is
zero in positive dimension. This kills inverse Fourier transforms of
point-supported discrepancies without constructing a second physical kernel. -/
theorem polynomial_bump_cancellation_zero {d N : ℕ} (hd : 0 < d)
    (K : KernelDistribution d) (hK : BumpCancellation K N)
    (s : Finset (List (Fin d))) (c : List (Fin d) → ℂ)
    (hpoly : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      K φ = ∫ x : Euclidean d, (∑ w ∈ s, c w * wordMonomial w x) *
        testSchwartz ℂ φ x) : K = 0 := by
  classical
  ext φ
  obtain ⟨C, hC, hbound⟩ := bump_cancellation_fixed_test K hK φ
  let p : Polynomial ℂ := ∑ w ∈ s,
    Polynomial.C (c w * ∫ x : Euclidean d, wordMonomial w x * testSchwartz ℂ φ x) *
      Polynomial.X ^ w.length
  have hp (r : ℝ) : p.eval (r : ℂ) = ∑ w ∈ s,
      (c w * (r : ℂ) ^ w.length) *
        ∫ x : Euclidean d, wordMonomial w x * testSchwartz ℂ φ x := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    apply Finset.sum_congr rfl
    intro w hw
    ring
  have hpair (r : ℝ) (hr : 0 < r) :
      K (dilateTest r hr.ne' φ) = (r ^ d : ℝ) • p.eval (r : ℂ) := by
    rw [hpoly, polynomial_pairing_dilate s c φ r hr, hp]
  have hlim : Filter.Tendsto (fun r : ℝ => ‖p.eval (r : ℂ)‖)
      Filter.atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun r => norm_nonneg _))
      (g := fun r : ℝ => C * (r ^ d)⁻¹)
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
      have hb := hbound r hr
      rw [hpair r hr, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr d)] at hb
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hr d)]
      simpa [mul_comm] using hb
    · simpa using (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop hd.ne')) :
          Filter.Tendsto (fun r : ℝ => C * (r ^ d)⁻¹) Filter.atTop (𝓝 (C * 0)))
  have hpzero := polynomial_eq_zero_of_real_ray_limit p hlim
  have hdil : dilateTest 1 (by norm_num : (1 : ℝ) ≠ 0) φ = φ := by
    ext x
    simp [dilateTest_apply]
  have hz : p.eval (1 : ℂ) = 0 := by rw [hpzero, Polynomial.eval_zero]
  have hφ : K φ = 0 := by simpa [hz, hdil] using hpair 1 zero_lt_one
  exact hφ

/-- Singleton support on the original tests classifies the whole tempered
distribution, since compact tests determine every Schwartz pairing. -/
theorem point_supported_tempered {d : ℕ} (U : Tempered ℂ d)
    (hU : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      0 ∉ tsupport (testSchwartz ℂ φ) → U (testSchwartz ℂ φ) = 0) :
    ∃ (m : ℕ) (c : JetIndex d m → ℂ),
      U = ∑ i, c i • deltaDerivative (List.ofFn i.2).reverse := by
  obtain ⟨m,c,hc⟩ := point_supported_tempered_on_tests U hU
  exact ⟨m,c,tempered_ext_of_testSchwartz hc⟩

/-- Tempered extensions of a given original LF distribution are unique. -/
theorem ExtendsKernel.unique {d : ℕ} {K : KernelDistribution d}
    {U V : Tempered ℂ d} (hU : ExtendsKernel U K) (hV : ExtendsKernel V K) : U = V :=
  tempered_ext_of_testSchwartz (fun φ => (hU φ).trans (hV φ).symm)

/-- Increasing the finite normalization order preserves the bump bound. -/
theorem NormalizedBump.mono {d N M : ℕ}
    {φ : Tests ℂ (⊤ : Opens (Domain d))} (hφ : NormalizedBump M φ) (hNM : N ≤ M) :
    NormalizedBump N φ := ⟨hφ.1, fun n hn => hφ.2 n (hn.trans hNM)⟩

theorem BumpCancellation.mono {d N M : ℕ} {K : KernelDistribution d}
    (hK : BumpCancellation K N) (hNM : N ≤ M) : BumpCancellation K M := by
  obtain ⟨C,hC,hb⟩ := hK
  exact ⟨C,hC,fun φ hφ r hr => hb φ (hφ.mono hNM) r hr⟩

/-- Cancellation is stable under subtraction, allowing different input orders. -/
theorem BumpCancellation.sub {d N M : ℕ} {K L : KernelDistribution d}
    (hK : BumpCancellation K N) (hL : BumpCancellation L M) :
    BumpCancellation (K-L) (max N M) := by
  obtain ⟨C,hC,hKb⟩ := hK.mono (le_max_left N M)
  obtain ⟨D,hD,hLb⟩ := hL.mono (le_max_right N M)
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro φ hφ r hr
  exact (norm_sub_le _ _).trans (add_le_add (hKb φ hφ r hr) (hLb φ hφ r hr))

/-- Forgetting symbol derivative bounds retains global bounded Fourier representation. -/
theorem HasSmoothMultiplier.hasBoundedFourier {d : ℕ} {K : KernelDistribution d}
    (hK : HasSmoothMultiplier K) : HasBoundedFourier K := by
  obtain ⟨U,m,hU,hm,hrep,_⟩ := hK
  exact ⟨U,m,hU,hm,hrep⟩


/-- Explicit inverse transform of any finite combination of delta derivatives. -/
theorem fourier_inverse_delta_sum {d : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (w : ι → List (Fin d)) :
    temperedFourier (∑ i ∈ s,
      (c i * (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (w i).length) • monomialDistribution (w i)) =
        ∑ i ∈ s, c i • deltaDerivative (w i) := by
  classical
  have ha : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hc : -(2 * (Real.pi : ℂ) * Complex.I) *
      (-(2 * (Real.pi : ℂ) * Complex.I)⁻¹) = 1 := by
    rw [neg_mul_neg, mul_inv_cancel₀ ha]
  simp_rw [temperedFourier_sum, temperedFourier_smul, fourier_monomial, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc, ← mul_pow, hc, one_pow, mul_one]

/-- Exact amplitude-one dilation pairing for a finite coordinate polynomial. -/
theorem polynomial_pairing_dilate_indexed {d : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (w : ι → List (Fin d)) (φ : Tests ℂ (⊤ : Opens (Domain d)))
    (r : ℝ) (hr : 0 < r) :
    (∫ x : Euclidean d, (∑ i ∈ s, c i * wordMonomial (w i) x) *
      testSchwartz ℂ (dilateTest r hr.ne' φ) x) =
      (r ^ d : ℝ) • (∑ i ∈ s, (c i * (r : ℂ) ^ (w i).length) *
        ∫ x : Euclidean d, wordMonomial (w i) x * testSchwartz ℂ φ x) := by
  classical
  let g : Euclidean d → ℂ := fun x =>
    (∑ i ∈ s, c i * wordMonomial (w i) (r • x)) * testSchwartz ℂ φ x
  have heq (x : Euclidean d) :
      (∑ i ∈ s, c i * wordMonomial (w i) x) *
        testSchwartz ℂ (dilateTest r hr.ne' φ) x = g (r⁻¹ • x) := by
    simp [g, testSchwartz_apply, dilateTest_apply, smul_smul, hr.ne', map_smul]
  simp_rw [heq]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume g hr.le,
    finrank_euclideanSpace_fin]
  congr 1
  simp only [g, wordMonomial_smul, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hw
    simp_rw [show ∀ x, c i * ((r : ℂ) ^ (w i).length * wordMonomial (w i) x) *
      testSchwartz ℂ φ x = (c i * (r : ℂ) ^ (w i).length) *
        (wordMonomial (w i) x * testSchwartz ℂ φ x) by intro x; ring]
    exact integral_const_mul _ _
  · intro i hw
    convert ((monomial_pairing d (w i) (testSchwartz ℂ φ)).1.const_mul
      (c i * (r : ℂ) ^ (w i).length)) using 1
    ext x
    ring


/-- A regular polynomial with uniform amplitude-one bump cancellation is
zero in positive dimension. This kills inverse Fourier transforms of
point-supported discrepancies without constructing a second physical kernel. -/
theorem polynomial_bump_cancellation_zero_indexed {d N : ℕ} {ι : Type*} (hd : 0 < d)
    (K : KernelDistribution d) (hK : BumpCancellation K N)
    (s : Finset ι) (c : ι → ℂ) (w : ι → List (Fin d))
    (hpoly : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      K φ = ∫ x : Euclidean d, (∑ i ∈ s, c i * wordMonomial (w i) x) *
        testSchwartz ℂ φ x) : K = 0 := by
  classical
  ext φ
  obtain ⟨C, hC, hbound⟩ := bump_cancellation_fixed_test K hK φ
  let p : Polynomial ℂ := ∑ i ∈ s,
    Polynomial.C (c i * ∫ x : Euclidean d, wordMonomial (w i) x * testSchwartz ℂ φ x) *
      Polynomial.X ^ (w i).length
  have hp (r : ℝ) : p.eval (r : ℂ) = ∑ i ∈ s,
      (c i * (r : ℂ) ^ (w i).length) *
        ∫ x : Euclidean d, wordMonomial (w i) x * testSchwartz ℂ φ x := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    apply Finset.sum_congr rfl
    intro i hw
    ring
  have hpair (r : ℝ) (hr : 0 < r) :
      K (dilateTest r hr.ne' φ) = (r ^ d : ℝ) • p.eval (r : ℂ) := by
    rw [hpoly, polynomial_pairing_dilate_indexed s c w φ r hr, hp]
  have hlim : Filter.Tendsto (fun r : ℝ => ‖p.eval (r : ℂ)‖)
      Filter.atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun r => norm_nonneg _))
      (g := fun r : ℝ => C * (r ^ d)⁻¹)
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
      have hb := hbound r hr
      rw [hpair r hr, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr d)] at hb
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hr d)]
      simpa [mul_comm] using hb
    · simpa using (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop hd.ne')) :
          Filter.Tendsto (fun r : ℝ => C * (r ^ d)⁻¹) Filter.atTop (𝓝 (C * 0)))
  have hpzero := polynomial_eq_zero_of_real_ray_limit p hlim
  have hdil : dilateTest 1 (by norm_num : (1 : ℝ) ≠ 0) φ = φ := by
    ext x
    simp [dilateTest_apply]
  have hz : p.eval (1 : ℂ) = 0 := by rw [hpzero, Polynomial.eval_zero]
  have hφ : K φ = 0 := by simpa [hz, hdil] using hpair 1 zero_lt_one
  exact hφ



/-- A finite monomial distribution has exactly its regular polynomial pairing. -/
theorem finite_monomial_pairing {d : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (w : ι → List (Fin d)) (φ : Schwartz ℂ d) :
    (∑ i ∈ s, c i • monomialDistribution (w i)) φ =
      ∫ x : Euclidean d, (∑ i ∈ s, c i * wordMonomial (w i) x) * φ x := by
  classical
  simp only [sum_apply, smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [(monomial_pairing d (w i) φ).2]
    simp_rw [mul_assoc]
    exact (integral_const_mul _ _).symm
  · intro i hi
    simpa only [mul_assoc] using (monomial_pairing d (w i) φ).1.const_mul (c i)

/-- Cancellation removes every possible frequency-zero discrepancy. No
physical inverse-kernel construction is required for this step. -/
theorem fourier_representation_of_offZero_and_bumps {d N : ℕ} (hd : 0 < d)
    (K : KernelDistribution d) (U : Tempered ℂ d) (m : Euclidean d → ℂ)
    (hK : BumpCancellation K N) (hU : ExtendsKernel U K)
    (hm : BoundedFunction m) (hoff : FourierAgreesOffZero U m) :
    FourierRepresentedBy U m := by
  classical
  obtain ⟨M, hM, hMb⟩ := hm.2
  obtain ⟨B, hB⟩ := bounded_regular_tempered m hm.1 M hM hMb
  obtain ⟨e, he, heinv⟩ := Inversion.tempered_automorphism d
  let V : Tempered ℂ d := e.symm B
  have hVF : temperedFourier V = B := by rw [← he]; exact e.apply_symm_apply B
  have hVrep : FourierRepresentedBy V m := by
    intro φ
    simpa only [hVF] using hB φ
  let L : KernelDistribution d := temperedRestriction V
  have hL : HasBoundedFourier L := ⟨V, m, (fun _ => rfl), hm, hVrep⟩
  obtain ⟨N', hdN', hLb⟩ := bounded_to_bumps d L hL
  have hKb : BumpCancellation (K-L) (max N N') := hK.sub hLb
  let D : Tempered ℂ d := temperedFourier U - B
  have hD : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      0 ∉ tsupport (testSchwartz ℂ φ) → D (testSchwartz ℂ φ) = 0 := by
    intro φ hφ
    change temperedFourier U (testSchwartz ℂ φ) - B (testSchwartz ℂ φ) = 0
    rw [(hoff φ hφ).2, (hB (testSchwartz ℂ φ)).2, sub_self]
  obtain ⟨n,c,hc⟩ := point_supported_tempered D hD
  let w : JetIndex d n → List (Fin d) := fun i => (List.ofFn i.2).reverse
  let a : JetIndex d n → ℂ := fun i =>
    c i * (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (w i).length
  let P : Tempered ℂ d := ∑ i, a i • monomialDistribution (w i)
  have hPF : temperedFourier P = D := by
    rw [hc]
    exact fourier_inverse_delta_sum Finset.univ c w
  have hUV : U - V = P := by
    apply e.injective
    rw [he, he, hPF]
    ext φ
    change U (schwartzFourier φ) - V (schwartzFourier φ) =
      U (schwartzFourier φ) - B φ
    congr 1
    exact congrArg (fun T : Tempered ℂ d => T φ) hVF
  have hpoly : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      (K-L) φ = ∫ x : Euclidean d,
        (∑ i, a i * wordMonomial (w i) x) * testSchwartz ℂ φ x := by
    intro φ
    calc
      (K-L) φ = (U-V) (testSchwartz ℂ φ) := by
        change K φ - V (testSchwartz ℂ φ) = _
        rw [← hU φ]
        rfl
      _ = P (testSchwartz ℂ φ) := congrArg (fun T : Tempered ℂ d => T (testSchwartz ℂ φ)) hUV
      _ = _ := finite_monomial_pairing Finset.univ a w (testSchwartz ℂ φ)
  have hKL : K-L = 0 := polynomial_bump_cancellation_zero_indexed hd
    (K-L) hKb Finset.univ a w hpoly
  have hUVeq : U = V := ExtendsKernel.unique hU (by
    intro φ
    have h := congrArg (fun T : KernelDistribution d => T φ) hKL
    change K φ - V (testSchwartz ℂ φ) = 0 at h
    exact (sub_eq_zero.mp h).symm)
  simpa only [hUVeq] using hVrep


/-- On an open connected region, locally uniform summability of all derivatives
allows termwise differentiation to every order. -/
theorem iteratedFDeriv_tsum_on_open {d : ℕ}
    (f : ℕ → Euclidean d → ℂ) (s : Set (Euclidean d))
    (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, Summable (v n))
    (hb : ∀ n j x, x ∈ s → ‖iteratedFDeriv ℝ n (f j) x‖ ≤ v n j)
    (n : ℕ) : EqOn (iteratedFDeriv ℝ n (fun y => ∑' j, f j y))
      (fun x => ∑' j, iteratedFDeriv ℝ n (f j) x) s := by
  induction n with
  | zero =>
    intro x hx
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ (Euclidean d) ℂ).symm.toContinuousLinearEquiv.map_tsum
  | succ n IH =>
    intro x hx
    have heq : (iteratedFDeriv ℝ n (fun y => ∑' j, f j y)) =ᶠ[𝓝 x]
        (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact IH hy
    have hnorm (j : ℕ) (y : Euclidean d) (hy : y ∈ s) :
        ‖fderiv ℝ (iteratedFDeriv ℝ n (f j)) y‖ ≤ v (n+1) j := by
      rw [fderiv_iteratedFDeriv, comp_apply, LinearIsometryEquiv.norm_map]
      exact hb _ _ _ hy
    have hder (j : ℕ) (y : Euclidean d) (_hy : y ∈ s) :=
      ((hf j).differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n : (n : ℕ∞ω) < ∞) y).hasFDerivAt
    have hxsum : Summable (fun j => iteratedFDeriv ℝ n (f j) x) :=
      Summable.of_norm_bounded (hv n) (fun j => hb n j x hx)
    have h := hasFDerivAt_tsum_of_isPreconnected (hv (n+1)) hs hsc hder hnorm hx hxsum hx
    rw [iteratedFDeriv_succ_eq_comp_left, comp_apply, heq.fderiv_eq, h.fderiv]
    simp_rw [iteratedFDeriv_succ_eq_comp_left, comp_apply]
    exact (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (n+1) => Euclidean d) ℂ).symm.toContinuousLinearEquiv.map_tsum

/-- Local normal convergence of every derivative implies smoothness of the
outer dyadic Fourier series. -/
theorem contDiffOn_tsum_on_open {d : ℕ}
    (f : ℕ → Euclidean d → ℂ) (s : Set (Euclidean d))
    (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, Summable (v n))
    (hb : ∀ n j x, x ∈ s → ‖iteratedFDeriv ℝ n (f j) x‖ ≤ v n j) :
    ContDiffOn ℝ ∞ (fun y => ∑' j, f j y) s := by
  apply (contDiffOn_iff_continuousOn_differentiableOn hs.uniqueDiffOn).mpr
  have heq (n : ℕ) : EqOn
      (iteratedFDerivWithin ℝ n (fun y => ∑' j, f j y) s)
      (fun x => ∑' j, iteratedFDeriv ℝ n (f j) x) s := by
    intro x hx
    rw [iteratedFDerivWithin_of_isOpen n hs hx]
    exact iteratedFDeriv_tsum_on_open f s hs hsc hf v hv hb n hx
  constructor
  · intro n hn
    apply ContinuousOn.congr (continuousOn_tsum
      (fun j => ((hf j).continuous_iteratedFDeriv (by simp)).continuousOn) (hv n)
      (fun j x hx => hb n j x hx)) (heq n)
  · intro n hn x hx
    have hnorm (j : ℕ) (y : Euclidean d) (hy : y ∈ s) :
        ‖fderiv ℝ (iteratedFDeriv ℝ n (f j)) y‖ ≤ v (n+1) j := by
      rw [fderiv_iteratedFDeriv, comp_apply, LinearIsometryEquiv.norm_map]
      exact hb _ _ _ hy
    have hder (j : ℕ) (y : Euclidean d) (_hy : y ∈ s) :=
      ((hf j).differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n : (n : ℕ∞ω) < ∞) y).hasFDerivAt
    have hxsum : Summable (fun j => iteratedFDeriv ℝ n (f j) x) :=
      Summable.of_norm_bounded (hv n) (fun j => hb n j x hx)
    have h := hasFDerivAt_tsum_of_isPreconnected (hv (n+1)) hs hsc hder hnorm hx hxsum hx
    exact h.differentiableAt.differentiableWithinAt.congr (heq n) (heq n hx)

/-- At each frequency bounded away from zero, the outer dyadic annular
estimate with L=n+1 is controlled by a geometric sequence of ratio 1/2. -/
theorem dyadic_annular_majorant (n j : ℕ) (C R a u : ℝ)
    (hR : 0 < R) (ha : 0 < a) (hu : 0 ≤ u)
    (hbound : (1 + (R * 2^j) * a)^(n+1) * u ≤ C * (R * 2^j)^n) :
    u ≤ C * R⁻¹ * (a^(n+1))⁻¹ * (1/2 : ℝ)^j := by
  have hpow : ((R * 2^j) * a)^(n+1) ≤ (1 + (R * 2^j) * a)^(n+1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have h := (mul_le_mul_of_nonneg_right hpow hu).trans hbound
  apply (mul_le_mul_iff_of_pos_left (pow_pos (mul_pos (mul_pos hR (by positivity : (0 : ℝ) < 2^j)) ha) (n+1))).mp
  calc
    ((R * 2^j) * a)^(n+1) * u ≤ C * (R * 2^j)^n := h
    _ = ((R * 2^j) * a)^(n+1) *
        (C * R⁻¹ * (a^(n+1))⁻¹ * (1/2 : ℝ)^j) := by
      rw [show (1/2 : ℝ)^j = (2^j)⁻¹ by rw [one_div, inv_pow]]
      rw [mul_pow (R * 2^j) a (n+1), pow_succ (R * 2^j) n]
      field_simp

/-- The majorant supplied by the annular derivative estimate is summable. -/
theorem summable_dyadic_annular_majorant (n : ℕ) (C R a : ℝ) :
    Summable (fun j : ℕ => C * R⁻¹ * (a^(n+1))⁻¹ * (1/2 : ℝ)^j) := by
  exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_left _

/-- The outer-shell Fourier series converges smoothly on every open connected
frequency region a positive distance from zero. -/
theorem contDiffOn_outer_dyadic_series {d : ℕ}
    (f : ℕ → Euclidean d → ℂ) (s : Set (Euclidean d))
    (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (R a : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hregion : ∀ x ∈ s, a ≤ ‖x‖)
    (C : ℕ → ℝ)
    (hb : ∀ n j x, x ∈ s →
      (1 + (R * 2^j) * ‖x‖)^(n+1) * ‖iteratedFDeriv ℝ n (f j) x‖ ≤
        C n * (R * 2^j)^n) :
    ContDiffOn ℝ ∞ (fun y => ∑' j, f j y) s ∧
      ∀ n, EqOn (iteratedFDeriv ℝ n (fun y => ∑' j, f j y))
        (fun x => ∑' j, iteratedFDeriv ℝ n (f j) x) s := by
  let v : ℕ → ℕ → ℝ :=
    fun n j => C n * R⁻¹ * (a^(n+1))⁻¹ * (1/2 : ℝ)^j
  have hv (n : ℕ) : Summable (v n) := summable_dyadic_annular_majorant n (C n) R a
  have hmajorant (n j : ℕ) (x : Euclidean d) (hx : x ∈ s) :
      ‖iteratedFDeriv ℝ n (f j) x‖ ≤ v n j := by
    apply dyadic_annular_majorant n j (C n) R a _ hR ha (norm_nonneg _)
    calc
      (1 + R * 2^j * a)^(n+1) * ‖iteratedFDeriv ℝ n (f j) x‖ ≤
          (1 + R * 2^j * ‖x‖)^(n+1) * ‖iteratedFDeriv ℝ n (f j) x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply pow_le_pow_left₀ (by positivity)
        have h := mul_le_mul_of_nonneg_left (hregion x hx) (by positivity : (0 : ℝ) ≤ R*2^j)
        linarith
      _ ≤ C n * (R * 2^j)^n := hb n j x hx
  exact ⟨contDiffOn_tsum_on_open f s hs hsc hf v hv hmajorant,
    fun n => iteratedFDeriv_tsum_on_open f s hs hsc hf v hv hmajorant n⟩

/-- Summing the annular majorant gives the exact outer-series scale bound. -/
theorem norm_tsum_dyadic_annular_bound {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℕ → F) (n : ℕ) (C R a : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hb : ∀ j, (1 + (R * 2^j) * a)^(n+1) * ‖g j‖ ≤ C * (R * 2^j)^n) :
    ‖∑' j, g j‖ ≤ 2 * C * R⁻¹ * (a^(n+1))⁻¹ := by
  let v : ℕ → ℝ := fun j => C * R⁻¹ * (a^(n+1))⁻¹ * (1/2 : ℝ)^j
  have hv : Summable v := summable_dyadic_annular_majorant n C R a
  have hg (j : ℕ) : ‖g j‖ ≤ v j :=
    dyadic_annular_majorant n j C R a ‖g j‖ hR ha (norm_nonneg _) (hb j)
  have hnorm : Summable (fun j => ‖g j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hg hv
  calc
    ‖∑' j, g j‖ ≤ ∑' j, ‖g j‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j, v j := Summable.tsum_le_tsum hg hnorm hv
    _ = 2 * C * R⁻¹ * (a^(n+1))⁻¹ := by
      dsimp only [v]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)]
      norm_num
      ring
/-- The only analytic construction still needed for the forward implication
is a bounded symbol representing the Fourier transform away from zero. This
upgrade supplies global equality, including dimension zero. -/
theorem smooth_multiplier_of_offZero_symbol {d N : ℕ}
    (K : KernelDistribution d) (U : Tempered ℂ d) (m : Euclidean d → ℂ)
    (hK : BumpCancellation K N) (hU : ExtendsKernel U K)
    (hm : BoundedFunction m) (hoff : FourierAgreesOffZero U m) (hsym : SymbolBounds m) :
    HasSmoothMultiplier K := by
  by_cases hd : d = 0
  · subst d
    exact zero_dimension_multiplier K
  · exact ⟨U,m,hU,hm,
      fourier_representation_of_offZero_and_bumps (Nat.pos_of_ne_zero hd) K U m hK hU hm hoff,
      hsym⟩



/-- Restricting a smooth function on a product to the first factor does not
increase its derivative operator norms. This includes dimension zero. -/
theorem norm_spatial_iteratedFDeriv_le_joint {d : ℕ}
    (F : Euclidean d × Euclidean d → ℂ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (x t : Euclidean d) :
    ‖iteratedFDeriv ℝ n (fun y => F (y, t)) x‖ ≤
      ‖iteratedFDeriv ℝ n F (x, t)‖ := by
  let H : Euclidean d × Euclidean d → ℂ := fun p => F (p + (0, t))
  have hH : ContDiff ℝ ∞ H := hF.comp (contDiff_id.add contDiff_const)
  have h := (ContinuousLinearMap.inl ℝ (Euclidean d) (Euclidean d)).iteratedFDeriv_comp_right
    hH x (show (n : ℕ∞ω) ≤ ∞ by simp)
  have heq : iteratedFDeriv ℝ n (fun y => F (y, t)) x =
      (iteratedFDeriv ℝ n F (x, t)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ (Euclidean d) (Euclidean d)) := by
    simpa only [H, Function.comp_def, ContinuousLinearMap.inl_apply,
      Prod.mk_add_mk, add_zero, zero_add, iteratedFDeriv_comp_add_right] using h
  rw [heq]
  exact ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _
    (fun _ => LinearIsometry.inl ℝ (Euclidean d) (Euclidean d))

/-- Coordinate monomials are smooth, including the empty word. -/
theorem contDiff_wordMonomial {d : ℕ} (w : List (Fin d)) :
    ContDiff ℝ ∞ (wordMonomial w) := by
  induction w with
  | nil => exact contDiff_const
  | cons i w ih =>
    exact (Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj i).contDiff).mul ih

/-- Joint smoothness in physical and frequency variables. -/
theorem contDiff_inner_bump_joint {d : ℕ} (a : Euclidean d → ℂ)
    (ha : ContDiff ℝ ∞ a) (w : List (Fin d)) :
    ContDiff ℝ ∞ (fun p : Euclidean d × Euclidean d =>
      a p.1 * wordMonomial w p.1 *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ p.1 p.2 : ℝ))) := by
  have hp : ContDiff ℝ ∞ (fun p : Euclidean d × Euclidean d =>
      (inner ℝ p.1 p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_fst.inner ℝ contDiff_snd)
  exact ((ha.comp contDiff_fst).mul ((contDiff_wordMonomial w).comp contDiff_fst)).mul
    (contDiff_const.mul hp).cexp


/-- An oscillatory compact amplitude has derivative bounds uniform on a compact
frequency ball, with one constant for all spatial derivatives up to N. -/
theorem inner_bump_uniform_derivative_bound {d : ℕ} (a : Euclidean d → ℂ)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (w : List (Fin d)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : Euclidean d), ‖t‖ ≤ 2 → ∀ (n : ℕ), n ≤ N →
      ∀ x : Euclidean d,
      ‖iteratedFDeriv ℝ n (fun y => a y * wordMonomial w y *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ y t : ℝ))) x‖ ≤ C := by
  classical
  let F : Euclidean d × Euclidean d → ℂ := fun p =>
    a p.1 * wordMonomial w p.1 *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ p.1 p.2 : ℝ))
  have hF : ContDiff ℝ ∞ F := contDiff_inner_bump_joint a ha w
  have hsupp (t : Euclidean d) : tsupport (fun y => F (y, t)) ⊆ tsupport a := by
    change tsupport ((a * wordMonomial w) *
      (fun y => Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ y t : ℝ)))) ⊆ _
    exact tsupport_mul_subset_left.trans tsupport_mul_subset_left
  have key (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Euclidean d, ‖t‖ ≤ 2 →
      ∀ x : Euclidean d, ‖iteratedFDeriv ℝ n (fun y => F (y, t)) x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hac.prod (isCompact_closedBall (0 : Euclidean d) 2)).exists_bound_of_continuousOn
      (hF.continuous_iteratedFDeriv (show (n : ℕ∞ω) ≤ ∞ by simp)).continuousOn
    refine ⟨max 0 C, le_max_left _ _, ?_⟩
    intro t ht x
    by_cases hx : x ∈ tsupport a
    · exact (norm_spatial_iteratedFDeriv_le_joint F hF n x t).trans
        ((hC (x, t) ⟨hx, by simpa using ht⟩).trans (le_max_right _ _))
    · have hz : iteratedFDeriv ℝ n (fun y => F (y, t)) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp t (tsupport_iteratedFDeriv_subset n h)))
      simp [hz]
  choose C hC hb using key
  refine ⟨∑ n ∈ Finset.range (N + 1), C n,
    Finset.sum_nonneg (fun n _ => hC n), ?_⟩
  intro t ht n hn x
  exact (hb n t ht x).trans
    (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

/-- The same functions retain the original amplitude's compact support. -/
theorem inner_bump_hasCompactSupport {d : ℕ} (a : Euclidean d → ℂ)
    (hac : HasCompactSupport a) (w : List (Fin d)) (t : Euclidean d) :
    HasCompactSupport (fun y => a y * wordMonomial w y *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ y t : ℝ))) := by
  exact (hac.mul_right).mul_right

/-- The support needed for normalized bumps is unchanged by monomials or oscillation. -/
theorem inner_bump_tsupport_subset {d : ℕ} (a : Euclidean d → ℂ)
    (w : List (Fin d)) (t : Euclidean d) :
    tsupport (fun y => a y * wordMonomial w y *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ y t : ℝ))) ⊆ tsupport a := by
  exact tsupport_mul_subset_left.trans tsupport_mul_subset_left


/-- The original LF test represented by an oscillatory compact amplitude. -/
def innerOscillatoryTest {d : ℕ} (a : Euclidean d → ℂ)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (w : List (Fin d)) (t : Euclidean d) : Tests ℂ (⊤ : Opens (Domain d)) := by
  let f : Euclidean d → ℂ := fun y => a y * wordMonomial w y *
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ y t : ℝ))
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_inner_bump_joint a ha w).comp (contDiff_id.prodMk contDiff_const)
  let e := EuclideanSpace.equiv (Fin d) ℝ
  exact ⟨fun x => f (e.symm x), hf.comp e.symm.contDiff,
    (inner_bump_hasCompactSupport a hac w t).comp_homeomorph e.symm.toHomeomorph,
    subset_univ _⟩

@[simp] theorem testSchwartz_innerOscillatoryTest {d : ℕ} (a : Euclidean d → ℂ)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (w : List (Fin d)) (t : Euclidean d) :
    ⇑(testSchwartz ℂ (innerOscillatoryTest a ha hac w t)) =
      fun y => a y * wordMonomial w y *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ y t : ℝ)) := by
  funext y
  change a ((EuclideanSpace.equiv (Fin d) ℝ).symm ((EuclideanSpace.equiv (Fin d) ℝ) y)) *
    wordMonomial w ((EuclideanSpace.equiv (Fin d) ℝ).symm ((EuclideanSpace.equiv (Fin d) ℝ) y)) *
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm ((EuclideanSpace.equiv (Fin d) ℝ) y)) t : ℝ)) = _
  simp

/-- A single positive C^N bound works for all actual unit-support oscillatory LF tests. -/
theorem inner_oscillatory_tests_bounded {d : ℕ} (a : Euclidean d → ℂ)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (has : tsupport a ⊆ Metric.closedBall 0 1) (w : List (Fin d)) (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : Euclidean d, ‖t‖ ≤ 2 →
      tsupport (testSchwartz ℂ (innerOscillatoryTest a ha hac w t)) ⊆ Metric.closedBall 0 1 ∧
      ∀ n ≤ N, ∀ x : Euclidean d,
        ‖iteratedFDeriv ℝ n (testSchwartz ℂ (innerOscillatoryTest a ha hac w t)) x‖ ≤ B := by
  obtain ⟨C, hC, hb⟩ := inner_bump_uniform_derivative_bound a ha hac w N
  refine ⟨C + 1, by positivity, ?_⟩
  intro t ht
  rw [testSchwartz_innerOscillatoryTest]
  exact ⟨(inner_bump_tsupport_subset a w t).trans has,
    fun n hn x => (hb t ht n hn x).trans (by linarith)⟩


/-- Bump cancellation bounds these compact oscillatory pairings uniformly on
scaled frequencies of norm at most two. No frequency differentiation is asserted. -/
theorem inner_oscillatory_pairing_bound {d N : ℕ} (K : KernelDistribution d)
    (hK : BumpCancellation K N) (a : Euclidean d → ℂ)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (has : tsupport a ⊆ Metric.closedBall 0 1) (w : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (hr : 0 < r) (ξ : Euclidean d), ‖r • ξ‖ ≤ 2 →
      ‖K (dilateTest r hr.ne' (innerOscillatoryTest a ha hac w (r • ξ)))‖ ≤ C := by
  obtain ⟨A, hA, hpair⟩ := bump_pairing_bound d N K hK
  obtain ⟨B, hB, hb⟩ := inner_oscillatory_tests_bounded a ha hac has w N
  refine ⟨A * B, mul_nonneg hA hB.le, ?_⟩
  intro r hr ξ hξ
  exact hpair (innerOscillatoryTest a ha hac w (r • ξ)) B hB
    (hb (r • ξ) hξ).1 (hb (r • ξ) hξ).2 r hr

/-- The degree factor supplies the expected power of the spatial scale for the
same scalar pairings, without identifying them with derivatives. -/
theorem inner_oscillatory_pairing_bound_weighted {d N : ℕ} (K : KernelDistribution d)
    (hK : BumpCancellation K N) (a : Euclidean d → ℂ)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (has : tsupport a ⊆ Metric.closedBall 0 1) (w : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (hr : 0 < r) (ξ : Euclidean d), ‖r • ξ‖ ≤ 2 →
      ‖(r ^ w.length : ℝ) •
        K (dilateTest r hr.ne' (innerOscillatoryTest a ha hac w (r • ξ)))‖ ≤
        C * r ^ w.length := by
  obtain ⟨C, hC, hb⟩ := inner_oscillatory_pairing_bound K hK a ha hac has w
  refine ⟨C, hC, ?_⟩
  intro r hr ξ hξ
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _)]
  exact (mul_le_mul_of_nonneg_left (hb r hr ξ hξ) (pow_nonneg hr.le _)).trans_eq (mul_comm _ _)


/-- A scalar functional controlled by a normed linear observation factors
through a bounded functional on the whole observation space. -/
theorem exists_clm_factor_of_norm_bound {E F : Type*}
    [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (J : E →ₗ[ℂ] F) (L : E →ₗ[ℂ] ℂ) (C : ℝ)
    (h : ∀ x, ‖L x‖ ≤ C * ‖J x‖) :
    ∃ A : F →L[ℂ] ℂ, ∀ x, A (J x) = L x := by
  let Q := J.rangeRestrict
  have hker : LinearMap.ker Q ≤ LinearMap.ker L := by
    intro x hx
    have hx' : J x = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [hx', norm_zero, mul_zero] using h x
  let l : J.range →ₗ[ℂ] ℂ := Q.liftOfSurjective J.surjective_rangeRestrict ⟨L, hker⟩
  have hl (x : E) : l (Q x) = L x := LinearMap.equivOfSurjective_apply _ _
  have hb (y : J.range) : ‖l y‖ ≤ C * ‖y‖ := by
    obtain ⟨x, rfl⟩ := J.surjective_rangeRestrict y
    rw [hl]
    exact h x
  let lc : J.range →L[ℂ] ℂ := l.mkContinuous C hb
  obtain ⟨A,hA,hAnorm⟩ := exists_extension_norm_eq J.range lc
  refine ⟨A, fun x => ?_⟩
  exact (hA (Q x)).trans (hl x)

/-- Finite Banach jet space on a fixed compact set. -/
abbrev CompactJetSpace {d : ℕ} (K : Compacts (Domain d)) (N : ℕ) :=
  (n : Fin (N + 1)) → C(K, (Domain d) [×n.val]→L[ℝ] ℂ)

/-- Record each derivative through order N on the compact support set. -/
def compactStepJet {d : ℕ} (K : Compacts (Domain d)) (N : ℕ) :
    Step ℂ K →ₗ[ℂ] CompactJetSpace K N where
  toFun φ n := ⟨fun x => iteratedFDeriv ℝ n.val φ x,
    (φ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast
      (show (n.val : ℕ∞) ≤ ⊤ from le_top))).comp continuous_subtype_val⟩
  map_add' φ ψ := by
    funext n
    apply ContinuousMap.ext
    intro x
    exact iteratedFDeriv_add_apply (φ.contDiff.contDiffAt.of_le (by simp))
      (ψ.contDiff.contDiffAt.of_le (by simp))
  map_smul' c φ := by
    funext n
    apply ContinuousMap.ext
    intro x
    exact iteratedFDeriv_const_smul_apply (φ.contDiff.contDiffAt.of_le (by simp))

/-- The finite jet norm controls the accepted coordinate derivative seminorm. -/
theorem stepSeminorm_le_compactStepJet_norm {d : ℕ}
    (K : Compacts (Domain d)) (N : ℕ) (φ : Step ℂ K) :
    stepSeminorm ℂ K N φ ≤ ‖compactStepJet K N φ‖ := by
  apply (step_seminorm_formula ℂ d K N φ _ (norm_nonneg _)).mpr
  intro n hn w x
  have hop : ‖iteratedFDeriv ℝ n φ x‖ ≤ ‖compactStepJet K N φ‖ := by
    by_cases hx : x ∈ K
    · apply (ContinuousMap.norm_coe_le_norm
        (compactStepJet K N φ ⟨n, Nat.lt_succ_of_le hn⟩) ⟨x,hx⟩).trans
      exact norm_le_pi_norm (compactStepJet K N φ) _
    · have hz : iteratedFDeriv ℝ n φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ht => hx (φ.tsupport_subset
          (tsupport_iteratedFDeriv_subset n ht)))
      rw [hz, norm_zero]
      exact norm_nonneg _
  calc
    _ ≤ ‖iteratedFDeriv ℝ n φ x‖ * ∏ j, ‖coordinateVector (w j)‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ n φ x‖ := by simp [coordinateVector, Pi.norm_single]
    _ ≤ _ := hop

/-- Every LF distribution restricted to a fixed compact step factors through
some finite Banach jet space, with no assumed certificate. -/
theorem distribution_factors_compact_jet {d : ℕ}
    (u : KernelDistribution d) (K : Compacts (Domain d)) :
    ∃ N : ℕ, ∃ A : CompactJetSpace K N →L[ℂ] ℂ,
      ∀ φ : Step ℂ K,
        A (compactStepJet K N φ) = u (TestFunction.ofSupportedIn (subset_univ (K : Set (Domain d))) φ) := by
  obtain ⟨C,hC,N,hb⟩ := (finite_order_criterion ℂ d ⊤ u.toLinearMap).mp u.continuous
    K (subset_univ (K : Set (Domain d)))
  let L : Step ℂ K →ₗ[ℂ] ℂ := u.toLinearMap.comp
    (TestFunction.ofSupportedInCLM ℂ (subset_univ (K : Set (Domain d)))).toLinearMap
  have hbound : ∀ φ : Step ℂ K, ‖L φ‖ ≤ C * ‖compactStepJet K N φ‖ := by
    intro φ
    exact (hb φ).trans (mul_le_mul_of_nonneg_left
      (stepSeminorm_le_compactStepJet_norm K N φ) hC)
  obtain ⟨A,hA⟩ := exists_clm_factor_of_norm_bound (E := Step ℂ K) (F := CompactJetSpace K N)
    (compactStepJet K N) L C hbound
  exact ⟨N,A,hA⟩


/-- The Banach algebra exponential of continuous functions is pointwise. -/
theorem continuousMap_exp_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : C(X,ℂ)) (x : X) : (NormedSpace.exp f) x = Complex.exp (f x) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x)
    (ContinuousMap.evalCLM ℂ x).continuous f
  simpa only [ContinuousMap.evalAlgHom_apply, Complex.exp_eq_exp_ℂ] using h

/-- Applying a continuous linear scalar functional after a Banach algebra
exponential gives a smooth scalar parameter function. -/
theorem contDiff_continuousMap_exp {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] C(X,ℂ)) :
    ContDiff ℝ ∞ (fun ξ => NormedSpace.exp (L ξ)) := by
  have h : AnalyticOnNhd ℝ (NormedSpace.exp : C(X,ℂ) → C(X,ℂ)) Set.univ :=
    fun f _ => NormedSpace.exp_analytic f
  exact h.contDiff.comp L.contDiff

/-- The Fourier phase on a compact family of physical points is a bounded
real-linear map into the Banach algebra of continuous complex functions. -/
def compactFourierPhase {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (v : C(X, Euclidean d)) : Euclidean d →L[ℝ] C(X,ℂ) := by
  let a : ℂ := -2 * (Real.pi : ℂ) * Complex.I
  let L : Euclidean d →ₗ[ℝ] C(X,ℂ) :=
    { toFun ξ := ⟨fun x => a * (inner ℝ (v x) ξ : ℝ), by fun_prop⟩
      map_add' ξ η := by
        ext x
        change a * (inner ℝ (v x) (ξ+η) : ℝ) =
          a * (inner ℝ (v x) ξ : ℝ) + a * (inner ℝ (v x) η : ℝ)
        simp only [inner_add_right, Complex.ofReal_add, mul_add]
      map_smul' c ξ := by
        ext x
        change a * (inner ℝ (v x) (c • ξ) : ℝ) =
          c • (a * (inner ℝ (v x) ξ : ℝ))
        simp only [real_inner_smul_right, Complex.ofReal_mul, Complex.real_smul]
        ring }
  refine L.mkContinuous (‖a‖ * ‖v‖) ?_
  intro ξ
  apply (ContinuousMap.norm_le (L ξ) (by positivity)).mpr
  intro x
  change ‖a * (inner ℝ (v x) ξ : ℝ)‖ ≤ _
  rw [norm_mul, Complex.norm_real]
  calc
    ‖a‖ * ‖inner ℝ (v x) ξ‖ ≤ ‖a‖ * (‖v x‖ * ‖ξ‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
    _ ≤ ‖a‖ * (‖v‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm v x) (norm_nonneg _))
      (norm_nonneg _)
    _ = _ := by ring

@[simp] theorem compactFourierPhase_apply {d : ℕ} {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (v : C(X, Euclidean d))
    (ξ : Euclidean d) (x : X) :
    compactFourierPhase v ξ x = -2 * (Real.pi : ℂ) * Complex.I *
      (inner ℝ (v x) ξ : ℝ) := rfl

/-- Compact Fourier exponentials form an actual smooth map into a Banach
space, with the exact manuscript Fourier phase at every physical point. -/
theorem compact_fourier_exponential {d : ℕ} {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (v : C(X, Euclidean d)) :
    ContDiff ℝ ∞ (fun ξ => NormedSpace.exp (compactFourierPhase v ξ)) ∧
      ∀ (ξ : Euclidean d) (x : X),
        (NormedSpace.exp (compactFourierPhase v ξ)) x =
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ (v x) ξ : ℝ)) := by
  exact ⟨contDiff_continuousMap_exp _, fun ξ x => continuousMap_exp_apply _ _⟩


def dyadicCutoffBump (d : ℕ) : ContDiffBump (0 : Euclidean d) :=
  ⟨1/2, 1, by norm_num, by norm_num⟩

def dyadicCutoff (d : ℕ) : Euclidean d → ℂ := fun x => (dyadicCutoffBump d x : ℂ)

def dyadicAnnularCutoff (d : ℕ) : Euclidean d → ℂ :=
  fun x => dyadicCutoff d x - dyadicCutoff d ((2 : ℝ) • x)

lemma dyadicCutoff_smooth (d : ℕ) : ContDiff ℝ ∞ (dyadicCutoff d) :=
  Complex.ofRealCLM.contDiff.comp (dyadicCutoffBump d).contDiff

lemma dyadicAnnularCutoff_smooth (d : ℕ) : ContDiff ℝ ∞ (dyadicAnnularCutoff d) :=
  (dyadicCutoff_smooth d).sub ((dyadicCutoff_smooth d).comp (contDiff_id.const_smul 2))

lemma dyadicCutoff_compact (d : ℕ) : HasCompactSupport (dyadicCutoff d) :=
  (dyadicCutoffBump d).hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

lemma dyadicAnnularCutoff_compact (d : ℕ) : HasCompactSupport (dyadicAnnularCutoff d) :=
  (dyadicCutoff_compact d).sub ((dyadicCutoff_compact d).comp_homeomorph
    (Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num)))

lemma dyadicCutoff_one (d : ℕ) {x : Euclidean d} (hx : ‖x‖ ≤ 1/2) :
    dyadicCutoff d x = 1 := by
  have h := (dyadicCutoffBump d).one_of_mem_closedBall (by simpa [dyadicCutoffBump] using hx)
  simp [dyadicCutoff, h]

lemma dyadicCutoff_zero (d : ℕ) {x : Euclidean d} (hx : 1 ≤ ‖x‖) :
    dyadicCutoff d x = 0 := by
  have h := (dyadicCutoffBump d).zero_of_le_dist (by simpa [dyadicCutoffBump] using hx)
  simp [dyadicCutoff, h]

lemma dyadicAnnularCutoff_support (d : ℕ) :
    tsupport (dyadicAnnularCutoff d) ⊆ Metric.closedBall 0 1 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra h
  have hnorm : 1 < ‖x‖ := by simpa using h
  have hnorm2 : 1 ≤ ‖(2 : ℝ) • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have he : dyadicAnnularCutoff d x = 0 := by
    rw [dyadicAnnularCutoff, dyadicCutoff_zero d hnorm.le, dyadicCutoff_zero d hnorm2]
    simp
  exact hx he

lemma dyadicAnnularCutoff_inner (d : ℕ) :
    ∀ x ∈ tsupport (dyadicAnnularCutoff d), (1/4 : ℝ) ≤ ‖x‖ := by
  have hs : tsupport (dyadicAnnularCutoff d) ⊆ {x | (1/4 : ℝ) ≤ ‖x‖} := by
    apply closure_minimal _ (isClosed_le continuous_const continuous_norm)
    intro x hx
    by_contra h
    change ¬ (1/4 : ℝ) ≤ ‖x‖ at h
    have hnorm : ‖x‖ ≤ 1/2 := by linarith
    have hnorm2 : ‖(2 : ℝ) • x‖ ≤ 1/2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have he : dyadicAnnularCutoff d x = 0 := by
      rw [dyadicAnnularCutoff, dyadicCutoff_one d hnorm, dyadicCutoff_one d hnorm2]
      simp
    exact hx he
  exact fun x hx => hs hx


/-- Consecutive dyadic annular cutoffs telescope to the large-radius cutoff. -/
theorem dyadicAnnularCutoff_telescope {d : ℕ} (R : ℝ) (hR : 0 < R)
    (J : ℕ) (x : Euclidean d) :
    dyadicCutoff d (R⁻¹ • x) +
      ∑ j ∈ Finset.range J,
        dyadicAnnularCutoff d ((R * 2^(j+1))⁻¹ • x) =
      dyadicCutoff d ((R * 2^J)⁻¹ • x) := by
  have ht (j : ℕ) : dyadicAnnularCutoff d ((R * 2^(j+1))⁻¹ • x) =
      dyadicCutoff d ((R * 2^(j+1))⁻¹ • x) -
        dyadicCutoff d ((R * 2^j)⁻¹ • x) := by
    dsimp only [dyadicAnnularCutoff]
    rw [smul_smul]
    congr 2
    congr 1
    rw [pow_succ]
    field_simp
  simp_rw [ht]
  rw [Finset.sum_range_sub (fun j => dyadicCutoff d ((R * 2^j)⁻¹ • x)) J]
  simp

/-- At sufficiently large dyadic radius, the cutoff is identically one on
any prescribed compact spatial set, uniformly at all later radii. -/
theorem dyadicCutoff_eventually_one_on_compact {d : ℕ}
    (R : ℝ) (hR : 0 < R) (S : Set (Euclidean d)) (hS : IsCompact S) :
    ∃ J : ℕ, ∀ J' ≥ J, ∀ x ∈ S, dyadicCutoff d ((R * 2^J')⁻¹ • x) = 1 := by
  obtain ⟨M, hM, hbound⟩ := hS.isBounded.exists_pos_norm_le
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (2*M/R) (by norm_num : (1 : ℝ) < 2)
  have hbig : 2*M ≤ R * 2^J := by
    have h := (div_lt_iff₀ hR).mp hJ
    linarith
  refine ⟨J, ?_⟩
  intro J' hJJ' x hx
  apply dyadicCutoff_one d
  have hpow : (2 : ℝ)^J ≤ 2^J' := pow_le_pow_right₀ (by norm_num) hJJ'
  have hbig' : 2*M ≤ R * 2^J' :=
    hbig.trans (mul_le_mul_of_nonneg_left hpow hR.le)
  have hscale : 0 < R * (2 : ℝ)^J' := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale)]
  apply (inv_mul_le_iff₀ hscale).mpr
  have h := hbound x hx
  linarith


set_option maxHeartbeats 1000000

theorem contDiff_spatial_fderiv {d e : ℕ}
    (F : Domain d × Euclidean e → ℂ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : Domain d × Euclidean e =>
      fderiv ℝ (fun x => F (x,p.2)) p.1) := by
  have h : ContDiff ℝ ∞ (fun p : (Domain d × Euclidean e) × Domain d =>
      F (p.2,p.1.2)) := hF.comp (contDiff_snd.prodMk contDiff_fst.snd)
  exact h.fderiv contDiff_fst (by simp)

/-- A jointly smooth integrand supported in a fixed compact set in the
integration variable permits differentiation of its integral. -/
theorem hasFDerivAt_integral_compact_parameter {d e : ℕ}
    (F : Domain d × Euclidean e → ℂ) (hF : ContDiff ℝ ∞ F)
    (S : Set (Euclidean e)) (hS : IsCompact S)
    (hsupp : ∀ x ξ, ξ ∉ S → F (x,ξ) = 0) (x₀ : Domain d) :
    HasFDerivAt (fun x => ∫ ξ, F (x,ξ))
      (∫ ξ, fderiv ℝ (fun x => F (x,ξ)) x₀) x₀ := by
  let D : Domain d × Euclidean e → Domain d →L[ℝ] ℂ :=
    fun p => fderiv ℝ (fun x => F (x,p.2)) p.1
  have hD : Continuous D := (contDiff_spatial_fderiv F hF).continuous
  have hDz (x : Domain d) (ξ : Euclidean e) (hξ : ξ ∉ S) : D (x,ξ) = 0 := by
    have hz : (fun x => F (x,ξ)) = fun _ => (0 : ℂ) := funext fun x => hsupp x ξ hξ
    simp [D, hz]
  have hFc (x : Domain d) : HasCompactSupport (fun ξ => F (x,ξ)) := by
    apply HasCompactSupport.intro hS
    intro ξ hξ
    exact hsupp x ξ hξ
  have hDc (x : Domain d) : HasCompactSupport (fun ξ => D (x,ξ)) := by
    apply HasCompactSupport.intro hS
    intro ξ hξ
    exact hDz x ξ hξ
  have hFi (x : Domain d) : Integrable (fun ξ => F (x,ξ)) :=
    (hF.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport (hFc x)
  have hDi (x : Domain d) : Integrable (fun ξ => D (x,ξ)) :=
    (hD.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport (hDc x)
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x₀ 1).prod hS).exists_bound_of_continuousOn hD.continuousOn
  let b : Euclidean e → ℝ := S.indicator (fun _ => max 0 C)
  have hbi : Integrable b := by
    rw [integrable_indicator_iff hS.measurableSet]
    exact integrableOn_const (hS.measure_lt_top.ne) (by simp)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun x ξ => D (x,ξ))
    (Metric.ball_mem_nhds x₀ zero_lt_one)
    (Filter.Eventually.of_forall fun x => (hFi x).aestronglyMeasurable)
    (hFi x₀) (hDi x₀).aestronglyMeasurable
    (Filter.Eventually.of_forall ?_) hbi ?_
  · intro ξ x hx
    by_cases hξ : ξ ∈ S
    · change ‖D (x,ξ)‖ ≤ _
      rw [show b ξ = max 0 C from indicator_of_mem hξ _]
      exact (hC (x,ξ) ⟨Metric.ball_subset_closedBall hx,hξ⟩).trans (le_max_right _ _)
    · simp [b,hξ,hDz x ξ hξ]
  · exact Filter.Eventually.of_forall fun ξ x _ =>
      ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x).hasFDerivAt


/-- Spatial coordinate derivatives of a smooth joint family remain smooth. -/
theorem contDiff_spatial_partialFunction {d e : ℕ}
    (F : Domain d × Euclidean e → ℂ) (hF : ContDiff ℝ ∞ F)
    (w : List (Fin d)) :
    ContDiff ℝ ∞ (fun p : Domain d × Euclidean e =>
      partialFunction w (fun x => F (x,p.2)) p.1) := by
  induction w with
  | nil => simpa [partialFunction] using hF
  | cons i w ih =>
    exact (contDiff_spatial_fderiv _ ih).clm_apply contDiff_const

@[simp] theorem partialFunction_zero {d : ℕ} (w : List (Fin d)) :
    partialFunction w (fun _ : Domain d => (0 : ℂ)) = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih => funext x; simp [partialFunction,ih]

/-- Every coordinate spatial derivative can be passed through an integral
whose frequency support is uniformly compact. -/
theorem partialFunction_integral_compact_parameter {d e : ℕ}
    (F : Domain d × Euclidean e → ℂ) (hF : ContDiff ℝ ∞ F)
    (S : Set (Euclidean e)) (hS : IsCompact S)
    (hsupp : ∀ x ξ, ξ ∉ S → F (x,ξ) = 0) (w : List (Fin d)) :
    partialFunction w (fun x => ∫ ξ, F (x,ξ)) =
      fun x => ∫ ξ, partialFunction w (fun y => F (y,ξ)) x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    change fderiv ℝ (partialFunction w (fun x => ∫ ξ, F (x,ξ))) x
      (coordinateVector i) = _
    rw [ih]
    let G : Domain d × Euclidean e → ℂ :=
      fun p => partialFunction w (fun y => F (y,p.2)) p.1
    have hG := contDiff_spatial_partialFunction F hF w
    have hsG (y : Domain d) (ξ : Euclidean e) (hξ : ξ ∉ S) : G (y,ξ) = 0 := by
      have hz : (fun y => F (y,ξ)) = fun _ => (0 : ℂ) := funext fun y => hsupp y ξ hξ
      simp [G,hz]
    rw [(hasFDerivAt_integral_compact_parameter G hG S hS hsG x).fderiv]
    have hD : Continuous (fun ξ => fderiv ℝ (fun y => G (y,ξ)) x) :=
      (contDiff_spatial_fderiv G hG).continuous.comp (continuous_const.prodMk continuous_id)
    have hDc : HasCompactSupport (fun ξ => fderiv ℝ (fun y => G (y,ξ)) x) := by
      apply HasCompactSupport.intro hS
      intro ξ hξ
      have hz : (fun y => G (y,ξ)) = fun _ => (0 : ℂ) := funext fun y => hsG y ξ hξ
      simp [hz]
    exact ContinuousLinearMap.integral_apply (hD.integrable_of_hasCompactSupport hDc) _

lemma partialFunction_smooth {d : ℕ} (w : List (Fin d))
    (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (partialFunction w a) := by
  induction w with
  | nil => exact ha
  | cons i w ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

lemma partialFunction_append {d : ℕ} (w v : List (Fin d)) (a : Domain d → ℂ) :
    partialFunction (w ++ v) a = partialFunction w (partialFunction v a) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append, partialFunction, ih]

lemma partialFunction_add {d : ℕ} (w : List (Fin d))
    (a b : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    partialFunction w (a + b) = partialFunction w a + partialFunction w b := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    simp only [partialFunction, ih]
    rw [fderiv_add ((partialFunction_smooth w a ha).differentiable (by simp) x)
      ((partialFunction_smooth w b hb).differentiable (by simp) x)]
    rfl

lemma partialFunction_const_mul {d : ℕ} (w : List (Fin d))
    (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) (c : ℂ) :
    partialFunction w (fun x => c * a x) = fun x => c * partialFunction w a x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    simp only [partialFunction, ih]
    rw [fderiv_const_mul ((partialFunction_smooth w a ha).differentiable (by simp) x)]
    rfl

def domainFourierPhase {d : ℕ} (ξ : Euclidean d) : Domain d →L[ℝ] ℂ :=
  (-2 * (Real.pi : ℂ) * Complex.I) •
    (Complex.ofRealCLM.comp (((innerSL ℝ).flip ξ).comp
      (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap))

lemma domainFourierPhase_apply {d : ℕ} (ξ : Euclidean d) (x : Domain d) :
    domainFourierPhase ξ x = -2 * (Real.pi : ℂ) * Complex.I *
      (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) ξ : ℝ) := by
  rfl

lemma domainFourierPhase_coordinate {d : ℕ} (ξ : Euclidean d) (i : Fin d) :
    domainFourierPhase ξ (coordinateVector i) =
      -2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℝ) := by
  change -2 * (Real.pi : ℂ) * Complex.I *
    (inner ℝ (basisVector i) ξ : ℝ) = _
  rw [real_inner_comm, inner_basisVector]

def domainFourierExp {d : ℕ} (ξ : Euclidean d) (x : Domain d) :=
  Complex.exp (domainFourierPhase ξ x)

lemma domainFourierExp_smooth {d : ℕ} (ξ : Euclidean d) :
    ContDiff ℝ ∞ (domainFourierExp ξ) :=
  Complex.contDiff_exp.comp (domainFourierPhase ξ).contDiff

lemma domainFourierExp_partial_mul {d : ℕ} (a : Domain d → ℂ)
    (ha : ContDiff ℝ ∞ a) (i : Fin d) (ξ : Euclidean d) :
    partialFunction [i] (fun x => a x * domainFourierExp ξ x) =
      (fun x => partialFunction [i] a x * domainFourierExp ξ x) +
      (fun x => (-2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℝ)) *
        (a x * domainFourierExp ξ x)) := by
  funext x
  have hexp := ((domainFourierPhase ξ).hasFDerivAt (x := x)).cexp
  have hmul := (ha.differentiable (by simp) x).hasFDerivAt.mul hexp
  change fderiv ℝ (fun x => a x * domainFourierExp ξ x) x (coordinateVector i) = _
  change fderiv ℝ (a * (fun x => Complex.exp (domainFourierPhase ξ x))) x (coordinateVector i) = _
  rw [hmul.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    domainFourierPhase_coordinate, Pi.add_apply, domainFourierExp]
  change _ = fderiv ℝ a x (coordinateVector i) * _ + _
  ring

def compactOscPartial {d : ℕ} (K : Compacts (Domain d)) (w : List (Fin d))
    (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) (ξ : Euclidean d) : C(K,ℂ) :=
  ⟨fun x => partialFunction w (fun x => a x * domainFourierExp ξ x) x,
    (partialFunction_smooth w _ (ha.mul (domainFourierExp_smooth ξ))).continuous.comp
      continuous_subtype_val⟩

lemma compactOscPartial_append_singleton {d : ℕ} (K : Compacts (Domain d))
    (w : List (Fin d)) (i : Fin d) (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a)
    (ξ : Euclidean d) :
    compactOscPartial K (w ++ [i]) a ha ξ =
      compactOscPartial K w (partialFunction [i] a) (partialFunction_smooth [i] a ha) ξ +
      (-2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℝ)) • compactOscPartial K w a ha ξ := by
  apply ContinuousMap.ext
  intro x
  change partialFunction (w ++ [i]) (fun x => a x * domainFourierExp ξ x) x = _
  rw [partialFunction_append, domainFourierExp_partial_mul a ha i ξ]
  rw [partialFunction_add w _ _ ((partialFunction_smooth [i] a ha).mul (domainFourierExp_smooth ξ))
    (contDiff_const.mul (ha.mul (domainFourierExp_smooth ξ)))]
  rw [partialFunction_const_mul w _ (ha.mul (domainFourierExp_smooth ξ))]
  rfl

lemma contDiff_compactOscPartial {d : ℕ} (K : Compacts (Domain d)) (w : List (Fin d))
    (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (compactOscPartial K w a ha) := by
  induction w using List.reverseRecOn generalizing a with
  | nil =>
    let v : C(K, Euclidean d) := ⟨fun x => (EuclideanSpace.equiv (Fin d) ℝ).symm x,
      (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp continuous_subtype_val⟩
    let ac : C(K,ℂ) := ⟨fun x => a x, ha.continuous.comp continuous_subtype_val⟩
    have hs : ContDiff ℝ ∞ (fun ξ => ac * NormedSpace.exp (compactFourierPhase v ξ)) :=
      contDiff_const.mul (compact_fourier_exponential v).1
    convert hs using 1
    funext ξ
    apply ContinuousMap.ext
    intro x
    change a x * domainFourierExp ξ x = a x * (NormedSpace.exp (compactFourierPhase v ξ)) x
    rw [(compact_fourier_exponential v).2]
    rfl
  | append_singleton w i ih =>
    have hc : ContDiff ℝ ∞ (fun ξ : Euclidean d =>
        -2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℝ)) := by
      apply contDiff_const.mul
      exact Complex.ofRealCLM.contDiff.comp
        (((ContinuousLinearMap.proj i).comp
          (EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap).contDiff)
    have hs := (ih (partialFunction [i] a) (partialFunction_smooth [i] a ha)).add
      (hc.smul (ih a ha))
    convert hs using 1
    funext ξ
    exact compactOscPartial_append_singleton K w i a ha ξ

abbrev CompactCoordinateJetIndex (d N : ℕ) := Σ n : Fin (N+1), Fin n.val → Fin d
abbrev CompactCoordinateJetSpace {d : ℕ} (K : Compacts (Domain d)) (N : ℕ) :=
  CompactCoordinateJetIndex d N → C(K,ℂ)

def compactStepCoordinateJet {d : ℕ} (K : Compacts (Domain d)) (N : ℕ) :
    Step ℂ K →ₗ[ℂ] CompactCoordinateJetSpace K N where
  toFun φ i := ⟨fun x => coordinateDerivative ℂ K i.2 φ x,
    (coordinateDerivative ℂ K i.2 φ).continuous.comp continuous_subtype_val⟩
  map_add' φ ψ := by
    funext i
    apply ContinuousMap.ext
    intro x
    simp only [map_add, BoundedContinuousFunction.add_apply]
    rfl
  map_smul' c φ := by
    funext i
    apply ContinuousMap.ext
    intro x
    simp only [map_smul, BoundedContinuousFunction.smul_apply]
    rfl

@[simp] lemma compactStepCoordinateJet_apply {d : ℕ} (K : Compacts (Domain d)) (N : ℕ)
    (φ : Step ℂ K) (i : CompactCoordinateJetIndex d N) (x : K) :
    compactStepCoordinateJet K N φ i x =
      partialFunction (List.ofFn i.2) φ x := by
  change coordinateDerivative ℂ K i.2 φ x = _
  rw [coordinateDerivative_apply, partialFunction_ofFn i.1.val i.2 φ φ.contDiff]

lemma stepSeminorm_le_compactStepCoordinateJet_norm {d : ℕ}
    (K : Compacts (Domain d)) (N : ℕ) (φ : Step ℂ K) :
    stepSeminorm ℂ K N φ ≤ ‖compactStepCoordinateJet K N φ‖ := by
  apply (step_seminorm_formula ℂ d K N φ _ (norm_nonneg _)).mpr
  intro n hn w x
  by_cases hx : x ∈ K
  · rw [← coordinateDerivative_apply]
    exact (ContinuousMap.norm_coe_le_norm
      (compactStepCoordinateJet K N φ ⟨⟨n,Nat.lt_succ_of_le hn⟩,w⟩) ⟨x,hx⟩).trans
      (norm_le_pi_norm (compactStepCoordinateJet K N φ) _)
  · have hz : iteratedFDeriv ℝ n φ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hx (φ.tsupport_subset
        (tsupport_iteratedFDeriv_subset n ht)))
    simp only [hz, ContinuousMultilinearMap.zero_apply, norm_zero]
    exact norm_nonneg _

lemma distribution_factors_compact_coordinate_jet {d : ℕ}
    (u : KernelDistribution d) (K : Compacts (Domain d)) :
    ∃ N : ℕ, ∃ A : CompactCoordinateJetSpace K N →L[ℂ] ℂ,
      ∀ φ : Step ℂ K,
        A (compactStepCoordinateJet K N φ) = u (TestFunction.ofSupportedIn (subset_univ (K : Set (Domain d))) φ) := by
  obtain ⟨C,hC,N,hb⟩ := (finite_order_criterion ℂ d ⊤ u.toLinearMap).mp u.continuous
    K (subset_univ (K : Set (Domain d)))
  let L : Step ℂ K →ₗ[ℂ] ℂ := u.toLinearMap.comp
    (TestFunction.ofSupportedInCLM ℂ (subset_univ (K : Set (Domain d)))).toLinearMap
  have hbound : ∀ φ : Step ℂ K, ‖L φ‖ ≤ C * ‖compactStepCoordinateJet K N φ‖ := by
    intro φ
    exact (hb φ).trans (mul_le_mul_of_nonneg_left
      (stepSeminorm_le_compactStepCoordinateJet_norm K N φ) hC)
  obtain ⟨A,hA⟩ := exists_clm_factor_of_norm_bound (E := Step ℂ K) (F := CompactCoordinateJetSpace K N)
    (compactStepCoordinateJet K N) L C hbound
  exact ⟨N,A,hA⟩

def compactOscCoordinateJet {d : ℕ} (K : Compacts (Domain d)) (N : ℕ)
    (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) (ξ : Euclidean d) :
    CompactCoordinateJetSpace K N := fun i => compactOscPartial K (List.ofFn i.2) a ha ξ

lemma contDiff_compactOscCoordinateJet {d : ℕ} (K : Compacts (Domain d)) (N : ℕ)
    (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (compactOscCoordinateJet K N a ha) := by
  exact contDiff_pi.mpr (fun i => contDiff_compactOscPartial K (List.ofFn i.2) a ha)

lemma compact_integral_phase_smooth {d : ℕ} :
    ContDiff ℝ ∞ (fun p : Domain d × Euclidean d => domainFourierExp p.2 p.1) := by
  have hi : ContDiff ℝ ∞ (fun p : Domain d × Euclidean d =>
      (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm p.1) p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (((EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff.comp contDiff_fst).inner ℝ contDiff_snd)
  exact (contDiff_const.mul hi).cexp

def compactOscillatoryTest {d : ℕ} (a : Domain d → ℂ)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (ξ : Euclidean d) :
    Tests ℂ (⊤ : Opens (Domain d)) :=
  ⟨fun x => a x * domainFourierExp ξ x, ha.mul (domainFourierExp_smooth ξ),
    hac.mul_right, subset_univ _⟩

def compactFourierCutoffTest {d : ℕ} (a : Domain d → ℂ)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (φ : Schwartz ℂ d) :
    Tests ℂ (⊤ : Opens (Domain d)) :=
  ⟨fun x => a x * schwartzFourier φ ((EuclideanSpace.equiv (Fin d) ℝ).symm x),
    ha.mul ((schwartzFourier φ).smooth (⊤ : ℕ∞) |>.comp
      (EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff), hac.mul_right, subset_univ _⟩

/-- A compactly supported distribution may be passed through a Fourier
integral with a compact frequency test. The proof takes the integral in its
finite Banach coordinate-jet space, so no LF-valued Bochner integral is used. -/
theorem compact_distribution_fourier_pairing {d : ℕ} (u : KernelDistribution d)
    (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    Integrable (fun ξ => u (compactOscillatoryTest a ha hac ξ) * testSchwartz ℂ φ ξ) ∧
    u (compactFourierCutoffTest a ha hac (testSchwartz ℂ φ)) =
      ∫ ξ, u (compactOscillatoryTest a ha hac ξ) * testSchwartz ℂ φ ξ := by
  classical
  let K : Compacts (Domain d) := ⟨tsupport a, hac⟩
  obtain ⟨N,A,hA⟩ := distribution_factors_compact_coordinate_jet u K
  let Q := compactOscCoordinateJet K N a ha
  let G : Euclidean d → CompactCoordinateJetSpace K N :=
    fun ξ => testSchwartz ℂ φ ξ • Q ξ
  let S : Set (Euclidean d) := tsupport (testSchwartz ℂ φ)
  have hS : IsCompact S := φ.hasCompactSupport.comp_homeomorph
    (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph
  have hGc : Continuous G :=
    (testSchwartz ℂ φ).continuous.smul (contDiff_compactOscCoordinateJet K N a ha).continuous
  have hGs : HasCompactSupport G := by
    apply HasCompactSupport.intro hS
    intro ξ hξ
    have hz : testSchwartz ℂ φ ξ = 0 := image_eq_zero_of_notMem_tsupport hξ
    dsimp only [G]
    rw [hz,zero_smul]
  have hGi : Integrable G := hGc.integrable_of_hasCompactSupport hGs
  let T : Euclidean d → Step ℂ K := fun ξ =>
    ⟨fun x => a x * domainFourierExp ξ x, ha.mul (domainFourierExp_smooth ξ),
      fun x hx => by simp [show a x = 0 from image_eq_zero_of_notMem_tsupport hx]⟩
  have hT (ξ : Euclidean d) : compactStepCoordinateJet K N (T ξ) = Q ξ := by
    funext i
    apply ContinuousMap.ext
    intro x
    rw [compactStepCoordinateJet_apply]
    rfl
  have hAQ (ξ : Euclidean d) : A (Q ξ) = u (compactOscillatoryTest a ha hac ξ) := by
    rw [← hT ξ, hA]
    congr 1
  have hAG (ξ : Euclidean d) : A (G ξ) =
      u (compactOscillatoryTest a ha hac ξ) * testSchwartz ℂ φ ξ := by
    dsimp only [G]
    rw [map_smul,hAQ,smul_eq_mul,mul_comm]
  have hpairi : Integrable (fun ξ => u (compactOscillatoryTest a ha hac ξ) * testSchwartz ℂ φ ξ) := by
    simpa only [← hAG] using A.integrable_comp hGi
  let ψ : Step ℂ K :=
    ⟨fun x => a x * schwartzFourier (testSchwartz ℂ φ)
      ((EuclideanSpace.equiv (Fin d) ℝ).symm x),
      ha.mul ((schwartzFourier (testSchwartz ℂ φ)).smooth (⊤ : ℕ∞) |>.comp
        (EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff),
      fun x hx => by simp [show a x = 0 from image_eq_zero_of_notMem_tsupport hx]⟩
  let F : Domain d × Euclidean d → ℂ := fun p =>
    testSchwartz ℂ φ p.2 * (a p.1 * domainFourierExp p.2 p.1)
  have hF : ContDiff ℝ ∞ F :=
    ((testSchwartz ℂ φ).smooth (⊤ : ℕ∞) |>.comp contDiff_snd).mul
      ((ha.comp contDiff_fst).mul compact_integral_phase_smooth)
  have hFs (x : Domain d) (ξ : Euclidean d) (hξ : ξ ∉ S) : F (x,ξ) = 0 := by
    dsimp only [F]
    rw [show testSchwartz ℂ φ ξ = 0 from image_eq_zero_of_notMem_tsupport hξ,zero_mul]
  have hψ : (ψ : Domain d → ℂ) = fun x => ∫ ξ, F (x,ξ) := by
    funext x
    change a x * schwartzFourier (testSchwartz ℂ φ)
      ((EuclideanSpace.equiv (Fin d) ℝ).symm x) = _
    rw [schwartz_integral,integralFourier,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ξ
    dsimp [F,domainFourierExp]
    rw [domainFourierPhase_apply,real_inner_comm]
    ring
  have hJ : compactStepCoordinateJet K N ψ = ∫ ξ, G ξ := by
    funext i
    apply ContinuousMap.ext
    intro x
    let hproj := (ContinuousLinearMap.proj i : CompactCoordinateJetSpace K N →L[ℂ] C(K,ℂ))
    have hpi : Integrable (fun ξ => G ξ i) := hproj.integrable_comp hGi
    change ((compactStepCoordinateJet K N ψ) i) x = hproj (∫ ξ, G ξ) x
    rw [← hproj.integral_comp_comm hGi]
    change ((compactStepCoordinateJet K N ψ) i) x = (∫ ξ, G ξ i) x
    rw [ContinuousMap.integral_apply hpi]
    rw [compactStepCoordinateJet_apply,hψ,
      partialFunction_integral_compact_parameter F hF S hS hFs]
    apply integral_congr_ae
    filter_upwards [] with ξ
    have heq : (fun y => F (y,ξ)) =
        fun y => testSchwartz ℂ φ ξ * (a y * domainFourierExp ξ y) := rfl
    rw [heq,partialFunction_const_mul _ _ (ha.mul (domainFourierExp_smooth ξ))]
    rfl
  refine ⟨hpairi, ?_⟩
  have hψA : A (compactStepCoordinateJet K N ψ) =
      u (compactFourierCutoffTest a ha hac (testSchwartz ℂ φ)) := by
    rw [hA]
    congr 1
  rw [← hψA,hJ,← A.integral_comp_comm hGi]
  exact integral_congr_ae (Filter.Eventually.of_forall hAG)

/-- Compact physical cutoff of a Schwartz function, as an original LF test. -/
def dyadicCutoffTest {d : ℕ} (r : ℝ) (hr : 0 < r) (φ : Schwartz ℂ d) :
    Tests ℂ (⊤ : Opens (Domain d)) :=
  euclideanTest (fun x => dyadicCutoff d (r⁻¹ • x) * φ x)
    (((dyadicCutoff_smooth d).comp (contDiff_id.const_smul r⁻¹)).mul (φ.smooth ⊤))
    (((dyadicCutoff_compact d).comp_homeomorph
      (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))).mul_right)

@[simp] theorem dyadicCutoffTest_apply {d : ℕ} (r : ℝ) (hr : 0 < r)
    (φ : Schwartz ℂ d) (x : Euclidean d) :
    testSchwartz ℂ (dyadicCutoffTest r hr φ) x = dyadicCutoff d (r⁻¹ • x) * φ x := by
  exact congrFun (testSchwartz_euclideanTest _ _ _) x

/-- The canonical dyadic cutoffs converge in the full Schwartz topology. -/
theorem dyadicCutoffTest_tendsto {d : ℕ} (R : ℝ) (hR : 0 < R) (φ : Schwartz ℂ d) :
    Filter.Tendsto (fun j : ℕ => testSchwartz ℂ
      (dyadicCutoffTest (R * 2^j) (by positivity) φ)) Filter.atTop (𝓝 φ) := by
  let r : ℕ → ℝ := fun j => R * 2^j
  have hr (j : ℕ) : 0 < r j := by dsimp [r]; positivity
  have hrlim : Filter.Tendsto r Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos hR).mpr
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  obtain ⟨B, hB0, hB⟩ := tail_cutoff_derivative_bounds (dyadicCutoffBump d)
  apply (schwartz_withSeminorms ℂ (Euclidean d) ℂ).tendsto_nhds_atTop _ _ |>.mpr
  rintro ⟨k,n⟩ ε hε
  let C : ℝ := ∑ i ∈ Finset.range (n+1),
    (n.choose i : ℝ) * B i * SchwartzMap.seminorm ℂ (k+1) (n-i) φ
  have hlim : Filter.Tendsto (fun j : ℕ => (r j / 2)⁻¹ * C) Filter.atTop (𝓝 0) := by
    have hhalf : Filter.Tendsto (fun j => r j / 2) Filter.atTop Filter.atTop :=
      (Filter.tendsto_mul_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)).mpr hrlim
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hhalf).mul_const C
  obtain ⟨j₀, hj₀⟩ := Filter.eventually_atTop.mp
    (((tendsto_order.mp hlim).2 ε hε).and (hrlim.eventually (Filter.eventually_ge_atTop 1)))
  refine ⟨j₀, fun j hj => ?_⟩
  have hsmall (x : Euclidean d) (hx : ‖x‖ < r j / 2) :
      1 - dyadicCutoff d ((r j)⁻¹ • x) = 0 := by
    apply tail_cutoff_eq_zero (dyadicCutoffBump d) (hj₀ j hj).2
    simpa [dyadicCutoffBump, div_eq_mul_inv] using hx.le
  have hbnd := tail_product_seminorm φ
    (φ - testSchwartz ℂ (dyadicCutoffTest (r j) (hr j) φ))
    (fun x => 1 - dyadicCutoff d ((r j)⁻¹ • x))
    (contDiff_const.sub ((dyadicCutoff_smooth d).comp (contDiff_id.const_smul (r j)⁻¹)))
    (by intro x; simp only [sub_apply, dyadicCutoffTest_apply]; ring)
    (r j / 2) (by positivity) hsmall B
    (fun i x => hB i (r j) (hj₀ j hj).2 x) k n
  have hneg : SchwartzMap.seminorm ℂ k n
      (testSchwartz ℂ (dyadicCutoffTest (r j) (hr j) φ) - φ) =
      SchwartzMap.seminorm ℂ k n
      (φ - testSchwartz ℂ (dyadicCutoffTest (r j) (hr j) φ)) := by
    rw [← neg_sub, map_neg_eq_map]
  change SchwartzMap.seminorm ℂ k n
    (testSchwartz ℂ (dyadicCutoffTest (r j) (hr j) φ) - φ) < ε
  rw [hneg]
  exact hbnd.trans_lt (hj₀ j hj).1

/-- Every tempered pairing is the limit of the canonical dyadic compact pairings. -/
theorem tendsto_dyadicCutoff_pairing {d : ℕ} (U : Tempered ℂ d)
    (R : ℝ) (hR : 0 < R) (φ : Schwartz ℂ d) :
    Filter.Tendsto (fun j : ℕ => U (testSchwartz ℂ
      (dyadicCutoffTest (R * 2^j) (by positivity) φ))) Filter.atTop (𝓝 (U φ)) :=
  (U.continuous.tendsto φ).comp (dyadicCutoffTest_tendsto R hR φ)

/-- A dyadic annulus multiplied by a Schwartz function, as an original LF test. -/
def dyadicAnnularTest {d : ℕ} (r : ℝ) (hr : 0 < r) (φ : Schwartz ℂ d) :
    Tests ℂ (⊤ : Opens (Domain d)) :=
  euclideanTest (fun x => dyadicAnnularCutoff d (r⁻¹ • x) * φ x)
    (((dyadicAnnularCutoff_smooth d).comp (contDiff_id.const_smul r⁻¹)).mul (φ.smooth ⊤))
    (((dyadicAnnularCutoff_compact d).comp_homeomorph
      (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))).mul_right)

@[simp] theorem dyadicAnnularTest_apply {d : ℕ} (r : ℝ) (hr : 0 < r)
    (φ : Schwartz ℂ d) (x : Euclidean d) :
    testSchwartz ℂ (dyadicAnnularTest r hr φ) x = dyadicAnnularCutoff d (r⁻¹ • x) * φ x :=
  congrFun (testSchwartz_euclideanTest _ _ _) x

lemma dyadicAnnularTest_avoids_zero {d : ℕ} (r : ℝ) (hr : 0 < r) (φ : Schwartz ℂ d) :
    0 ∉ tsupport (testSchwartz ℂ (dyadicAnnularTest r hr φ)) := by
  intro hz
  have hfun : ⇑(testSchwartz ℂ (dyadicAnnularTest r hr φ)) =
      fun x => dyadicAnnularCutoff d (r⁻¹ • x) * φ x := by ext x; exact dyadicAnnularTest_apply r hr φ x
  rw [hfun] at hz
  have hpre := tsupport_comp_subset_preimage (dyadicAnnularCutoff d)
    (continuous_id.const_smul r⁻¹) (tsupport_mul_subset_left hz)
  have hb := dyadicAnnularCutoff_inner d 0 (by simpa using hpre)
  norm_num at hb

/-- The finite physical partition is also an exact identity of Schwartz maps. -/
theorem dyadicCutoffTest_telescope {d : ℕ} (R : ℝ) (hR : 0 < R)
    (J : ℕ) (φ : Schwartz ℂ d) :
    testSchwartz ℂ (dyadicCutoffTest (R * 2^J) (by positivity) φ) =
      testSchwartz ℂ (dyadicCutoffTest R hR φ) +
        ∑ j ∈ Finset.range J, testSchwartz ℂ
          (dyadicAnnularTest (R * 2^(j+1)) (by positivity) φ) := by
  ext x
  simp only [add_apply, sum_apply, dyadicCutoffTest_apply,
    dyadicAnnularTest_apply]
  rw [← Finset.sum_mul, ← add_mul, dyadicAnnularCutoff_telescope R hR]

/-- The Fourier transform pairing is the limit of the compact inner term plus
its physical annular integrals. This uses the original off-zero agreement. -/
theorem tendsto_inner_add_annular_pairings {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} {U : Tempered ℂ d} (hUK : ExtendsKernel U K)
    (hK : AgreesOffZero K k) (R : ℝ) (hR : 0 < R) (φ : Schwartz ℂ d) :
    Filter.Tendsto (fun J : ℕ => K (dyadicCutoffTest R hR φ) +
      ∑ j ∈ Finset.range J, ∫ x, k x * dyadicAnnularCutoff d
        ((R * 2^(j+1))⁻¹ • x) * φ x) Filter.atTop (𝓝 (U φ)) := by
  have hterm (j : ℕ) :
      U (testSchwartz ℂ (dyadicAnnularTest (R * 2^(j+1)) (by positivity) φ)) =
        ∫ x, k x * dyadicAnnularCutoff d ((R * 2^(j+1))⁻¹ • x) * φ x := by
    rw [hUK]
    rw [(hK _ (dyadicAnnularTest_avoids_zero _ _ _)).2]
    apply integral_congr_ae
    filter_upwards with x
    rw [dyadicAnnularTest_apply]
    ring
  have heq (J : ℕ) :
      U (testSchwartz ℂ (dyadicCutoffTest (R * 2^J) (by positivity) φ)) =
        K (dyadicCutoffTest R hR φ) +
          ∑ j ∈ Finset.range J, ∫ x, k x * dyadicAnnularCutoff d
            ((R * 2^(j+1))⁻¹ • x) * φ x := by
    rw [dyadicCutoffTest_telescope R hR, map_add, map_sum, hUK]
    congr 1
    exact Finset.sum_congr rfl fun j hj => hterm j
  simpa only [heq] using tendsto_dyadicCutoff_pairing U R hR φ

/-- Physical annuli may be moved across the Fourier pairing before taking
limits; no interchange of an infinite distributional sum is assumed. -/
theorem tendsto_inner_add_annular_fourier_pairings {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} {U : Tempered ℂ d} (hUK : ExtendsKernel U K)
    (hK : AgreesOffZero K k) (R : ℝ) (hR : 0 < R)
    (g : ℕ → Schwartz ℂ d)
    (hg : ∀ (j : ℕ) (x : Euclidean d),
      g j x = dyadicAnnularCutoff d ((R * 2^(j+1))⁻¹ • x) * k x)
    (φ : Schwartz ℂ d) :
    Filter.Tendsto (fun J : ℕ =>
      K (dyadicCutoffTest R hR (schwartzFourier φ)) +
        ∑ j ∈ Finset.range J, ∫ ξ, schwartzFourier (g j) ξ * φ ξ)
      Filter.atTop (𝓝 (temperedFourier U φ)) := by
  have hterm (j : ℕ) : (∫ ξ, schwartzFourier (g j) ξ * φ ξ) =
      ∫ x, k x * dyadicAnnularCutoff d ((R * 2^(j+1))⁻¹ • x) * schwartzFourier φ x := by
    change (∫ ξ, (𝓕 (g j)) ξ * φ ξ) = _
    rw [SchwartzMap.integral_fourier_mul_eq]
    apply integral_congr_ae
    filter_upwards with x
    rw [hg]
    change _ * k x * schwartzFourier φ x = _
    ring
  change Filter.Tendsto _ _ (𝓝 (U (schwartzFourier φ)))
  simpa only [hterm] using
    tendsto_inner_add_annular_pairings hUK hK R hR (schwartzFourier φ)

/-- A dyadic series with the annular decay estimate may be integrated
term by term against every Schwartz function vanishing near zero. -/
theorem dyadic_series_pairing_hasSum {d : ℕ} (F : ℕ → Schwartz ℂ d)
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 < R)
    (hb : ∀ (j : ℕ) (ξ : Euclidean d),
      (1 + (R * 2^j) * ‖ξ‖) * ‖F j ξ‖ ≤ C)
    (φ : Schwartz ℂ d) (hφ : 0 ∉ tsupport φ) :
    Integrable (fun ξ => (∑' j, F j ξ) * φ ξ) ∧
      HasSum (fun j => ∫ ξ, F j ξ * φ ξ)
        (∫ ξ, (∑' j, F j ξ) * φ ξ) := by
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp
    (isClosed_tsupport φ).isOpen_compl 0 hφ
  have haway (ξ : Euclidean d) (hξ : φ ξ ≠ 0) : a ≤ ‖ξ‖ := by
    by_contra h
    have hin : ξ ∈ Metric.ball 0 a := by simpa using lt_of_not_ge h
    exact hball hin (subset_tsupport φ hξ)
  let v : ℕ → ℝ := fun j => C * R⁻¹ * (a^(0+1))⁻¹ * (1/2 : ℝ)^j
  have hv : Summable v := summable_dyadic_annular_majorant 0 C R a
  have hv0 (j : ℕ) : 0 ≤ v j := by dsimp [v]; positivity
  have hprod (j : ℕ) (ξ : Euclidean d) :
      ‖F j ξ * φ ξ‖ ≤ v j * ‖φ ξ‖ := by
    by_cases hz : φ ξ = 0
    · simp [hz]
    have hmajor : ‖F j ξ‖ ≤ v j := by
      apply dyadic_annular_majorant 0 j C R a _ hR ha (norm_nonneg _)
      simp only [zero_add, pow_one, pow_zero, mul_one]
      calc
        (1 + R * 2^j * a) * ‖F j ξ‖ ≤
            (1 + R * 2^j * ‖ξ‖) * ‖F j ξ‖ := by gcongr; exact haway ξ hz
        _ ≤ C := hb j ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hmajor (norm_nonneg _)
  have hsum (ξ : Euclidean d) : Summable (fun j => F j ξ * φ ξ) :=
    (hv.mul_right ‖φ ξ‖).of_norm_bounded (fun j => hprod j ξ)
  have hnormsum (ξ : Euclidean d) : Summable (fun j => ‖F j ξ * φ ξ‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hprod j ξ)
      (hv.mul_right ‖φ ξ‖)
  have hint : Integrable (fun ξ => ∑' j, v j * ‖φ ξ‖) := by
    simpa only [tsum_mul_right] using φ.integrable.norm.const_mul (∑' j, v j)
  have hmeas : AEStronglyMeasurable (fun ξ => (∑' j, F j ξ) * φ ξ) volume :=
    ((Measurable.tsum (fun j => (F j).continuous.measurable)).mul φ.continuous.measurable).aestronglyMeasurable
  refine ⟨hint.mono' hmeas ?_, ?_⟩
  · filter_upwards with ξ
    rw [← tsum_mul_right]
    exact (norm_tsum_le_tsum_norm (hnormsum ξ)).trans
      (Summable.tsum_le_tsum (fun j => hprod j ξ) (hnormsum ξ) (hv.mul_right ‖φ ξ‖))
  · apply hasSum_integral_of_dominated_convergence (fun j ξ => v j * ‖φ ξ‖)
    · intro j
      exact ((F j).continuous.mul φ.continuous).aestronglyMeasurable
    · intro j
      exact Filter.Eventually.of_forall (hprod j)
    · exact Filter.Eventually.of_forall (fun ξ => hv.mul_right ‖φ ξ‖)
    · exact hint
    · filter_upwards with ξ
      simpa only [tsum_mul_right] using (hsum ξ).hasSum

/-- The outer Fourier series and compact inner distribution recover the
original Fourier transform on every frequency test supported away from zero. -/
theorem fourier_pairing_eq_inner_add_outer_series {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} {U : Tempered ℂ d} (hUK : ExtendsKernel U K)
    (hK : AgreesOffZero K k) (R : ℝ) (hR : 0 < R)
    (g : ℕ → Schwartz ℂ d)
    (hg : ∀ (j : ℕ) (x : Euclidean d),
      g j x = dyadicAnnularCutoff d ((R * 2^(j+1))⁻¹ • x) * k x)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (j : ℕ) (ξ : Euclidean d),
      (1 + (R * 2^(j+1)) * ‖ξ‖) * ‖schwartzFourier (g j) ξ‖ ≤ C)
    (φ : Schwartz ℂ d) (hφ : 0 ∉ tsupport φ) :
    Integrable (fun ξ => (∑' j, schwartzFourier (g j) ξ) * φ ξ) ∧
      temperedFourier U φ = K (dyadicCutoffTest R hR (schwartzFourier φ)) +
        ∫ ξ, (∑' j, schwartzFourier (g j) ξ) * φ ξ := by
  have hb' (j : ℕ) (ξ : Euclidean d) :
      (1 + ((R * 2) * 2^j) * ‖ξ‖) * ‖schwartzFourier (g j) ξ‖ ≤ C := by
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hb j ξ
  obtain ⟨hint, hsum⟩ := dyadic_series_pairing_hasSum
    (fun j => schwartzFourier (g j)) C (R*2) hC (by positivity) hb' φ hφ
  refine ⟨hint, ?_⟩
  exact tendsto_nhds_unique
    (tendsto_inner_add_annular_fourier_pairings hUK hK R hR g hg φ)
    (hsum.tendsto_sum_nat.const_add _)

lemma annularKernel_smooth_compact {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ∞ (fun x => dyadicAnnularCutoff d (r⁻¹ • x) * k x) ∧
      HasCompactSupport (fun x => dyadicAnnularCutoff d (r⁻¹ • x) * k x) := by
  obtain ⟨C, hC, hb⟩ := annular_kernel_fourier_decay hK (dyadicAnnularCutoff d)
    (dyadicAnnularCutoff_smooth d) (dyadicAnnularCutoff_compact d)
    (dyadicAnnularCutoff_support d) (by norm_num : (0 : ℝ) < 1/4)
    (dyadicAnnularCutoff_inner d) 0 0
  obtain ⟨φ, hφ, hbound⟩ := hb r hr
  rw [← hφ]
  exact ⟨(testSchwartz ℂ φ).smooth (⊤ : ℕ∞), φ.hasCompactSupport.comp_homeomorph
    (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph⟩

def annularKernelTest {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (r : ℝ) (hr : 0 < r) :
    Tests ℂ (⊤ : Opens (Domain d)) :=
  euclideanTest (fun x => dyadicAnnularCutoff d (r⁻¹ • x) * k x)
    (annularKernel_smooth_compact hK r hr).1 (annularKernel_smooth_compact hK r hr).2

@[simp] theorem testSchwartz_annularKernelTest {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (r : ℝ) (hr : 0 < r) :
    ⇑(testSchwartz ℂ (annularKernelTest hK r hr)) =
      (fun x => dyadicAnnularCutoff d (r⁻¹ • x) * k x) :=
  testSchwartz_euclideanTest _ _ _

lemma annularKernelTest_fourier_decay {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (n L : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, ∀ hr : 0 < r, ∀ ξ : Euclidean d,
      (1 + r * ‖ξ‖)^L * ‖iteratedFDeriv ℝ n
        (schwartzFourier (testSchwartz ℂ (annularKernelTest hK r hr))) ξ‖ ≤ C * r^n := by
  obtain ⟨C, hC, hb⟩ := annular_kernel_fourier_decay hK (dyadicAnnularCutoff d)
    (dyadicAnnularCutoff_smooth d) (dyadicAnnularCutoff_compact d)
    (dyadicAnnularCutoff_support d) (by norm_num : (0 : ℝ) < 1/4)
    (dyadicAnnularCutoff_inner d) n L
  refine ⟨C, hC, ?_⟩
  intro r hr ξ
  obtain ⟨φ, hφ, hbound⟩ := hb r hr
  have heq : testSchwartz ℂ (annularKernelTest hK r hr) = testSchwartz ℂ φ := by
    apply SchwartzMap.ext
    intro x
    rw [testSchwartz_annularKernelTest]
    exact congrFun hφ x |>.symm
  rw [heq]
  exact hbound ξ

/-- Fourier transform of the canonical outer annular pieces. -/
def outerAnnularFourier {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (R : ℝ) (hR : 0 < R)
    (j : ℕ) : Schwartz ℂ d :=
  schwartzFourier (testSchwartz ℂ (annularKernelTest hK (R * 2^(j+1)) (by positivity)))

def outerFourierSeries {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (R : ℝ) (hR : 0 < R) :
    Euclidean d → ℂ := fun ξ => ∑' j, outerAnnularFourier hK R hR j ξ

lemma outerAnnularFourier_decay {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R) (j : ℕ) (ξ : Euclidean d),
      (1 + (2*R * 2^j) * ‖ξ‖)^(n+1) *
        ‖iteratedFDeriv ℝ n (outerAnnularFourier hK R hR j) ξ‖ ≤
          C * (2*R * 2^j)^n := by
  obtain ⟨C, hC, hb⟩ := annularKernelTest_fourier_decay hK n (n+1)
  refine ⟨C, hC, ?_⟩
  intro R hR j ξ
  have h := hb (R*2^(j+1)) (by positivity) ξ
  have he : R*2^(j+1) = 2*R*2^j := by rw [pow_succ]; ring
  simpa only [outerAnnularFourier, he] using h

lemma outerFourierSeries_on_open {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (R : ℝ) (hR : 0 < R)
    (s : Set (Euclidean d)) (hs : IsOpen s) (hsc : IsPreconnected s)
    (a : ℝ) (ha : 0 < a) (hregion : ∀ ξ ∈ s, a ≤ ‖ξ‖) :
    ContDiffOn ℝ ∞ (outerFourierSeries hK R hR) s ∧
      ∀ n, EqOn (iteratedFDeriv ℝ n (outerFourierSeries hK R hR))
        (fun ξ => ∑' j, iteratedFDeriv ℝ n (outerAnnularFourier hK R hR j) ξ) s := by
  choose C hC hb using outerAnnularFourier_decay hK
  exact contDiffOn_outer_dyadic_series _ s hs hsc
    (fun j => (outerAnnularFourier hK R hR j).smooth (⊤ : ℕ∞)) (2*R) a (by positivity) ha hregion C
    (fun n j ξ _hξ => hb n R hR j ξ)

lemma outerFourierSeries_offZero {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (R : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (outerFourierSeries hK R hR) ({0}ᶜ : Set (Euclidean d)) ∧
      ∀ n ξ, ξ ≠ 0 → iteratedFDeriv ℝ n (outerFourierSeries hK R hR) ξ =
        ∑' j, iteratedFDeriv ℝ n (outerAnnularFourier hK R hR j) ξ := by
  have hlocal (ξ : Euclidean d) (hξ : ξ ≠ 0) := by
    have ha : 0 < ‖ξ‖/2 := half_pos (norm_pos_iff.mpr hξ)
    have hregion : ∀ y ∈ Metric.ball ξ (‖ξ‖/2), ‖ξ‖/2 ≤ ‖y‖ := by
      intro y hy
      have hy' : ‖ξ-y‖ < ‖ξ‖/2 := by
        simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
      have h := norm_sub_norm_le ξ y
      linarith
    exact outerFourierSeries_on_open hK R hR (Metric.ball ξ (‖ξ‖/2))
      Metric.isOpen_ball (convex_ball ξ _).isPreconnected (‖ξ‖/2) ha hregion
  constructor
  · intro ξ hξ
    have hξ0 : ξ ≠ 0 := by simpa using hξ
    exact ((hlocal ξ hξ0).1.contDiffAt
      (Metric.ball_mem_nhds ξ (half_pos (norm_pos_iff.mpr hξ0)))).contDiffWithinAt
  · intro n ξ hξ
    exact (hlocal ξ hξ).2 n (Metric.mem_ball_self (half_pos (norm_pos_iff.mpr hξ)))

lemma summable_outerAnnularFourier_derivatives {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (R : ℝ) (hR : 0 < R)
    (n : ℕ) (ξ : Euclidean d) (hξ : ξ ≠ 0) :
    Summable (fun j => iteratedFDeriv ℝ n (outerAnnularFourier hK R hR j) ξ) := by
  obtain ⟨C, hC, hb⟩ := outerAnnularFourier_decay hK n
  apply Summable.of_norm_bounded (summable_dyadic_annular_majorant n C (2*R) ‖ξ‖)
  intro j
  exact dyadic_annular_majorant n j C (2*R) ‖ξ‖ _ (by positivity)
    (norm_pos_iff.mpr hξ) (norm_nonneg _) (hb R hR j ξ)

lemma outerFourierSeries_derivative_bound {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R) (a : ℝ), 0 < a →
      ∀ ξ : Euclidean d, a ≤ ‖ξ‖ →
      ‖iteratedFDeriv ℝ n (outerFourierSeries hK R hR) ξ‖ ≤
        C * R⁻¹ * (a^(n+1))⁻¹ := by
  obtain ⟨C, hC, hb⟩ := outerAnnularFourier_decay hK n
  refine ⟨C, hC, ?_⟩
  intro R hR a ha ξ hξ
  have hξ0 : ξ ≠ 0 := norm_pos_iff.mp (ha.trans_le hξ)
  rw [(outerFourierSeries_offZero hK R hR).2 n ξ hξ0]
  have hsum := norm_tsum_dyadic_annular_bound
    (fun j => iteratedFDeriv ℝ n (outerAnnularFourier hK R hR j) ξ)
    n C (2*R) a (by positivity) ha (fun j => ?_)
  · convert hsum using 1
    field_simp
  · calc
      (1 + (2*R * 2^j) * a)^(n+1) *
          ‖iteratedFDeriv ℝ n (outerAnnularFourier hK R hR j) ξ‖ ≤
        (1 + (2*R * 2^j) * ‖ξ‖)^(n+1) *
          ‖iteratedFDeriv ℝ n (outerAnnularFourier hK R hR j) ξ‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply pow_le_pow_left₀ (by positivity)
        have h := mul_le_mul_of_nonneg_left hξ (by positivity : 0 ≤ 2*R*2^j)
        linarith
      _ ≤ C * (2*R*2^j)^n := hb R hR j ξ

lemma outerFourierSeries_scale_bound {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R) (ξ : Euclidean d),
      R⁻¹ ≤ ‖ξ‖ → ‖iteratedFDeriv ℝ n (outerFourierSeries hK R hR) ξ‖ ≤ C * R^n := by
  obtain ⟨C, hC, hb⟩ := outerFourierSeries_derivative_bound hK n
  refine ⟨C, hC, ?_⟩
  intro R hR ξ hξ
  have h := hb R hR R⁻¹ (inv_pos.mpr hR) ξ hξ
  convert h using 1
  rw [inv_pow, inv_inv, pow_succ]
  field_simp

lemma outerFourierSeries_neighborhood_bound {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ₀ : Euclidean d, ∀ hξ₀ : ξ₀ ≠ 0,
      ∀ ξ ∈ Metric.ball ξ₀ (‖ξ₀‖/2),
        ‖iteratedFDeriv ℝ n (outerFourierSeries hK ‖ξ₀‖⁻¹
          (inv_pos.mpr (norm_pos_iff.mpr hξ₀))) ξ‖ ≤ C * (‖ξ₀‖^n)⁻¹ := by
  obtain ⟨C, hC, hb⟩ := outerFourierSeries_derivative_bound hK n
  refine ⟨C*2^(n+1), by positivity, ?_⟩
  intro ξ₀ hξ₀ ξ hξ
  have hpos : 0 < ‖ξ₀‖ := norm_pos_iff.mpr hξ₀
  have hregion : ‖ξ₀‖/2 ≤ ‖ξ‖ := by
    have hy' : ‖ξ₀-ξ‖ < ‖ξ₀‖/2 := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hξ
    have h := norm_sub_norm_le ξ₀ ξ
    linarith
  have h := hb ‖ξ₀‖⁻¹ (inv_pos.mpr hpos) (‖ξ₀‖/2) (by positivity) ξ hregion
  convert h using 1
  rw [inv_inv, div_pow, inv_div, pow_succ]
  field_simp
  <;> ring

/-- The canonical outer Fourier series recovers the exact LF cutoff pairing. -/
theorem fourier_pairing_eq_inner_add_canonical_outer {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} {U : Tempered ℂ d} (hUK : ExtendsKernel U K)
    (hK : KernelBounds K k) (R : ℝ) (hR : 0 < R)
    (φ : Schwartz ℂ d) (hφ : 0 ∉ tsupport φ) :
    Integrable (fun ξ => outerFourierSeries hK R hR ξ * φ ξ) ∧
      temperedFourier U φ = K (dyadicCutoffTest R hR (schwartzFourier φ)) +
        ∫ ξ, outerFourierSeries hK R hR ξ * φ ξ := by
  obtain ⟨C, hC, hb⟩ := annularKernelTest_fourier_decay hK 0 1
  let g : ℕ → Schwartz ℂ d := fun j =>
    testSchwartz ℂ (annularKernelTest hK (R*2^(j+1)) (by positivity))
  have hg (j : ℕ) (x : Euclidean d) :
      g j x = dyadicAnnularCutoff d ((R*2^(j+1))⁻¹ • x) * k x :=
    congrFun (testSchwartz_annularKernelTest hK (R*2^(j+1)) (by positivity)) x
  have hbound (j : ℕ) (ξ : Euclidean d) :
      (1 + (R*2^(j+1))*‖ξ‖) * ‖schwartzFourier (g j) ξ‖ ≤ C := by
    simpa only [g, pow_one, norm_iteratedFDeriv_zero, pow_zero, mul_one] using
      hb (R*2^(j+1)) (by positivity) ξ
  exact fourier_pairing_eq_inner_add_outer_series hUK hK.1 R hR g hg C hC hbound φ hφ

/-- The Fourier function of a compactly supported distribution is smooth.
The proof factors through its finite Banach coordinate-jet space. -/
theorem contDiff_compact_distribution_fourier {d : ℕ} (u : KernelDistribution d)
    (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) :
    ContDiff ℝ ∞ (fun ξ => u (compactOscillatoryTest a ha hac ξ)) := by
  classical
  let S : Compacts (Domain d) := ⟨tsupport a, hac⟩
  obtain ⟨N,A,hA⟩ := distribution_factors_compact_coordinate_jet u S
  let T : Euclidean d → Step ℂ S := fun ξ =>
    ⟨fun x => a x * domainFourierExp ξ x, ha.mul (domainFourierExp_smooth ξ),
      fun x hx => by simp [show a x = 0 from image_eq_zero_of_notMem_tsupport hx]⟩
  have hT (ξ : Euclidean d) :
      compactStepCoordinateJet S N (T ξ) = compactOscCoordinateJet S N a ha ξ := by
    funext i
    apply ContinuousMap.ext
    intro x
    rw [compactStepCoordinateJet_apply]
    rfl
  have hscalar : (fun ξ => u (compactOscillatoryTest a ha hac ξ)) =
      fun ξ => A (compactOscCoordinateJet S N a ha ξ) := by
    funext ξ
    rw [← hT ξ, hA]
    rfl
  rw [hscalar]
  exact (A.restrictScalars ℝ).contDiff.comp (contDiff_compactOscCoordinateJet S N a ha)

/-- The canonical physical cutoff in the original coordinate realization. -/
def scaledPhysicalCutoff {d : ℕ} (R : ℝ) : Domain d → ℂ :=
  fun x => dyadicCutoff d (R⁻¹ • (EuclideanSpace.equiv (Fin d) ℝ).symm x)

lemma scaledPhysicalCutoff_smooth {d : ℕ} (R : ℝ) :
    ContDiff ℝ ∞ (scaledPhysicalCutoff (d := d) R) :=
  (dyadicCutoff_smooth d).comp
    ((contDiff_id.const_smul R⁻¹).comp (EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff)

lemma scaledPhysicalCutoff_compact {d : ℕ} (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (scaledPhysicalCutoff (d := d) R) :=
  ((dyadicCutoff_compact d).comp_homeomorph
    (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))).comp_homeomorph
      (EuclideanSpace.equiv (Fin d) ℝ).symm.toHomeomorph

/-- The compact inner Fourier function at a prescribed physical radius. -/
def innerFourierFunction {d : ℕ} (K : KernelDistribution d)
    (R : ℝ) (hR : 0 < R) (ξ : Euclidean d) : ℂ :=
  K (compactOscillatoryTest (scaledPhysicalCutoff R)
    (scaledPhysicalCutoff_smooth R) (scaledPhysicalCutoff_compact R hR) ξ)

lemma innerFourierFunction_smooth {d : ℕ} (K : KernelDistribution d)
    (R : ℝ) (hR : 0 < R) : ContDiff ℝ ∞ (innerFourierFunction K R hR) :=
  contDiff_compact_distribution_fourier K (scaledPhysicalCutoff R)
    (scaledPhysicalCutoff_smooth R) (scaledPhysicalCutoff_compact R hR)

/-- The Fourier model obtained by splitting the physical distribution at R. -/
def localFourierModel {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (R : ℝ) (hR : 0 < R) :
    Euclidean d → ℂ :=
  fun ξ => innerFourierFunction K R hR ξ + outerFourierSeries hK R hR ξ

lemma localFourierModel_smooth_offZero {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (R : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (localFourierModel hK R hR) ({0}ᶜ : Set (Euclidean d)) :=
  (innerFourierFunction_smooth K R hR).contDiffOn.add
    (outerFourierSeries_offZero hK R hR).1

lemma innerFourierFunction_pairing {d : ℕ} (K : KernelDistribution d)
    (R : ℝ) (hR : 0 < R) (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    Integrable (fun ξ => innerFourierFunction K R hR ξ * testSchwartz ℂ φ ξ) ∧
      K (dyadicCutoffTest R hR (schwartzFourier (testSchwartz ℂ φ))) =
        ∫ ξ, innerFourierFunction K R hR ξ * testSchwartz ℂ φ ξ := by
  have htest : compactFourierCutoffTest (scaledPhysicalCutoff R)
      (scaledPhysicalCutoff_smooth R) (scaledPhysicalCutoff_compact R hR)
      (testSchwartz ℂ φ) =
        dyadicCutoffTest R hR (schwartzFourier (testSchwartz ℂ φ)) := by
    ext x
    rfl
  simpa only [innerFourierFunction, htest] using
    compact_distribution_fourier_pairing K (scaledPhysicalCutoff R)
      (scaledPhysicalCutoff_smooth R) (scaledPhysicalCutoff_compact R hR) φ

/-- The model is the Fourier transform on every original test away from zero.
This statement includes integrability and uses the genuine distribution pairing. -/
theorem localFourierModel_agreesOffZero {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} {U : Tempered ℂ d}
    (hUK : ExtendsKernel U K) (hK : KernelBounds K k)
    (R : ℝ) (hR : 0 < R) :
    FourierAgreesOffZero U (localFourierModel hK R hR) := by
  intro φ hφ
  obtain ⟨hin, heqin⟩ := innerFourierFunction_pairing K R hR φ
  obtain ⟨hout, heqout⟩ := fourier_pairing_eq_inner_add_canonical_outer
    hUK hK R hR (testSchwartz ℂ φ) hφ
  constructor
  · have hadd : Integrable (fun ξ => innerFourierFunction K R hR ξ * testSchwartz ℂ φ ξ +
        outerFourierSeries hK R hR ξ * testSchwartz ℂ φ ξ) := hin.add hout
    convert hadd using 1
    funext ξ
    dsimp only [localFourierModel]
    ring
  · rw [heqout, heqin]
    simpa only [localFourierModel, add_mul] using (integral_add hin hout).symm

section General
variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma fderiv_slice_left (G : E × F → H) (hG : ContDiff ℝ ∞ G) (x : E) (y : F) (v : E) :
    fderiv ℝ (fun z => G (z,y)) x v = fderiv ℝ G (x,y) (v,0) := by
  have h := ((hG.differentiable (by simp) (x,y)).hasFDerivAt).comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const y x))
  have he := congrArg (fun L : E →L[ℝ] H => L v) h.fderiv
  simpa [Function.comp_def] using he

lemma fderiv_slice_right (G : E × F → H) (hG : ContDiff ℝ ∞ G) (x : E) (y : F) (w : F) :
    fderiv ℝ (fun z => G (x,z)) y w = fderiv ℝ G (x,y) (0,w) := by
  have h := ((hG.differentiable (by simp) (x,y)).hasFDerivAt).comp y
    ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y))
  have he := congrArg (fun L : F →L[ℝ] H => L w) h.fderiv
  simpa [Function.comp_def] using he

lemma fderiv_apply_const (G : E → F →L[ℝ] H) (hG : ContDiff ℝ ∞ G) (x : E) (v : E) (w : F) :
    fderiv ℝ (fun z => G z w) x v = fderiv ℝ G x v w := by
  have h := ((hG.differentiable (by simp) x).hasFDerivAt).clm_apply
    (hasFDerivAt_const w x)
  have he := congrArg (fun L : E →L[ℝ] H => L v) h.fderiv
  simpa [Function.comp_def] using he

lemma mixed_fderiv_comm (G : E × F → H) (hG : ContDiff ℝ ∞ G)
    (x : E) (y : F) (v : E) (w : F) :
    fderiv ℝ (fun t => fderiv ℝ (fun z => G (z,t)) x v) y w =
      fderiv ℝ (fun z => fderiv ℝ (fun t => G (z,t)) y w) x v := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
  have hl : (fun t => fderiv ℝ (fun z => G (z,t)) x v) =
      fun t => fderiv ℝ G (x,t) (v,0) := funext fun t => fderiv_slice_left G hG x t v
  have hr : (fun z => fderiv ℝ (fun t => G (z,t)) y w) =
      fun z => fderiv ℝ G (z,y) (0,w) := funext fun z => fderiv_slice_right G hG z y w
  rw [hl,hr]
  rw [fderiv_slice_right _ (hD.clm_apply contDiff_const),
    fderiv_slice_left _ (hD.clm_apply contDiff_const)]
  rw [fderiv_apply_const _ hD, fderiv_apply_const _ hD]
  exact hG.contDiffAt.isSymmSndFDerivAt (by simp) (0,w) (v,0)
end General

lemma fderiv_partialFunction_parameter {d e : ℕ}
    (G : Domain d × Euclidean e → ℂ) (hG : ContDiff ℝ ∞ G)
    (w : List (Fin d)) (x : Domain d) (ξ η : Euclidean e) :
    fderiv ℝ (fun t => partialFunction w (fun z => G (z,t)) x) ξ η =
      partialFunction w (fun z => fderiv ℝ (fun t => G (z,t)) ξ η) x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    change fderiv ℝ (fun t =>
      fderiv ℝ (partialFunction w (fun z => G (z,t))) x (coordinateVector i)) ξ η = _
    rw [mixed_fderiv_comm _ (contDiff_spatial_partialFunction G hG w)]
    have he : (fun z => fderiv ℝ (fun t => partialFunction w (fun z => G (z,t)) z) ξ η) =
        partialFunction w (fun z => fderiv ℝ (fun t => G (z,t)) ξ η) := funext fun z => ih z
    rw [he]
    rfl

lemma domainFourierExp_joint_smooth {d : ℕ} :
    ContDiff ℝ ∞ (fun p : Domain d × Euclidean d => domainFourierExp p.2 p.1) := by
  unfold domainFourierExp
  simp only [domainFourierPhase_apply]
  exact Complex.contDiff_exp.comp (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp
      (((EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff.comp contDiff_fst).inner ℝ contDiff_snd)))

lemma domainFourierExp_frequency_deriv {d : ℕ}
    (a : Domain d → ℂ) (x : Domain d) (ξ η : Euclidean d) :
    fderiv ℝ (fun t => a x * domainFourierExp t x) ξ η =
      (-2 * (Real.pi : ℂ) * Complex.I *
        (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) η : ℝ)) *
        (a x * domainFourierExp ξ x) := by
  let L : Euclidean d →L[ℝ] ℂ := (-2 * (Real.pi : ℂ) * Complex.I) •
    (Complex.ofRealCLM.comp ((innerSL ℝ) ((EuclideanSpace.equiv (Fin d) ℝ).symm x)))
  have h := ((L.hasFDerivAt (x := ξ)).cexp).const_mul (a x)
  have he := congrArg (fun D : Euclidean d →L[ℝ] ℂ => D η) h.fderiv
  change fderiv ℝ (fun t => a x * Complex.exp (L t)) ξ η = _ at he
  convert he using 1
  · rfl
  · change _ = a x * (Complex.exp (L ξ) * L η)
    change _ = a x * (domainFourierExp ξ x *
      (-2 * (Real.pi : ℂ) * Complex.I *
        (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) η : ℝ)))
    ring

lemma fderiv_compactOscPartial {d : ℕ} (K : Compacts (Domain d)) (w : List (Fin d))
    (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) (ξ η : Euclidean d) :
    fderiv ℝ (compactOscPartial K w a ha) ξ η =
      compactOscPartial K w (fun x => domainFourierPhase η x * a x)
        ((domainFourierPhase η).contDiff.mul ha) ξ := by
  apply ContinuousMap.ext
  intro x
  have he : fderiv ℝ (fun t => compactOscPartial K w a ha t x) ξ η =
      (fderiv ℝ (compactOscPartial K w a ha) ξ η) x := by
    have h := (ContinuousMap.evalCLM ℝ x).hasFDerivAt.comp ξ
      ((contDiff_compactOscPartial K w a ha).differentiable (by simp) ξ).hasFDerivAt
    have heq := congrArg (fun D : Euclidean d →L[ℝ] ℂ => D η) h.fderiv
    simpa [Function.comp_def] using heq
  rw [← he]
  change fderiv ℝ (fun t => partialFunction w (fun z => a z * domainFourierExp t z) x) ξ η = _
  rw [fderiv_partialFunction_parameter (fun p : Domain d × Euclidean d => a p.1 * domainFourierExp p.2 p.1)
    ((ha.comp contDiff_fst).mul domainFourierExp_joint_smooth) w x ξ η]
  have hformula : (fun z => fderiv ℝ (fun t => a z * domainFourierExp t z) ξ η) =
      (fun z => (domainFourierPhase η z * a z) * domainFourierExp ξ z) := by
    funext z
    rw [domainFourierExp_frequency_deriv, domainFourierPhase_apply]
    ring
  rw [hformula]
  rfl

lemma fderiv_compactOscCoordinateJet {d : ℕ} (K : Compacts (Domain d)) (N : ℕ)
    (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) (ξ η : Euclidean d) :
    fderiv ℝ (compactOscCoordinateJet K N a ha) ξ η =
      compactOscCoordinateJet K N (fun x => domainFourierPhase η x * a x)
        ((domainFourierPhase η).contDiff.mul ha) ξ := by
  funext i
  have h := hasFDerivAt_pi'.mp
    ((contDiff_compactOscCoordinateJet K N a ha).differentiable (by simp) ξ).hasFDerivAt i
  have he := congrArg (fun D : Euclidean d →L[ℝ] C(K,ℂ) => D η) h.fderiv
  change fderiv ℝ (compactOscPartial K (List.ofFn i.2) a ha) ξ η = _ at he
  exact he.symm.trans (fderiv_compactOscPartial K (List.ofFn i.2) a ha ξ η)

def phaseWordAmplitude {d n : ℕ} (a : Domain d → ℂ) (v : Fin n → Euclidean d)
    (x : Domain d) : ℂ := a x * ∏ j, domainFourierPhase (v j) x

lemma phaseWordAmplitude_smooth {d n : ℕ} (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a)
    (v : Fin n → Euclidean d) : ContDiff ℝ ∞ (phaseWordAmplitude a v) := by
  exact ha.mul (contDiff_prod (fun j _ => (domainFourierPhase (v j)).contDiff))

lemma compactOscCoordinateJet_congr {d : ℕ} (K : Compacts (Domain d)) (N : ℕ)
    (a b : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (heq : a = b) (ξ : Euclidean d) :
    compactOscCoordinateJet K N a ha ξ = compactOscCoordinateJet K N b hb ξ := by
  subst b
  rfl

lemma iteratedFDeriv_compactOscCoordinateJet {d : ℕ} (K : Compacts (Domain d)) (N n : ℕ)
    (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) (ξ : Euclidean d)
    (v : Fin n → Euclidean d) :
    iteratedFDeriv ℝ n (compactOscCoordinateJet K N a ha) ξ v =
      compactOscCoordinateJet K N (phaseWordAmplitude a v) (phaseWordAmplitude_smooth a ha v) ξ := by
  induction n generalizing a ξ with
  | zero =>
    rw [iteratedFDeriv_zero_apply]
    have hamp : phaseWordAmplitude a v = a := by funext x; simp [phaseWordAmplitude]
    exact compactOscCoordinateJet_congr K N _ _ _ _ hamp.symm ξ
  | succ n ih =>
    rw [DifferentiableAt.iteratedFDeriv_succ_apply_left'
      (((contDiff_compactOscCoordinateJet K N a ha).iteratedFDeriv_right
        (m := 1) (i := n) (by simp)).differentiable (by simp) ξ)]
    have he : (fun t => iteratedFDeriv ℝ n (compactOscCoordinateJet K N a ha) t (Fin.tail v)) =
        compactOscCoordinateJet K N (phaseWordAmplitude a (Fin.tail v))
          (phaseWordAmplitude_smooth a ha (Fin.tail v)) := funext fun t => ih a ha t (Fin.tail v)
    rw [he, fderiv_compactOscCoordinateJet]
    have hamp : (fun x => domainFourierPhase (v 0) x * phaseWordAmplitude a (Fin.tail v) x) =
        phaseWordAmplitude a v := by
      funext x
      simp only [phaseWordAmplitude, Fin.prod_univ_succ, Fin.tail_def]
      ring
    exact compactOscCoordinateJet_congr K N _ _ _ _ hamp ξ

lemma wordMonomial_ofFn {d n : ℕ} (w : Fin n → Fin d) (x : Euclidean d) :
    wordMonomial (List.ofFn w) x = ∏ j, (x (w j) : ℂ) := by
  induction n with
  | zero => simp [wordMonomial]
  | succ n ih =>
    simp only [List.ofFn_succ, wordMonomial, Fin.prod_univ_succ]
    rw [ih]

lemma phaseWordAmplitude_basis {d n : ℕ} (a : Domain d → ℂ)
    (w : Fin n → Fin d) (x : Domain d) :
    phaseWordAmplitude a (fun j => basisVector (w j)) x =
      (-2 * (Real.pi : ℂ) * Complex.I)^n * a x *
        wordMonomial (List.ofFn w) ((EuclideanSpace.equiv (Fin d) ℝ).symm x) := by
  rw [wordMonomial_ofFn]
  simp only [phaseWordAmplitude, domainFourierPhase_apply, inner_basisVector,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma compactOscillatoryTest_phaseWord_basis {d n : ℕ}
    (a : Euclidean d → ℂ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (w : Fin n → Fin d) (ξ : Euclidean d)
    (hphase : HasCompactSupport (phaseWordAmplitude
      (fun x => a ((EuclideanSpace.equiv (Fin d) ℝ).symm x)) (fun j => basisVector (w j)))) :
    compactOscillatoryTest
      (phaseWordAmplitude (fun x => a ((EuclideanSpace.equiv (Fin d) ℝ).symm x))
        (fun j => basisVector (w j)))
      (phaseWordAmplitude_smooth _ (ha.comp (EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff) _)
      hphase ξ =
    ((-2 * (Real.pi : ℂ) * Complex.I)^n) • innerOscillatoryTest a ha hac (List.ofFn w) ξ := by
  ext x
  change phaseWordAmplitude (fun x => a ((EuclideanSpace.equiv (Fin d) ℝ).symm x))
    (fun j => basisVector (w j)) x * domainFourierExp ξ x = _
  rw [phaseWordAmplitude_basis]
  change _ = (-2 * (Real.pi : ℂ) * Complex.I)^n *
    (a ((EuclideanSpace.equiv (Fin d) ℝ).symm x) *
      wordMonomial (List.ofFn w) ((EuclideanSpace.equiv (Fin d) ℝ).symm x) *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) ξ : ℝ)))
  rw [domainFourierExp, domainFourierPhase_apply]
  ring

/-- Agreement off zero lets any one smooth model determine all the jets. -/
lemma iteratedFDeriv_eq_of_offZero_eq {d : ℕ} {f g : Euclidean d → ℂ}
    (heq : EqOn f g ({0}ᶜ : Set (Euclidean d))) (n : ℕ)
    (ξ : Euclidean d) (hξ : ξ ≠ 0) :
    iteratedFDeriv ℝ n f ξ = iteratedFDeriv ℝ n g ξ := by
  have hev : f =ᶠ[nhds ξ] g := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hξ)] with y hy
    exact heq hy
  exact (hev.iteratedFDeriv ℝ n).eq_of_nhds

/-- Local scale models supply global boundedness and every symbol estimate.
No regularity or compatibility at the exceptional point is imposed. -/
theorem bounded_symbol_of_local_models {d : ℕ}
    (m : Euclidean d → ℂ) (hm0 : m 0 = 0)
    (f : (R : ℝ) → 0 < R → Euclidean d → ℂ)
    (hf : ∀ R hR, ContDiffOn ℝ ∞ (f R hR) ({0}ᶜ : Set (Euclidean d)))
    (heq : ∀ R hR, EqOn m (f R hR) ({0}ᶜ : Set (Euclidean d)))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R) (ξ : Euclidean d),
      R⁻¹ ≤ ‖ξ‖ → ‖ξ‖ ≤ 2*R⁻¹ → ‖iteratedFDeriv ℝ n (f R hR) ξ‖ ≤ C*R^n) :
    BoundedFunction m ∧ SymbolBounds m := by
  have hms : ContDiffOn ℝ ∞ m ({0}ᶜ : Set (Euclidean d)) :=
    (hf 1 (by norm_num)).congr (heq 1 (by norm_num))
  have hmder (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Euclidean d, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ n m ξ‖ ≤ C*(‖ξ‖^n)⁻¹ := by
    obtain ⟨C, hC, hbound⟩ := hb n
    refine ⟨C, hC, ?_⟩
    intro ξ hξ
    have hp : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    rw [iteratedFDeriv_eq_of_offZero_eq (heq ‖ξ‖⁻¹ (inv_pos.mpr hp)) n ξ hξ]
    have h := hbound ‖ξ‖⁻¹ (inv_pos.mpr hp) ξ (by simp) (by simp only [inv_inv]; linarith)
    simpa only [inv_pow] using h
  constructor
  · refine ⟨(measurable_of_continuousOn_compl_singleton 0 hms.continuousOn).aestronglyMeasurable, ?_⟩
    obtain ⟨C, hC, hbound⟩ := hmder 0
    refine ⟨C, hC, ?_⟩
    intro ξ
    by_cases hξ : ξ = 0
    · subst ξ
      simpa only [hm0, norm_zero] using hC
    · simpa only [norm_iteratedFDeriv_zero, pow_zero, inv_one, mul_one] using hbound ξ hξ
  · refine ⟨hms, ?_⟩
    intro n w
    obtain ⟨C, hC, hbound⟩ := hmder n
    refine ⟨C, hC, ?_⟩
    intro ξ hξ
    calc
      ‖iteratedFDeriv ℝ n m ξ (fun j => basisVector (w j))‖ ≤
          ‖iteratedFDeriv ℝ n m ξ‖ * ∏ j, ‖basisVector (w j)‖ :=
        (iteratedFDeriv ℝ n m ξ).le_opNorm _
      _ = ‖iteratedFDeriv ℝ n m ξ‖ := by simp
      _ ≤ C * (‖ξ‖^n)⁻¹ := hbound ξ hξ

/-- Patch the value at the origin after gluing models that agree off zero. -/
def gluedSymbol {d : ℕ} (f : (R : ℝ) → 0 < R → Euclidean d → ℂ) :
    Euclidean d → ℂ := fun ξ => if ξ = 0 then 0 else f 1 (by norm_num) ξ

lemma gluedSymbol_eqOn {d : ℕ}
    (f : (R : ℝ) → 0 < R → Euclidean d → ℂ)
    (hcompat : ∀ R hR S hS, EqOn (f R hR) (f S hS) ({0}ᶜ : Set (Euclidean d)))
    (R : ℝ) (hR : 0 < R) :
    EqOn (gluedSymbol f) (f R hR) ({0}ᶜ : Set (Euclidean d)) := by
  intro ξ hξ
  have hξ0 : ξ ≠ 0 := by simpa using hξ
  simpa only [gluedSymbol, if_neg hξ0] using hcompat 1 (by norm_num) R hR hξ

 theorem gluedSymbol_bounded_symbol {d : ℕ}
    (f : (R : ℝ) → 0 < R → Euclidean d → ℂ)
    (hf : ∀ R hR, ContDiffOn ℝ ∞ (f R hR) ({0}ᶜ : Set (Euclidean d)))
    (hcompat : ∀ R hR S hS, EqOn (f R hR) (f S hS) ({0}ᶜ : Set (Euclidean d)))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R) (ξ : Euclidean d),
      R⁻¹ ≤ ‖ξ‖ → ‖ξ‖ ≤ 2*R⁻¹ → ‖iteratedFDeriv ℝ n (f R hR) ξ‖ ≤ C*R^n) :
    BoundedFunction (gluedSymbol f) ∧ SymbolBounds (gluedSymbol f) := by
  exact bounded_symbol_of_local_models (gluedSymbol f) (by simp [gluedSymbol]) f hf
    (gluedSymbol_eqOn f hcompat) hb

/-- LF test pairings determine any continuous representatives away from zero,
even when no integrability near the origin is available. -/
theorem offZero_eq_of_test_pairings {d : ℕ} (f g : Euclidean d → ℂ)
    (hf : ContinuousOn f ({0}ᶜ : Set (Euclidean d)))
    (hg : ContinuousOn g ({0}ᶜ : Set (Euclidean d)))
    (hpair : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      0 ∉ tsupport (testSchwartz ℂ φ) →
        Integrable (fun ξ => f ξ * testSchwartz ℂ φ ξ) ∧
        Integrable (fun ξ => g ξ * testSchwartz ℂ φ ξ) ∧
        (∫ ξ, f ξ * testSchwartz ℂ φ ξ) = ∫ ξ, g ξ * testSchwartz ℂ φ ξ) :
    EqOn f g ({0}ᶜ : Set (Euclidean d)) := by
  have hzero : ∀ ξ : Euclidean d, ξ ≠ 0 → f ξ - g ξ = 0 := by
    apply continuous_offZero_zero_of_test_pairings (fun ξ => f ξ - g ξ) (hf.sub hg)
    intro φ hφ
    obtain ⟨hfi, hgi, heq⟩ := hpair φ hφ
    simp_rw [sub_mul]
    rw [integral_sub hfi hgi, heq, sub_self]
  intro ξ hξ
  exact sub_eq_zero.mp (hzero ξ (by simpa using hξ))

lemma scaledAmplitude_smooth {d : ℕ} (a : Euclidean d → ℂ) (ha : ContDiff ℝ ∞ a) (R : ℝ) :
    ContDiff ℝ ∞ (fun x => a (R⁻¹ • x)) := ha.comp (contDiff_id.const_smul R⁻¹)

lemma scaledAmplitude_compact {d : ℕ} (a : Euclidean d → ℂ) (hac : HasCompactSupport a)
    (R : ℝ) (hR : 0 < R) : HasCompactSupport (fun x => a (R⁻¹ • x)) :=
  hac.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))

lemma scaled_innerOscillatoryTest_eq {d : ℕ} (a : Euclidean d → ℂ)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (R : ℝ) (hR : 0 < R) (w : List (Fin d)) (ξ : Euclidean d) :
    innerOscillatoryTest (fun x => a (R⁻¹ • x)) (scaledAmplitude_smooth a ha R)
        (scaledAmplitude_compact a hac R hR) w ξ =
      (R ^ w.length : ℝ) • dilateTest R hR.ne' (innerOscillatoryTest a ha hac w (R • ξ)) := by
  apply TestFunction.ext
  intro x
  let y := (EuclideanSpace.equiv (Fin d) ℝ).symm x
  have he : inner ℝ (R⁻¹ • y) (R • ξ) = inner ℝ y ξ := by
    simp only [real_inner_smul_left,real_inner_smul_right]
    field_simp
  change a (R⁻¹ • y) * wordMonomial w y *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ y ξ : ℝ)) =
    (R ^ w.length : ℝ) • (a ((EuclideanSpace.equiv (Fin d) ℝ).symm (R⁻¹ • x)) *
      wordMonomial w ((EuclideanSpace.equiv (Fin d) ℝ).symm (R⁻¹ • x)) *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm (R⁻¹ • x)) (R • ξ) : ℝ)))
  rw [map_smul]
  change _ = (R ^ w.length : ℝ) • (a (R⁻¹ • y) * wordMonomial w (R⁻¹ • y) *
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ (R⁻¹ • y) (R • ξ) : ℝ)))
  rw [he,wordMonomial_smul,Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_inv]
  have hRi : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hc : (R : ℂ)^w.length * ((R : ℂ)⁻¹)^w.length = 1 := by
    rw [← mul_pow,mul_inv_cancel₀ hRi,one_pow]
  calc
    _ = ((R : ℂ)^w.length * ((R : ℂ)⁻¹)^w.length) *
      (a (R⁻¹ • y) * wordMonomial w y *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ y ξ : ℝ))) := by rw [hc,one_mul]
    _ = _ := by ring

/-- The compact inner Fourier moments obey the source's scale bound, uniformly
for scaled frequencies of norm at most two. -/
theorem scaled_inner_oscillatory_pairing_bound {d N : ℕ} (K : KernelDistribution d)
    (hK : BumpCancellation K N) (a : Euclidean d → ℂ)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (has : tsupport a ⊆ Metric.closedBall 0 1) (w : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R) (ξ : Euclidean d), ‖R • ξ‖ ≤ 2 →
      ‖K (innerOscillatoryTest (fun x => a (R⁻¹ • x))
        (scaledAmplitude_smooth a ha R) (scaledAmplitude_compact a hac R hR) w ξ)‖ ≤ C * R^w.length := by
  obtain ⟨C,hC,hb⟩ := inner_oscillatory_pairing_bound_weighted K hK a ha hac has w
  refine ⟨C,hC,?_⟩
  intro R hR ξ hξ
  rw [scaled_innerOscillatoryTest_eq a ha hac R hR w ξ]
  change ‖(K.restrictScalars ℝ) ((R ^ w.length : ℝ) • _)‖ ≤ _
  rw [map_smul]
  exact hb R hR ξ hξ

lemma phaseWordAmplitude_compact {d n : ℕ} (a : Domain d → ℂ)
    (hac : HasCompactSupport a) (v : Fin n → Euclidean d) :
    HasCompactSupport (phaseWordAmplitude a v) := hac.mul_right

/-- Exact real frequency derivatives of a compact distributional Fourier
function, including the original phase and all its multilinear directions. -/
theorem iteratedFDeriv_compact_distribution_fourier {d : ℕ} (u : KernelDistribution d)
    (a : Domain d → ℂ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (n : ℕ) (ξ : Euclidean d) (v : Fin n → Euclidean d) :
    iteratedFDeriv ℝ n (fun ξ => u (compactOscillatoryTest a ha hac ξ)) ξ v =
      u (compactOscillatoryTest (phaseWordAmplitude a v)
        (phaseWordAmplitude_smooth a ha v) (phaseWordAmplitude_compact a hac v) ξ) := by
  classical
  let S : Compacts (Domain d) := ⟨tsupport a, hac⟩
  obtain ⟨N,A,hA⟩ := distribution_factors_compact_coordinate_jet u S
  let T : Euclidean d → Step ℂ S := fun t =>
    ⟨fun x => a x * domainFourierExp t x, ha.mul (domainFourierExp_smooth t),
      fun x hx => by simp [show a x = 0 from image_eq_zero_of_notMem_tsupport hx]⟩
  have hT (t : Euclidean d) :
      compactStepCoordinateJet S N (T t) = compactOscCoordinateJet S N a ha t := by
    funext i
    apply ContinuousMap.ext
    intro x
    rw [compactStepCoordinateJet_apply]
    rfl
  have hscalar : (fun t => u (compactOscillatoryTest a ha hac t)) =
      (A.restrictScalars ℝ) ∘ compactOscCoordinateJet S N a ha := by
    funext t
    change u (compactOscillatoryTest a ha hac t) = A (compactOscCoordinateJet S N a ha t)
    rw [← hT t, hA]
    rfl
  rw [hscalar, (A.restrictScalars ℝ).iteratedFDeriv_comp_left
    ((contDiff_compactOscCoordinateJet S N a ha).contDiffAt)
    (show (n : ℕ∞ω) ≤ ∞ by simp)]
  change A (iteratedFDeriv ℝ n (compactOscCoordinateJet S N a ha) ξ v) = _
  rw [iteratedFDeriv_compactOscCoordinateJet]
  let ψ : Step ℂ S :=
    ⟨fun x => phaseWordAmplitude a v x * domainFourierExp ξ x,
      (phaseWordAmplitude_smooth a ha v).mul (domainFourierExp_smooth ξ),
      fun x hx => by simp [phaseWordAmplitude,
        show a x = 0 from image_eq_zero_of_notMem_tsupport hx]⟩
  have hψ : compactStepCoordinateJet S N ψ =
      compactOscCoordinateJet S N (phaseWordAmplitude a v)
        (phaseWordAmplitude_smooth a ha v) ξ := by
    funext i
    apply ContinuousMap.ext
    intro x
    rw [compactStepCoordinateJet_apply]
    rfl
  rw [← hψ, hA]
  rfl

lemma innerFourierFunction_coordinate_derivative {d : ℕ} (K : KernelDistribution d)
    (R : ℝ) (hR : 0 < R) (n : ℕ) (w : Fin n → Fin d) (ξ : Euclidean d) :
    iteratedFDeriv ℝ n (innerFourierFunction K R hR) ξ (fun j => basisVector (w j)) =
      (-2 * (Real.pi : ℂ) * Complex.I)^n *
        K (innerOscillatoryTest (fun x => dyadicCutoff d (R⁻¹ • x))
          (scaledAmplitude_smooth _ (dyadicCutoff_smooth d) R)
          (scaledAmplitude_compact _ (dyadicCutoff_compact d) R hR) (List.ofFn w) ξ) := by
  change iteratedFDeriv ℝ n
    (fun ξ => K (compactOscillatoryTest (scaledPhysicalCutoff R)
      (scaledPhysicalCutoff_smooth R) (scaledPhysicalCutoff_compact R hR) ξ)) ξ
      (fun j => basisVector (w j)) = _
  rw [iteratedFDeriv_compact_distribution_fourier]
  unfold scaledPhysicalCutoff
  rw [compactOscillatoryTest_phaseWord_basis
    (fun x => dyadicCutoff d (R⁻¹ • x))
    (scaledAmplitude_smooth _ (dyadicCutoff_smooth d) R)
    (scaledAmplitude_compact _ (dyadicCutoff_compact d) R hR) w ξ]
  rw [map_smul,smul_eq_mul]

/-- Cancellation gives every derivative of the compact inner Fourier function
its expected power of the physical radius, uniformly on the scaled ball. -/
theorem innerFourierFunction_derivative_bound {d N : ℕ} (K : KernelDistribution d)
    (hc : BumpCancellation K N) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R) (ξ : Euclidean d),
      ‖R • ξ‖ ≤ 2 → ‖iteratedFDeriv ℝ n (innerFourierFunction K R hR) ξ‖ ≤ C*R^n := by
  classical
  intro n
  have hcut : tsupport (dyadicCutoff d) ⊆ Metric.closedBall 0 1 := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra h
    have hnorm : 1 < ‖x‖ := by simpa using h
    exact hx (dyadicCutoff_zero d hnorm.le)
  have hword (w : Fin n → Fin d) := scaled_inner_oscillatory_pairing_bound K hc
    (dyadicCutoff d) (dyadicCutoff_smooth d) (dyadicCutoff_compact d) hcut (List.ofFn w)
  choose C hC hb using hword
  let c : ℝ := ‖-2 * (Real.pi : ℂ) * Complex.I‖^n
  refine ⟨c * ∑ w : Fin n → Fin d, C w,
    mul_nonneg (by dsimp [c]; positivity) (Finset.sum_nonneg (fun w _ => hC w)), ?_⟩
  intro R hR ξ hξ
  calc
    ‖iteratedFDeriv ℝ n (innerFourierFunction K R hR) ξ‖ ≤
        ∑ w : Fin n → Fin d,
          ‖iteratedFDeriv ℝ n (innerFourierFunction K R hR) ξ (fun j => basisVector (w j))‖ :=
      multilinear_coordinate_sum _
    _ ≤ ∑ w : Fin n → Fin d, c * (C w * R^n) := by
      apply Finset.sum_le_sum
      intro w _
      rw [innerFourierFunction_coordinate_derivative,norm_mul,norm_pow]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
      simpa only [List.length_ofFn] using hb w R hR ξ hξ
    _ = (c * ∑ w : Fin n → Fin d, C w) * R^n := by
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w _
      ring

lemma localFourierModel_compatible {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} {U : Tempered ℂ d}
    (hUK : ExtendsKernel U K) (hK : KernelBounds K k)
    (R : ℝ) (hR : 0 < R) (S : ℝ) (hS : 0 < S) :
    EqOn (localFourierModel hK R hR) (localFourierModel hK S hS)
      ({0}ᶜ : Set (Euclidean d)) := by
  apply offZero_eq_of_test_pairings
    (localFourierModel hK R hR) (localFourierModel hK S hS)
    (localFourierModel_smooth_offZero hK R hR).continuousOn
    (localFourierModel_smooth_offZero hK S hS).continuousOn
  intro φ hφ
  obtain ⟨hfi, hf⟩ := localFourierModel_agreesOffZero hUK hK R hR φ hφ
  obtain ⟨hgi, hg⟩ := localFourierModel_agreesOffZero hUK hK S hS φ hφ
  exact ⟨hfi, hgi, hf.symm.trans hg⟩

lemma glued_localFourierModel_agreesOffZero {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} {U : Tempered ℂ d}
    (hUK : ExtendsKernel U K) (hK : KernelBounds K k) :
    FourierAgreesOffZero U (gluedSymbol (localFourierModel hK)) := by
  intro φ hφ
  have hmodel := localFourierModel_agreesOffZero hUK hK 1 (by norm_num) φ hφ
  have heq : (fun ξ => gluedSymbol (localFourierModel hK) ξ * testSchwartz ℂ φ ξ) =
      (fun ξ => localFourierModel hK 1 (by norm_num) ξ * testSchwartz ℂ φ ξ) := by
    funext ξ
    by_cases hξ : ξ = 0
    · subst ξ
      have hφ0 := image_eq_zero_of_notMem_tsupport hφ
      simp [hφ0]
    · simp [gluedSymbol, hξ]
  rw [heq]
  exact hmodel

/-- Add the independent compact and outer-annular derivative estimates. -/
lemma localFourierModel_derivative_bound_of_inner {d : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k)
    (hinner : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R) (ξ : Euclidean d),
      ‖R • ξ‖ ≤ 2 → ‖iteratedFDeriv ℝ n (innerFourierFunction K R hR) ξ‖ ≤ C*R^n) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R) (ξ : Euclidean d),
      R⁻¹ ≤ ‖ξ‖ → ‖ξ‖ ≤ 2*R⁻¹ →
        ‖iteratedFDeriv ℝ n (localFourierModel hK R hR) ξ‖ ≤ C*R^n := by
  intro n
  obtain ⟨C, hC, hCb⟩ := hinner n
  obtain ⟨D, hD, hDb⟩ := outerFourierSeries_scale_bound hK n
  refine ⟨C+D, add_nonneg hC hD, ?_⟩
  intro R hR ξ hlow hupp
  have hξ : ξ ≠ 0 := norm_pos_iff.mp ((inv_pos.mpr hR).trans_le hlow)
  have hξ' : ξ ∈ ({0}ᶜ : Set (Euclidean d)) := by simpa using hξ
  have hscaled : ‖R • ξ‖ ≤ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have h := mul_le_mul_of_nonneg_left hupp hR.le
    calc
      R*‖ξ‖ ≤ R*(2*R⁻¹) := h
      _ = 2 := by field_simp
  have hder : iteratedFDeriv ℝ n (localFourierModel hK R hR) ξ =
      iteratedFDeriv ℝ n (innerFourierFunction K R hR) ξ +
        iteratedFDeriv ℝ n (outerFourierSeries hK R hR) ξ := by
    exact iteratedFDeriv_add_apply
      ((innerFourierFunction_smooth K R hR).of_le (by simp)).contDiffAt
      (((outerFourierSeries_offZero hK R hR).1.contDiffAt
        (isOpen_compl_singleton.mem_nhds hξ')).of_le (by simp))
  rw [hder]
  calc
    ‖iteratedFDeriv ℝ n (innerFourierFunction K R hR) ξ +
        iteratedFDeriv ℝ n (outerFourierSeries hK R hR) ξ‖ ≤
      ‖iteratedFDeriv ℝ n (innerFourierFunction K R hR) ξ‖ +
        ‖iteratedFDeriv ℝ n (outerFourierSeries hK R hR) ξ‖ := norm_add_le _ _
    _ ≤ C*R^n + D*R^n := add_le_add (hCb R hR ξ hscaled) (hDb R hR ξ hlow)
    _ = (C+D)*R^n := by ring

lemma smooth_multiplier_of_inner_bounds {d N : ℕ} {K : KernelDistribution d}
    {k : Euclidean d → ℂ} (hK : KernelBounds K k) (hc : BumpCancellation K N)
    (hinner : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R) (ξ : Euclidean d),
      ‖R • ξ‖ ≤ 2 → ‖iteratedFDeriv ℝ n (innerFourierFunction K R hR) ξ‖ ≤ C*R^n) :
    HasSmoothMultiplier K := by
  obtain ⟨U, hUK⟩ := kernel_temperedness d K k hK
  obtain ⟨hbounded, hsymbol⟩ := gluedSymbol_bounded_symbol (localFourierModel hK)
    (localFourierModel_smooth_offZero hK)
    (localFourierModel_compatible hUK hK)
    (localFourierModel_derivative_bound_of_inner hK hinner)
  exact smooth_multiplier_of_offZero_symbol K U (gluedSymbol (localFourierModel hK))
    hc hUK hbounded (glued_localFourierModel_agreesOffZero hUK hK) hsymbol

/-- Cancellation of one fixed finite bump order constructs the full smooth
multiplier, including equality at frequency zero in the distribution sense. -/
theorem bump_to_symbol :
    Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence.bumpToSymbolType := by
  intro d K k hK hbumps
  obtain ⟨N, hN, hc⟩ := hbumps
  exact smooth_multiplier_of_inner_bounds hK hc (innerFourierFunction_derivative_bound K hc)

/-- The smooth kernel multiplier equivalence in the original distributional
setting, with no temperedness assumption and no discarded zero-frequency term. -/
theorem smooth_kernel_multiplier_equivalence :
    Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence.equivalenceType := by
  intro d K k hK
  have hdrop : HasSmoothMultiplier K → HasBoundedFourier K := by
    rintro ⟨U, m, hU, hm, hrep, hsymbol⟩
    exact ⟨U, m, hU, hm, hrep⟩
  refine ⟨kernel_temperedness d K k hK, ?_, ?_⟩
  · exact ⟨bump_to_symbol d K k hK, fun hm => bounded_to_bumps d K (hdrop hm)⟩
  · exact ⟨fun hm => bump_to_symbol d K k hK (bounded_to_bumps d K hm), hdrop⟩

end ExpandedFA.SingularIntegrals
