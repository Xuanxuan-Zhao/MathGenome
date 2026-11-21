import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.CzAnnularCriterion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.PointSupportedDistributions
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.OperatorNorm

open MeasureTheory Set TopologicalSpace Function
open scoped SchwartzMap ContDiff FourierTransform Topology

set_option maxHeartbeats 1000000

noncomputable section
namespace ExpandedFA.PartIV.CzAnnularCriterion
open ExpandedFA.Distributions ExpandedFA.Fourier ExpandedFA.Fourier.Examples
open ExpandedFA.SingularIntegrals

/-- A polynomial bounded on the positive real ray is constant, also for
complex coefficients. -/
theorem polynomial_constant_of_bounded_real_ray (p : Polynomial ℂ)
    (C : ℝ) (hb : ∀ t : ℝ, 0 < t → ‖p.eval (t : ℂ)‖ ≤ C) :
    p = Polynomial.C (p.coeff 0) := by
  apply Polynomial.eq_C_of_degree_le_zero
  by_contra hdeg
  have hz : Filter.Tendsto (fun t : ℝ => ‖(t : ℂ)‖) Filter.atTop Filter.atTop := by
    simpa using (Filter.tendsto_abs_atTop_atTop :
      Filter.Tendsto (fun t : ℝ => |t|) Filter.atTop Filter.atTop)
  have ht := p.tendsto_norm_atTop (lt_of_not_ge hdeg) hz
  obtain ⟨t, ht, ht0⟩ := ((ht.eventually (Filter.eventually_gt_atTop C)).and
    (Filter.eventually_gt_atTop (0 : ℝ))).exists
  exact (not_lt_of_ge (hb t ht0)) ht

/-- Exact scaling of a delta derivative on amplitude-one test dilations. -/
theorem deltaCoordinateDerivative_dilate {d n : ℕ} (w : Fin n → Fin d)
    (r : ℝ) (hr : r ≠ 0) (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    deltaCoordinateDerivative ℂ ⊤ 0 w (dilateTest r hr φ) =
      (r⁻¹ : ℂ) ^ n * deltaCoordinateDerivative ℂ ⊤ 0 w φ := by
  rw [deltaCoordinateDerivative_apply, deltaCoordinateDerivative_apply]
  change (-1 : ℂ) ^ n *
    iteratedFDeriv ℝ n (fun x => φ (r⁻¹ • x)) 0 _ = _
  rw [iteratedFDeriv_comp_const_smul r⁻¹
    (φ.contDiff.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)))]
  simp only [smul_zero, smul_apply,
    Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_inv]
  ring

/-- Bump cancellation eliminates positive-order derivatives from a distribution
supported at the origin. The proof does not require independent jet coordinates:
it applies the constant-polynomial argument separately to each original test. -/
theorem point_support_bumps :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.pointSupportBumpsType := by
  intro d N u hs hb
  classical
  obtain ⟨m, c, hc⟩ := point_supported_distributions ℂ d ⊤ 0 (by trivial) u hs
  let a : ℂ := ∑ i : JetIndex d m, if i.1.val = 0 then c i else 0
  refine ⟨a, ?_⟩
  ext φ
  obtain ⟨C, _, hC⟩ := bump_cancellation_fixed_test u hb φ
  let p : Polynomial ℂ := ∑ i : JetIndex d m,
    Polynomial.C (c i * deltaCoordinateDerivative ℂ ⊤ 0 i.2 φ) *
      Polynomial.X ^ i.1.val
  have heval (t : ℂ) : p.eval t = ∑ i : JetIndex d m,
      c i * deltaCoordinateDerivative ℂ ⊤ 0 i.2 φ * t ^ i.1.val := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hdil (r : ℝ) (hr : 0 < r) : u (dilateTest r hr.ne' φ) = p.eval (r⁻¹ : ℂ) := by
    rw [hc, heval]
    simp only [sum_apply, smul_apply, smul_eq_mul, deltaCoordinateDerivative_dilate]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hp := polynomial_constant_of_bounded_real_ray p C (by
    intro t ht
    have h := hC t⁻¹ (inv_pos.mpr ht)
    rw [hdil _ (inv_pos.mpr ht)] at h
    simpa using h)
  have hφ : u φ = p.eval 1 := by
    have h := hdil 1 zero_lt_one
    have htest : dilateTest 1 (by norm_num : (1 : ℝ) ≠ 0) φ = φ := by
      ext x
      simp [dilateTest_apply]
    simpa [htest] using h
  have hconst : p.eval 1 = p.eval 0 := by rw [hp]; simp
  have hzero : p.eval 0 = a * φ 0 := by
    rw [heval]
    simp only [a, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rcases i with ⟨⟨n, hn⟩, w⟩
    by_cases hi : n = 0
    · subst n
      simp [deltaCoordinateDerivative_apply, iteratedFDeriv_zero_apply]
    · simp [hi, zero_pow hi]
  change u φ = a * coordinateJet ℂ ⊤ 0 (Fin.elim0 : Fin 0 → Fin d) φ
  simpa [coordinateJet_apply, iteratedFDeriv_zero_apply] using hφ.trans (hconst.trans hzero)

/-- Equality of off-zero kernels gives singleton support of their difference. -/
theorem support_sub_of_agreesOffZero {d : ℕ} {k : Euclidean d → ℂ}
    {K L : KernelDistribution d} (hK : AgreesOffZero K k) (hL : AgreesOffZero L k) :
    distributionSupport (K - L) ⊆ {0} := by
  intro x hx
  by_contra hx0
  apply hx.2
  apply Set.mem_sUnion.mpr
  refine ⟨{0}ᶜ, ⟨isOpen_compl_singleton, subset_univ _, ?_⟩, hx0⟩
  intro φ hφ
  have hzero : 0 ∉ tsupport (testSchwartz ℂ φ) := by
    rw [show tsupport (⇑(testSchwartz ℂ φ)) =
      (EuclideanSpace.equiv (Fin d) ℝ) ⁻¹' tsupport (⇑φ) from
        tsupport_comp_eq_preimage (⇑φ) (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph]
    simpa using (fun h : (0 : Domain d) ∈ tsupport φ => hφ h (by simp))
  change K φ - L φ = 0
  rw [(hK φ hzero).2, (hL φ hzero).2, sub_self]

/-- Full uniqueness assertion, allowing different cancellation orders for the
two extensions and retaining the zero-dimensional case. -/
theorem extension_unique_modulo_dirac :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.uniquenessType := by
  intro d k K L hK hL
  obtain ⟨N, _, hN⟩ := bounded_to_bumps d K hK.2.hasBoundedFourier
  obtain ⟨M, _, hM⟩ := bounded_to_bumps d L hL.2.hasBoundedFourier
  exact point_support_bumps d (max N M) (K - L)
    (support_sub_of_agreesOffZero hK.1.1 hL.1.1) (hN.sub hM)

/-- Bounded measurable multiplication acts continuously on the actual L²
space. This construction also gives its pointwise almost-everywhere action. -/
theorem exists_bounded_multiply_L2 {d : ℕ} (m : Euclidean d → ℂ)
    (hm : AEStronglyMeasurable m volume) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ ξ, ‖m ξ‖ ≤ M) :
    ∃ A : L2 d →L[ℂ] L2 d, ‖A‖ ≤ M ∧
      ∀ f : L2 d, A f =ᵐ[volume] (fun ξ => m ξ * f ξ) := by
  have hmem (f : L2 d) : MemLp (fun ξ => m ξ * f ξ) 2 volume :=
    (Lp.memLp f).of_le_mul (hm.mul (Lp.aestronglyMeasurable f))
      (Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound ξ) (norm_nonneg _))
  let L : L2 d →ₗ[ℂ] L2 d :=
    { toFun f := (hmem f).toLp _
      map_add' f g := by
        apply Lp.ext
        filter_upwards [(hmem (f+g)).coeFn_toLp, Lp.coeFn_add f g,
          Lp.coeFn_add ((hmem f).toLp _) ((hmem g).toLp _),
          (hmem f).coeFn_toLp, (hmem g).coeFn_toLp] with ξ hfg hadd hsum hf hg
        simp only [hfg, hadd, hsum, Pi.add_apply, hf, hg, mul_add]
      map_smul' c f := by
        apply Lp.ext
        filter_upwards [(hmem (c • f)).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((hmem f).toLp _), (hmem f).coeFn_toLp] with ξ hcf hsm hsm' hf
        change (hmem (c • f)).toLp _ ξ = (c • (hmem f).toLp _) ξ
        simp only [hcf, hsm, hsm', Pi.smul_apply, hf, smul_eq_mul]
        ring }
  have hnorm (f : L2 d) : ‖L f‖ ≤ M * ‖f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(hmem f).coeFn_toLp] with ξ hξ
    change ‖(hmem f).toLp _ ξ‖ ≤ M * ‖f ξ‖
    rw [hξ, norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound ξ) (norm_nonneg _)
  refine ⟨L.mkContinuous M hnorm, LinearMap.mkContinuous_norm_le L hM hnorm, ?_⟩
  exact fun f => (hmem f).coeFn_toLp

/-- The source's L² assertion with the same globally represented multiplier.
Plancherel conjugates bounded multiplication to a bounded operator. -/
theorem bounded_fourier_hasL2 {d : ℕ} {K : KernelDistribution d}
    (hK : HasBoundedFourier K) : HasL2Realization K := by
  obtain ⟨U, m, hU, hm, hrep⟩ := hK
  obtain ⟨M, hM, hbound⟩ := hm.2
  obtain ⟨A, hA, hAe⟩ := exists_bounded_multiply_L2 m hm.1 M hM hbound
  let F := Lp.fourierTransformₗᵢ (Euclidean d) ℂ
  let T : L2 d →L[ℂ] L2 d :=
    F.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (A.comp F.toContinuousLinearEquiv.toContinuousLinearMap)
  have hTnorm : ‖T‖ ≤ M := by
    apply ContinuousLinearMap.opNorm_le_bound T hM
    intro f
    change ‖F.symm (A (F f))‖ ≤ M * ‖f‖
    rw [F.symm.norm_map]
    exact (A.le_opNorm _).trans (by
      rw [F.norm_map]
      exact mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  refine ⟨U, m, T, M, hU, hm, hrep, hM, hbound, hTnorm, ?_⟩
  intro f
  have he : 𝓕 (T f) = A (𝓕 f) := F.apply_symm_apply _
  rw [he]
  exact hAe _

theorem standard_consequences :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.standardConsequencesType := by
  intro d k K hK
  exact ⟨bounded_to_bumps d K hK.2.hasBoundedFourier,
    bounded_fourier_hasL2 hK.2.hasBoundedFourier⟩

/-- The already defined order-zero coordinate jet has cancellation constant one. -/
theorem dirac_bump_cancellation (d N : ℕ) :
    BumpCancellation (coordinateJet ℂ ⊤ (0 : Domain d) (Fin.elim0 : Fin 0 → Fin d)) N := by
  refine ⟨1, zero_le_one, ?_⟩
  intro φ hφ r hr
  have h := hφ.2 0 (Nat.zero_le N) (0 : Euclidean d)
  simpa [coordinateJet_apply, iteratedFDeriv_zero_apply, dilateTest_apply,
    norm_iteratedFDeriv_zero, testSchwartz_apply] using h

/-- Every scalar Dirac ambiguity really is allowed; it changes no off-zero
kernel and retains the uniform bump condition. -/
theorem dirac_stability :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.diracStabilityType := by
  intro d k K hK c
  let D := coordinateJet ℂ ⊤ (0 : Domain d) (Fin.elim0 : Fin 0 → Fin d)
  have hkernel : KernelBounds (K + c • D) k := by
    refine ⟨?_, hK.1.2⟩
    intro φ hφ
    refine ⟨(hK.1.1 φ hφ).1, ?_⟩
    have hφ0 : φ 0 = 0 := by
      have hz : testSchwartz ℂ φ 0 = 0 := image_eq_zero_of_notMem_tsupport hφ
      simpa [testSchwartz_apply] using hz
    change K φ + c * coordinateJet ℂ ⊤ 0 (Fin.elim0 : Fin 0 → Fin d) φ = _
    simp only [coordinateJet_apply, iteratedFDeriv_zero_apply, hφ0, mul_zero, add_zero]
    exact (hK.1.1 φ hφ).2
  refine ⟨hkernel, bump_to_symbol d (K+c • D) k hkernel ?_⟩
  obtain ⟨N, hdN, C, hC, hKb⟩ := bounded_to_bumps d K hK.2.hasBoundedFourier
  refine ⟨N, hdN, C + ‖c‖, add_nonneg hC (norm_nonneg _), ?_⟩
  intro φ hφ r hr
  change ‖K (dilateTest r hr.ne' φ) + c * D (dilateTest r hr.ne' φ)‖ ≤ _
  apply (norm_add_le _ _).trans
  apply add_le_add (hKb φ hφ r hr)
  rw [norm_mul]
  have hD : ‖D (dilateTest r hr.ne' φ)‖ ≤ 1 := by
    have h := hφ.2 0 (Nat.zero_le N) (0 : Euclidean d)
    simpa [D, coordinateJet_apply, iteratedFDeriv_zero_apply, dilateTest_apply,
      norm_iteratedFDeriv_zero, testSchwartz_apply] using h
  simpa using mul_le_mul_of_nonneg_left hD (norm_nonneg c)

/-- The order-zero size estimate, isolated from the higher smoothness bounds. -/
theorem kernel_size {d : ℕ} {k : Euclidean d → ℂ}
    (hk : SmoothKernelBounds k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, x ≠ 0 → ‖k x‖ ≤ C * (‖x‖ ^ d)⁻¹ := by
  obtain ⟨C, hC, hbound⟩ := hk.2 0 Fin.elim0
  exact ⟨C, hC, fun x hx => by simpa using hbound x hx⟩

/-- A finite sharp annulus has an ordinary integral without any cancellation
hypothesis. This also supplies integrability for the sharp/smooth comparison. -/
theorem integrableOn_annulus {d : ℕ} {k : Euclidean d → ℂ}
    (hk : SmoothKernelBounds k) {r R : ℝ} (hr : 0 < r) :
    IntegrableOn k {x | r < ‖x‖ ∧ ‖x‖ < R} := by
  obtain ⟨C, hC, hb⟩ := kernel_size hk
  have hm : AEStronglyMeasurable k volume :=
    (measurable_of_continuousOn_compl_singleton 0 hk.1.continuousOn).aestronglyMeasurable
  apply IntegrableOn.of_bound
    ((measure_mono (show {x : Euclidean d | r < ‖x‖ ∧ ‖x‖ < R} ⊆
      Metric.closedBall 0 R from fun x hx => by simpa using hx.2.le)).trans_lt
        (measure_closedBall_lt_top)) hm.restrict (C * (r ^ d)⁻¹)
  filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const measurable_norm |>.inter
    (measurableSet_lt measurable_norm measurable_const))] with x hx
  apply (hb x (by intro h; simp [h, hr.le.not_gt] at hx)).trans
  exact mul_le_mul_of_nonneg_left
    (inv_anti₀ (pow_pos hr d) (pow_le_pow_left₀ hr.le hx.1.le d)) hC

/-- The cutoff error is confined to one shell. Its integral is bounded by a
constant independent of its radius; a ball-volume bound suffices. -/
theorem cutoff_error_bound {d : ℕ} {k : Euclidean d → ℂ}
    (hk : SmoothKernelBounds k) (C : ℝ) (hC : 0 ≤ C)
    (hsize : ∀ x, x ≠ 0 → ‖k x‖ ≤ C * (‖x‖ ^ d)⁻¹)
    (b : ContDiffBump (0 : Euclidean d)) (hb1 : b.rIn = 1) (hb2 : b.rOut = 2)
    (r : ℝ) (hr : 0 < r) :
    let e := fun x : Euclidean d => k x *
      ((Metric.ball (0 : Euclidean d) r).indicator (fun _ => (1 : ℂ)) x - (b (r⁻¹ • x) : ℂ))
    Integrable e ∧ ‖∫ x, e x‖ ≤ C * 2^d * volume.real (Metric.closedBall (0 : Euclidean d) 1) := by
  classical
  dsimp only
  let e := fun x : Euclidean d => k x *
    ((Metric.ball (0 : Euclidean d) r).indicator (fun _ => (1 : ℂ)) x - (b (r⁻¹ • x) : ℂ))
  have hm : AEStronglyMeasurable e volume :=
    (measurable_of_continuousOn_compl_singleton 0 hk.1.continuousOn).aestronglyMeasurable.mul
      ((measurable_const.indicator measurableSet_ball).aestronglyMeasurable.sub
        (Complex.continuous_ofReal.comp (b.continuous.comp (continuous_const_smul r⁻¹))).aestronglyMeasurable)
  have hbnorm (x : Euclidean d) : ‖(b (r⁻¹ • x) : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg] using b.le_one (x := r⁻¹ • x)
  have hinner (x : Euclidean d) (hx : ‖x‖ < r) : e x = 0 := by
    have hbx : b (r⁻¹ • x) = 1 := by
      apply b.one_of_mem_closedBall
      simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr), hb1]
      exact (inv_mul_le_one₀ hr).mpr hx.le
    simp [e, Metric.mem_ball, dist_zero_right, hx, hbx]
  have houter (x : Euclidean d) (hx : 2*r ≤ ‖x‖) : e x = 0 := by
    have hbx : b (r⁻¹ • x) = 0 := by
      apply b.zero_of_le_dist
      simp only [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hb2]
      rw [le_inv_mul_iff₀ hr]
      linarith
    have hxr : ¬ ‖x‖ < r := by linarith
    simp [e, Metric.mem_ball, dist_zero_right, hxr, hbx]
  have hbound (x : Euclidean d) : ‖e x‖ ≤ C * (r^d)⁻¹ := by
    by_cases hx : ‖x‖ < r
    · rw [hinner x hx, norm_zero]
      positivity
    · have hx' : r ≤ ‖x‖ := le_of_not_gt hx
      have hx0 : x ≠ 0 := by intro he; simp [he] at hx'; linarith
      have he : ‖e x‖ = ‖k x‖ * ‖(b (r⁻¹ • x) : ℂ)‖ := by
        simp [e, Metric.mem_ball, dist_zero_right, hx]
      rw [he]
      calc
        ‖k x‖ * ‖(b (r⁻¹ • x) : ℂ)‖ ≤ ‖k x‖ * 1 :=
          mul_le_mul_of_nonneg_left (hbnorm x) (norm_nonneg _)
        _ ≤ C * (r^d)⁻¹ := by
          rw [mul_one]
          exact (hsize x hx0).trans (mul_le_mul_of_nonneg_left
            (inv_anti₀ (pow_pos hr d) (pow_le_pow_left₀ hr.le hx' d)) hC)
  have hs : support e ⊆ Metric.closedBall 0 (2*r) := by
    intro x hx
    by_contra hxball
    have hxnorm : 2*r ≤ ‖x‖ := by
      have : ¬ ‖x‖ ≤ 2*r := by simpa using hxball
      linarith
    exact hx (houter x hxnorm)
  have hint : IntegrableOn e (Metric.closedBall 0 (2*r)) :=
    IntegrableOn.of_bound measure_closedBall_lt_top hm.restrict _
      (Filter.Eventually.of_forall hbound)
  refine ⟨(integrableOn_iff_integrable_of_support_subset hs).mp hint, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Metric.closedBall (0 : Euclidean d) (2*r)) (fun x hx => by
    apply houter x
    have : ¬ ‖x‖ ≤ 2*r := by simpa using hx
    linarith)]
  apply (norm_setIntegral_le_of_norm_le_const_ae
    (s := Metric.closedBall (0 : Euclidean d) (2*r)) measure_closedBall_lt_top
    (Filter.Eventually.of_forall hbound)).trans_eq
  rw [volume.addHaar_real_closedBall' _ (by positivity), finrank_euclideanSpace_fin, mul_pow]
  field_simp [hr.ne']

/-- The difference of two sharp ball cutoffs is the sharp annulus indicator
almost everywhere. The positive inner radius avoids the singleton sphere
exception in dimension zero as well. -/
theorem sharp_cutoffs_eq_annulus_ae (d : ℕ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (fun x : Euclidean d =>
      (Metric.ball 0 R).indicator (fun _ => (1 : ℂ)) x -
        (Metric.ball 0 r).indicator (fun _ => (1 : ℂ)) x) =ᵐ[volume]
      {x : Euclidean d | r < ‖x‖ ∧ ‖x‖ < R}.indicator (fun _ => (1 : ℂ)) := by
  classical
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    (volume.addHaar_sphere_of_ne_zero (0 : Euclidean d) hr.ne')] with x hx
  have hne : ‖x‖ ≠ r := by simpa using hx
  by_cases hR : ‖x‖ < R <;> by_cases hxr : ‖x‖ < r
  · have hn : ¬ r < ‖x‖ := by linarith
    simp [Metric.mem_ball, dist_zero_right, hR, hxr, hn]
  · have hn : r < ‖x‖ := lt_of_le_of_ne (le_of_not_gt hxr) hne.symm
    simp [Metric.mem_ball, dist_zero_right, hR, hxr, hn]
  · exact (hR (hxr.trans hrR)).elim
  · simp [Metric.mem_ball, dist_zero_right, hR, hxr]

/-- Bump cancellation bounds the smooth difference of two fixed radial
cutoffs. Comparing each endpoint with a sharp ball costs only one uniformly
controlled shell, even when the shells overlap. -/
theorem annular_necessity :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.necessityType := by
  intro d K k hk hcancel
  classical
  have hfunc : SmoothKernelBounds k := hk.2
  obtain ⟨C, hC, hsize⟩ := kernel_size hfunc
  obtain ⟨N, hN⟩ := hcancel
  let b : ContDiffBump (0 : Euclidean d) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let a : Euclidean d → ℂ := fun x => (b x : ℂ)
  have ha : ContDiff ℝ ∞ a := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hac : HasCompactSupport a :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  let φ := euclideanTest a ha hac
  obtain ⟨B, hB, hbound⟩ := bump_cancellation_fixed_test K hN φ
  let D := C * 2^d * volume.real (Metric.closedBall (0 : Euclidean d) 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨2*B + 2*D, by positivity, ?_⟩
  intro r R hr hrR
  have hR : 0 < R := hr.trans hrR
  refine ⟨integrableOn_annulus hfunc hr, ?_⟩
  let ψ := dilateTest R hR.ne' φ - dilateTest r hr.ne' φ
  have hψfun : ⇑(testSchwartz ℂ ψ) =
      fun x : Euclidean d => a (R⁻¹ • x) - a (r⁻¹ • x) := by
    funext x
    change a ((EuclideanSpace.equiv (Fin d) ℝ).symm
      (R⁻¹ • (EuclideanSpace.equiv (Fin d) ℝ) x)) -
        a ((EuclideanSpace.equiv (Fin d) ℝ).symm
          (r⁻¹ • (EuclideanSpace.equiv (Fin d) ℝ) x)) = _
    rw [map_smul, map_smul, ContinuousLinearEquiv.symm_apply_apply]
  have hψzero : 0 ∉ tsupport (testSchwartz ℂ ψ) := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    have hnorm : ∀ᶠ x : Euclidean d in 𝓝 0, ‖x‖ < r := by
      filter_upwards [Metric.ball_mem_nhds (0 : Euclidean d) hr] with x hx
      simpa using hx
    filter_upwards [hnorm] with x hx
    have hbR : b (R⁻¹ • x) = 1 := by
      apply b.one_of_mem_closedBall
      simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hR)]
      exact (inv_mul_le_one₀ hR).mpr (hx.le.trans hrR.le)
    have hbr : b (r⁻¹ • x) = 1 := by
      apply b.one_of_mem_closedBall
      simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_le_one₀ hr).mpr hx.le
    change testSchwartz ℂ ψ x = 0
    rw [show testSchwartz ℂ ψ x = a (R⁻¹ • x) - a (r⁻¹ • x) from congrFun hψfun x]
    simp [a, hbR, hbr]
  have hψpair : ‖∫ x, k x * (a (R⁻¹ • x) - a (r⁻¹ • x))‖ ≤ 2*B := by
    have hp := (hk.1 ψ hψzero).2
    rw [hψfun] at hp
    rw [← hp]
    change ‖K (dilateTest R hR.ne' φ - dilateTest r hr.ne' φ)‖ ≤ _
    rw [map_sub]
    exact (norm_sub_le _ _).trans ((add_le_add (hbound R hR) (hbound r hr)).trans_eq (by ring))
  let er := fun x : Euclidean d => k x *
    ((Metric.ball (0 : Euclidean d) r).indicator (fun _ => (1 : ℂ)) x - a (r⁻¹ • x))
  let eR := fun x : Euclidean d => k x *
    ((Metric.ball (0 : Euclidean d) R).indicator (fun _ => (1 : ℂ)) x - a (R⁻¹ • x))
  have her : Integrable er ∧ ‖∫ x, er x‖ ≤ D :=
    cutoff_error_bound hfunc C hC hsize b rfl rfl r hr
  have heR : Integrable eR ∧ ‖∫ x, eR x‖ ≤ D :=
    cutoff_error_bound hfunc C hC hsize b rfl rfl R hR
  have hψint : Integrable (fun x : Euclidean d => k x * (a (R⁻¹ • x) - a (r⁻¹ • x))) := by
    simpa only [hψfun] using (hk.1 ψ hψzero).1
  have hidentity : (∫ x in {x : Euclidean d | r < ‖x‖ ∧ ‖x‖ < R}, k x) =
      (∫ x, k x * (a (R⁻¹ • x) - a (r⁻¹ • x))) +
        (∫ x, eR x) - (∫ x, er x) := by
    rw [← integral_add hψint heR.1]
    change _ = (∫ x, ((fun y => k y * (a (R⁻¹ • y) - a (r⁻¹ • y))) + eR) x) - ∫ x, er x
    rw [← integral_sub (hψint.add heR.1) her.1]
    have hmset : MeasurableSet {x : Euclidean d | r < ‖x‖ ∧ ‖x‖ < R} :=
      (measurableSet_lt measurable_const measurable_norm).inter
        (measurableSet_lt measurable_norm measurable_const)
    rw [← integral_indicator hmset]
    apply integral_congr_ae
    filter_upwards [sharp_cutoffs_eq_annulus_ae d hr hrR] with x hx
    have hm : {x : Euclidean d | r < ‖x‖ ∧ ‖x‖ < R}.indicator k x =
        k x * {x : Euclidean d | r < ‖x‖ ∧ ‖x‖ < R}.indicator (fun _ => (1 : ℂ)) x := by
      by_cases h : r < ‖x‖ ∧ ‖x‖ < R <;> simp [indicator, h]
    rw [hm, ← hx]
    dsimp [eR, er]
    ring
  rw [hidentity]
  calc
    ‖(∫ x, k x * (a (R⁻¹ • x) - a (r⁻¹ • x))) + (∫ x, eR x) - (∫ x, er x)‖ ≤
        ‖∫ x, k x * (a (R⁻¹ • x) - a (r⁻¹ • x))‖ + ‖∫ x, eR x‖ + ‖∫ x, er x‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2*B + D + D := add_le_add (add_le_add hψpair heR.2) her.2
    _ = 2*B + 2*D := by ring

/-- Empty annuli and empty off-zero domains give the full criterion in
zero dimension, using the mass-one singleton Fourier convention upstream. -/
theorem zero_dimension_criterion :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.zeroDimensionType := by
  intro k
  have hz (x : Euclidean 0) : x = 0 := Subsingleton.elim _ _
  constructor
  · refine ⟨0, le_rfl, ?_⟩
    intro r R hr _
    have he : {x : Euclidean 0 | r < ‖x‖ ∧ ‖x‖ < R} = ∅ := by
      ext x
      simp [hz x, hr.not_gt]
    simp [he]
  · refine ⟨0, ?_, zero_dimension_multiplier 0⟩
    constructor
    · intro φ hφ
      have hzero : testSchwartz ℂ φ = 0 := by
        ext x
        change testSchwartz ℂ φ x = 0
        rw [hz x]
        exact image_eq_zero_of_notMem_tsupport hφ
      simp [hzero]
    · constructor
      · have he : ({0}ᶜ : Set (Euclidean 0)) = ∅ := by
          ext x
          simp [hz x]
        rw [he]
        exact contDiffOn_empty
      · intro n w
        refine ⟨0, le_rfl, ?_⟩
        intro x hx
        exact (hx (hz x)).elim

/-- The radial majorant for the first moment of a kernel of size |x|⁻ᵈ.
The polar integral is finite even when the kernel itself is not locally integrable. -/
theorem inverse_power_ball {d : ℕ} (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : Euclidean d => (‖x‖ ^ (d-1))⁻¹) (Metric.ball 0 r) ∧
    (∫ x : Euclidean d in Metric.ball 0 r, (‖x‖ ^ (d-1))⁻¹) =
      (d : ℝ) * volume.real (Metric.ball (0 : Euclidean d) 1) * r := by
  have : Nontrivial (Euclidean d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hd)
  have hrad (y : ℝ) (hy : 0 < y) : y ^ (d-1) * (y ^ (d-1))⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ hy.ne')
  have hi : IntegrableOn (fun x : Euclidean d => (‖x‖ ^ (d-1))⁻¹) (Metric.ball 0 r) := by
    apply (integrableOn_fun_norm_addHaar volume (f := fun y : ℝ => (y ^ (d-1))⁻¹)).2
    simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using
      (integrableOn_const (C := (1 : ℝ)) (s := Ioo 0 r) (by simp)).congr_fun
        (fun y hy => (hrad y hy.1).symm) measurableSet_Ioo
  refine ⟨hi, ?_⟩
  let f : ℝ → ℝ := (Iio r).indicator (fun y => (y ^ (d-1))⁻¹)
  have heq : (fun x : Euclidean d => (Metric.ball 0 r).indicator
      (fun x => (‖x‖ ^ (d-1))⁻¹) x) = (fun x => f ‖x‖) := by
    funext x
    simp [f, indicator, Metric.mem_ball, dist_zero_right]
  rw [← integral_indicator measurableSet_ball, heq, integral_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul]
  have heq2 : (∫ y in Ioi (0 : ℝ), y ^ (d-1) * f y) = r := by
    have he : (fun y => y ^ (d-1) * f y) =ᵐ[volume.restrict (Ioi 0)]
        (Iio r).indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      by_cases hyr : y < r <;> simp [f, indicator, hyr, hrad y hy]
    rw [integral_congr_ae he, setIntegral_indicator measurableSet_Iio]
    rw [show Ioi (0 : ℝ) ∩ Iio r = Ioo 0 r by ext y; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]]
    simp [hr.le]
  rw [heq2]
  ring

/-- An explicit scale-invariant first-moment estimate. -/
theorem kernel_first_moment {d : ℕ} (hd : 0 < d) {k : Euclidean d → ℂ}
    (hk : SmoothKernelBounds k) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x, x ≠ 0 → ‖k x‖ ≤ C * (‖x‖ ^ d)⁻¹) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => ‖k x‖ * ‖x‖) (Metric.ball 0 r) ∧
    (∫ x in Metric.ball 0 r, ‖k x‖ * ‖x‖) ≤
      (C * (d : ℝ) * volume.real (Metric.ball (0 : Euclidean d) 1)) * r := by
  have hm := (measurable_of_continuousOn_compl_singleton 0 hk.1.continuousOn).norm.mul measurable_norm
  have hmajor (x : Euclidean d) : ‖k x‖ * ‖x‖ ≤ C * (‖x‖ ^ (d-1))⁻¹ := by
    by_cases hx : x = 0
    · simp only [hx, norm_zero, mul_zero]
      positivity
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    calc
      ‖k x‖ * ‖x‖ ≤ (C * (‖x‖ ^ d)⁻¹) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (hb x hx) (norm_nonneg _)
      _ = C * (‖x‖ ^ (d-1))⁻¹ := by
        have hp : ‖x‖ ^ (d-1) * ‖x‖ = ‖x‖ ^ d := by
          rw [← pow_succ, Nat.sub_add_cancel hd]
        rw [← hp]
        field_simp
  obtain ⟨hi, he⟩ := inverse_power_ball hd hr
  have hg := hi.const_mul C
  have hi' : IntegrableOn (fun x => ‖k x‖ * ‖x‖) (Metric.ball 0 r) :=
    hg.mono' hm.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hmajor x)
  refine ⟨hi', ?_⟩
  calc
    (∫ x in Metric.ball 0 r, ‖k x‖ * ‖x‖) ≤
        ∫ x in Metric.ball 0 r, C * (‖x‖ ^ (d-1))⁻¹ := integral_mono hi' hg hmajor
    _ = _ := by rw [integral_const_mul, he]; ring

/-- The cancellation subtraction is controlled by the global derivative bound. -/
theorem kernel_remainder_bound {d : ℕ} (hd : 0 < d) {k : Euclidean d → ℂ}
    (hk : SmoothKernelBounds k) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x, x ≠ 0 → ‖k x‖ ≤ C * (‖x‖ ^ d)⁻¹)
    (f : Euclidean d → ℂ) (hf : Differentiable ℝ f) (B : ℝ) (hB : 0 ≤ B)
    (hder : ∀ x, ‖fderiv ℝ f x‖ ≤ B) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => k x * (f x - f 0)) (Metric.ball 0 r) ∧
    ‖∫ x in Metric.ball 0 r, k x * (f x - f 0)‖ ≤
      (C * (d : ℝ) * volume.real (Metric.ball (0 : Euclidean d) 1)) * B * r := by
  have hdiff (x : Euclidean d) : ‖f x - f 0‖ ≤ B * ‖x‖ := by
    simpa using (convex_univ : Convex ℝ (univ : Set (Euclidean d))).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hf x) (fun x _ => hder x) (mem_univ 0) (mem_univ x)
  have hm : AEStronglyMeasurable (fun x => k x * (f x - f 0)) volume :=
    (measurable_of_continuousOn_compl_singleton 0 hk.1.continuousOn).aestronglyMeasurable.mul
    (hf.continuous.aestronglyMeasurable.sub aestronglyMeasurable_const)
  obtain ⟨hi, hmoment⟩ := kernel_first_moment hd hk C hC hb hr
  have hpoint (x : Euclidean d) : ‖k x * (f x - f 0)‖ ≤ B * (‖k x‖ * ‖x‖) := by
    rw [norm_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hdiff x) (norm_nonneg (k x))]
  have hi' : IntegrableOn (fun x => k x * (f x - f 0)) (Metric.ball 0 r) :=
    (hi.const_mul B).mono' hm.restrict (Filter.Eventually.of_forall hpoint)
  refine ⟨hi', ?_⟩
  calc
    ‖∫ x in Metric.ball 0 r, k x * (f x - f 0)‖ ≤
        ∫ x in Metric.ball 0 r, ‖k x * (f x - f 0)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Metric.ball 0 r, B * (‖k x‖ * ‖x‖) := integral_mono hi'.norm (hi.const_mul B) hpoint
    _ = B * (∫ x in Metric.ball 0 r, ‖k x‖ * ‖x‖) := integral_const_mul _ _
    _ ≤ B * ((C * (d : ℝ) * volume.real (Metric.ball (0 : Euclidean d) 1)) * r) :=
      mul_le_mul_of_nonneg_left hmoment hB
    _ = _ := by ring

/-- The finite part is a genuine continuous scalar-linear functional on Schwartz
space. No annular cancellation is needed to construct it. -/
theorem finite_part_tempered {d : ℕ} (hd : 0 < d) {k : Euclidean d → ℂ}
    (hk : SmoothKernelBounds k) :
    ∃ U : Tempered ℂ d, ∀ φ : Schwartz ℂ d,
      IntegrableOn (fun x => k x * (φ x - φ 0)) (Metric.ball 0 1) ∧
      IntegrableOn (fun x => k x * φ x) (Metric.ball 0 1)ᶜ ∧
      U φ = (∫ x in Metric.ball 0 1, k x * (φ x - φ 0)) +
        ∫ x in (Metric.ball 0 1)ᶜ, k x * φ x := by
  classical
  obtain ⟨C, hC, hsize⟩ := kernel_size hk
  let D := C * (d : ℝ) * volume.real (Metric.ball (0 : Euclidean d) 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrem (φ : Schwartz ℂ d) := kernel_remainder_bound hd hk C hC hsize
    φ (φ.smooth'.differentiable (by simp)) (SchwartzMap.seminorm ℂ 0 1 φ)
    (apply_nonneg _ _) (fun x => by
      rw [← norm_iteratedFDeriv_one]
      exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ 1 x) zero_lt_one
  let V : Tempered ℂ d := SchwartzMap.mkCLMtoNormedSpace
    (fun φ : Schwartz ℂ d => ∫ x in Metric.ball 0 1, k x * (φ x - φ 0))
    (fun φ ψ => by
      have he : (fun x => k x * ((φ+ψ) x - (φ+ψ) 0)) =
          (fun x => k x * (φ x - φ 0) + k x * (ψ x - ψ 0)) := by
        funext x; simp only [add_apply]; ring
      rw [he]
      exact integral_add (hrem φ).1 (hrem ψ).1)
    (fun c φ => by
      have he : (fun x => k x * ((c • φ) x - (c • φ) 0)) =
          (fun x => c * (k x * (φ x - φ 0))) := by
        funext x; simp only [smul_apply, smul_eq_mul]; ring
      rw [he]
      exact integral_const_mul c _)
    (by
      refine ⟨{(0,1)}, D, hD, ?_⟩
      intro φ
      simpa only [Finset.sup_singleton, mul_one, SchwartzMap.schwartzSeminormFamily_apply, D] using (hrem φ).2)
  let f : Euclidean d → ℂ := (Metric.ball 0 1)ᶜ.indicator k
  have hf : AEStronglyMeasurable f volume :=
    (measurable_of_continuousOn_compl_singleton 0 hk.1.continuousOn).aestronglyMeasurable.indicator
      measurableSet_ball.compl
  have hfb (x : Euclidean d) : ‖f x‖ ≤ C := by
    by_cases hx : x ∈ Metric.ball (0 : Euclidean d) 1
    · simpa [f, hx] using hC
    · have hxnorm : 1 ≤ ‖x‖ := by simpa using hx
      have hx0 : x ≠ 0 := by intro he; simp [he] at hxnorm; linarith
      simpa [f, hx] using (hsize x hx0).trans
        ((mul_le_mul_of_nonneg_left
          (inv_le_one_of_one_le₀ (one_le_pow₀ hxnorm)) hC).trans_eq (mul_one C))
  obtain ⟨W, hW⟩ := bounded_regular_tempered f hf C hC hfb
  refine ⟨V+W, ?_⟩
  intro φ
  have he : (fun x => f x * φ x) = (Metric.ball 0 1)ᶜ.indicator (fun x => k x * φ x) := by
    funext x
    by_cases hx : x ∈ Metric.ball (0 : Euclidean d) 1 <;> simp [f, hx]
  have hi : IntegrableOn (fun x => k x * φ x) (Metric.ball 0 1)ᶜ := by
    rw [← integrable_indicator_iff measurableSet_ball.compl, ← he]
    exact (hW φ).1
  refine ⟨(hrem φ).1, hi, ?_⟩
  change V φ + W φ = _
  rw [(hW φ).2, he, integral_indicator measurableSet_ball.compl]
  rfl

/-- Restriction of the finite part agrees with the original function off zero,
with ordinary integrability there. -/
theorem finite_part_agrees {d : ℕ} {k : Euclidean d → ℂ} (U : Tempered ℂ d)
    (hU : ∀ φ : Schwartz ℂ d,
      IntegrableOn (fun x => k x * (φ x - φ 0)) (Metric.ball 0 1) ∧
      IntegrableOn (fun x => k x * φ x) (Metric.ball 0 1)ᶜ ∧
      U φ = (∫ x in Metric.ball 0 1, k x * (φ x - φ 0)) +
        ∫ x in (Metric.ball 0 1)ᶜ, k x * φ x) :
    AgreesOffZero (temperedRestriction U) k := by
  intro φ hφ
  have hz : testSchwartz ℂ φ 0 = 0 := image_eq_zero_of_notMem_tsupport hφ
  obtain ⟨hi, ho, he⟩ := hU (testSchwartz ℂ φ)
  simp only [hz, sub_zero] at hi he
  have hint : Integrable (fun x => k x * testSchwartz ℂ φ x) :=
    (integrableOn_univ.mp ((hi.union ho).mono_set (by simp)))
  exact ⟨hint, he.trans (integral_add_compl measurableSet_ball hint)⟩

/-- The annular hypothesis also bounds differences of sharp ball cutoffs,
regardless of the ordering of their radii. -/
theorem annular_ball_difference {d : ℕ} {k : Euclidean d → ℂ}
    (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ r R : ℝ, 0 < r → r < R →
      IntegrableOn k {x | r < ‖x‖ ∧ ‖x‖ < R} ∧
        ‖∫ x in {x | r < ‖x‖ ∧ ‖x‖ < R}, k x‖ ≤ A)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    Integrable (fun x : Euclidean d => k x *
      ((Metric.ball 0 R).indicator (fun _ => (1 : ℂ)) x -
        (Metric.ball 0 r).indicator (fun _ => (1 : ℂ)) x)) ∧
    ‖∫ x : Euclidean d, k x *
      ((Metric.ball 0 R).indicator (fun _ => (1 : ℂ)) x -
        (Metric.ball 0 r).indicator (fun _ => (1 : ℂ)) x)‖ ≤ A := by
  classical
  have hordered (a b : ℝ) (ha0 : 0 < a) (hab : a < b) :
      Integrable (fun x : Euclidean d => k x *
        ((Metric.ball 0 b).indicator (fun _ => (1 : ℂ)) x -
          (Metric.ball 0 a).indicator (fun _ => (1 : ℂ)) x)) ∧
      ‖∫ x : Euclidean d, k x *
        ((Metric.ball 0 b).indicator (fun _ => (1 : ℂ)) x -
          (Metric.ball 0 a).indicator (fun _ => (1 : ℂ)) x)‖ ≤ A := by
    have hm : MeasurableSet {x : Euclidean d | a < ‖x‖ ∧ ‖x‖ < b} :=
      (measurableSet_lt measurable_const measurable_norm).inter
        (measurableSet_lt measurable_norm measurable_const)
    have he : (fun x : Euclidean d => k x *
        ((Metric.ball 0 b).indicator (fun _ => (1 : ℂ)) x -
          (Metric.ball 0 a).indicator (fun _ => (1 : ℂ)) x)) =ᵐ[volume]
        {x : Euclidean d | a < ‖x‖ ∧ ‖x‖ < b}.indicator k := by
      filter_upwards [sharp_cutoffs_eq_annulus_ae d ha0 hab] with x hx
      rw [hx]
      by_cases h : a < ‖x‖ ∧ ‖x‖ < b <;> simp [indicator, h]
    obtain ⟨hi, hb⟩ := ha a b ha0 hab
    refine ⟨(hi.integrable_indicator hm).congr he.symm, ?_⟩
    simpa only [integral_congr_ae he, integral_indicator hm] using hb
  rcases lt_trichotomy r R with h | h | h
  · exact hordered r R hr h
  · subst R
    simpa using hA
  · have he : (fun x : Euclidean d => k x *
        ((Metric.ball 0 R).indicator (fun _ => (1 : ℂ)) x -
          (Metric.ball 0 r).indicator (fun _ => (1 : ℂ)) x)) =
        -(fun x : Euclidean d => k x *
        ((Metric.ball 0 r).indicator (fun _ => (1 : ℂ)) x -
          (Metric.ball 0 R).indicator (fun _ => (1 : ℂ)) x)) := by
      funext x; simp only [Pi.neg_apply]; ring
    rw [he]
    obtain ⟨hi, hb⟩ := hordered R r hR h
    refine ⟨hi.neg, ?_⟩
    change ‖∫ x : Euclidean d, -(k x *
      ((Metric.ball 0 r).indicator (fun _ => (1 : ℂ)) x -
        (Metric.ball 0 R).indicator (fun _ => (1 : ℂ)) x))‖ ≤ A
    rw [integral_neg, norm_neg]
    exact hb

/-- At any radius containing the support, the finite part splits into the
small Taylor remainder and one bounded annular correction. -/
theorem finite_part_at_scale {d : ℕ} {k : Euclidean d → ℂ} (U : Tempered ℂ d)
    (hU : ∀ φ : Schwartz ℂ d,
      IntegrableOn (fun x => k x * (φ x - φ 0)) (Metric.ball 0 1) ∧
      IntegrableOn (fun x => k x * φ x) (Metric.ball 0 1)ᶜ ∧
      U φ = (∫ x in Metric.ball 0 1, k x * (φ x - φ 0)) +
        ∫ x in (Metric.ball 0 1)ᶜ, k x * φ x)
    (φ : Schwartz ℂ d) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ x, r < ‖x‖ → φ x = 0)
    (hi : IntegrableOn (fun x => k x * (φ x - φ 0)) (Metric.ball 0 r))
    (hq : Integrable (fun x : Euclidean d => k x *
      ((Metric.ball 0 r).indicator (fun _ => (1 : ℂ)) x -
        (Metric.ball 0 1).indicator (fun _ => (1 : ℂ)) x))) :
    U φ = (∫ x in Metric.ball 0 r, k x * (φ x - φ 0)) + φ 0 *
      (∫ x : Euclidean d, k x *
        ((Metric.ball 0 r).indicator (fun _ => (1 : ℂ)) x -
          (Metric.ball 0 1).indicator (fun _ => (1 : ℂ)) x)) := by
  classical
  let q := fun x : Euclidean d => k x *
    ((Metric.ball 0 r).indicator (fun _ => (1 : ℂ)) x -
      (Metric.ball 0 1).indicator (fun _ => (1 : ℂ)) x)
  obtain ⟨hi1, ho1, hpair⟩ := hU φ
  calc
    U φ = (∫ x in Metric.ball 0 1, k x * (φ x - φ 0)) +
        ∫ x in (Metric.ball 0 1)ᶜ, k x * φ x := hpair
    _ = ∫ x, (Metric.ball 0 1).indicator (fun x => k x * (φ x - φ 0)) x +
        (Metric.ball 0 1)ᶜ.indicator (fun x => k x * φ x) x := by
      rw [integral_add (hi1.integrable_indicator measurableSet_ball)
        (ho1.integrable_indicator measurableSet_ball.compl),
        integral_indicator measurableSet_ball, integral_indicator measurableSet_ball.compl]
    _ = ∫ x, (Metric.ball 0 r).indicator (fun x => k x * (φ x - φ 0)) x + φ 0 * q x := by
      apply integral_congr_ae
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp
        (volume.addHaar_sphere_of_ne_zero (0 : Euclidean d) hr.ne')] with x hx
      have hne : ‖x‖ ≠ r := by simpa using hx
      have hz (hx : x ∉ Metric.ball (0 : Euclidean d) r) : φ x = 0 := by
        apply hsupp x
        have hn : r ≤ ‖x‖ := by simpa using hx
        exact lt_of_le_of_ne hn hne.symm
      by_cases hx1 : x ∈ Metric.ball (0 : Euclidean d) 1 <;>
        by_cases hxr : x ∈ Metric.ball (0 : Euclidean d) r <;>
        simp only [q, indicator_apply, mem_compl_iff, hx1, hxr, not_true_eq_false, not_false_eq_true, ite_true, ite_false]
          <;> (try rw [hz hxr]) <;> ring
    _ = _ := by
      rw [integral_add (hi.integrable_indicator measurableSet_ball) (hq.const_mul (φ 0)),
        integral_indicator measurableSet_ball, integral_const_mul]

/-- Annular cancellation gives uniform normalized C¹ bump pairings for the
finite-part distribution, at every positive scale. -/
theorem finite_part_bumps {d : ℕ} (hd : 0 < d) {k : Euclidean d → ℂ}
    (hk : SmoothKernelBounds k) (ha : AnnularCancellation k) (U : Tempered ℂ d)
    (hU : ∀ φ : Schwartz ℂ d,
      IntegrableOn (fun x => k x * (φ x - φ 0)) (Metric.ball 0 1) ∧
      IntegrableOn (fun x => k x * φ x) (Metric.ball 0 1)ᶜ ∧
      U φ = (∫ x in Metric.ball 0 1, k x * (φ x - φ 0)) +
        ∫ x in (Metric.ball 0 1)ᶜ, k x * φ x) :
    BumpCancellation (temperedRestriction U) 1 := by
  obtain ⟨C, hC, hsize⟩ := kernel_size hk
  obtain ⟨A, hA, ha⟩ := ha
  let D := C * (d : ℝ) * volume.real (Metric.ball (0 : Euclidean d) 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D+A, add_nonneg hD hA, ?_⟩
  intro φ hφ r hr
  let ψ := testSchwartz ℂ (dilateTest r hr.ne' φ)
  have hψfun : ⇑ψ = fun x : Euclidean d => testSchwartz ℂ φ (r⁻¹ • x) := by
    funext x
    simp only [ψ, testSchwartz_apply, dilateTest_apply, map_smul]
  have hder (x : Euclidean d) : ‖fderiv ℝ ψ x‖ ≤ r⁻¹ := by
    rw [hψfun, fderiv_comp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    have hb := hφ.2 1 le_rfl (r⁻¹ • x)
    rw [norm_iteratedFDeriv_one] at hb
    exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hr.le)).trans_eq (mul_one _)
  have hsupp (x : Euclidean d) (hx : r < ‖x‖) : ψ x = 0 := by
    rw [show ψ x = testSchwartz ℂ φ (r⁻¹ • x) from congrFun hψfun x]
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hn : ‖r⁻¹ • x‖ ≤ 1 := by simpa using hφ.1 h
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hn
    have : ‖x‖ ≤ r := (inv_mul_le_one₀ hr).mp hn
    exact hx.not_ge this
  have hψ0 : ‖ψ 0‖ ≤ 1 := by
    have he : ψ 0 = testSchwartz ℂ φ 0 := by simp only [hψfun, smul_zero]
    rw [he]
    simpa only [norm_iteratedFDeriv_zero] using hφ.2 0 (by omega) (0 : Euclidean d)
  obtain ⟨hi, hrem⟩ := kernel_remainder_bound hd hk C hC hsize ψ
    (ψ.smooth'.differentiable (by simp)) r⁻¹ (inv_nonneg.mpr hr.le) hder hr
  have hremD : ‖∫ x in Metric.ball 0 r, k x * (ψ x - ψ 0)‖ ≤ D := by
    simpa only [mul_assoc, inv_mul_cancel₀ hr.ne', mul_one, D] using hrem
  obtain ⟨hq, hqbound⟩ := annular_ball_difference A hA ha zero_lt_one hr
  have hp := finite_part_at_scale U hU ψ hr hsupp hi hq
  change ‖U ψ‖ ≤ _
  rw [hp]
  apply (norm_add_le _ _).trans
  apply add_le_add hremD
  rw [norm_mul]
  exact (mul_le_mul hψ0 hqbound (norm_nonneg _) zero_le_one).trans_eq (one_mul A)

/-- Full annular cancellation criterion in every dimension. The finite-part
construction supplies the extension; bump cancellation supplies its global
smooth bounded multiplier through the accepted equivalence. -/
theorem annular_criterion :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.annularCriterionType := by
  intro d k hk
  constructor
  · rintro ⟨K, hK⟩
    obtain ⟨N, _, hN⟩ := bounded_to_bumps d K hK.2.hasBoundedFourier
    exact annular_necessity d K k hK.1 ⟨N, hN⟩
  · intro ha
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst d
      exact (zero_dimension_criterion k).2
    · obtain ⟨U, hU⟩ := finite_part_tempered hd hk
      let K := temperedRestriction U
      have hkernel : KernelBounds K k := ⟨finite_part_agrees U hU, hk⟩
      have hb : BumpCancellation K 1 := finite_part_bumps hd hk ha U hU
      exact ⟨K, hkernel, bump_to_symbol d K k hkernel
        ⟨d+1, by omega, hb.mono (by omega)⟩⟩

end ExpandedFA.PartIV.CzAnnularCriterion



open MeasureTheory Set TopologicalSpace Function
open scoped SchwartzMap ContDiff FourierTransform Topology
namespace ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open ExpandedFA.Distributions ExpandedFA.Fourier ExpandedFA.Fourier.Examples

@[simp] theorem complexify_apply {d : ℕ} (u : KernelDistribution d) (φ) :
    complexify u φ = (u (realTest φ) : ℂ) + Complex.I * (u (imagTest φ) : ℂ) := rfl
@[simp] theorem restrict_apply {d : ℕ}
    (K : ExpandedFA.SingularIntegrals.KernelDistribution d) (φ) :
    restrict K φ = (K (ofRealTest φ)).re := rfl

@[simp] theorem realTest_ofRealTest {d : ℕ} (φ : Tests ℝ (⊤ : Opens (Domain d))) :
    realTest (ofRealTest φ) = φ := by ext x; simp
@[simp] theorem imagTest_ofRealTest {d : ℕ} (φ : Tests ℝ (⊤ : Opens (Domain d))) :
    imagTest (ofRealTest φ) = 0 := by ext x; simp
@[simp] theorem complexify_ofRealTest {d : ℕ} (u : KernelDistribution d)
    (φ : Tests ℝ (⊤ : Opens (Domain d))) : complexify u (ofRealTest φ) = (u φ : ℂ) := by simp
@[simp] theorem restrict_complexify {d : ℕ} (u : KernelDistribution d) :
    restrict (complexify u) = u := by ext φ; simp

theorem testSchwartz_postcomp {𝕜 𝕜' : Type} [RCLike 𝕜] [RCLike 𝕜'] {d : ℕ}
    (T : 𝕜 →L[ℝ] 𝕜') (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    ⇑(testSchwartz 𝕜' (TestFunction.postcompCLM T φ)) = T ∘ testSchwartz 𝕜 φ := rfl

theorem normalized_postcomp {𝕜 𝕜' : Type} [RCLike 𝕜] [RCLike 𝕜'] {d N : ℕ}
    (T : 𝕜 →L[ℝ] 𝕜') (hT : ‖T‖ ≤ 1)
    (φ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (hs : tsupport (testSchwartz 𝕜 φ) ⊆ Metric.closedBall 0 1)
    (hb : ∀ n ≤ N, ∀ x : Euclidean d, ‖iteratedFDeriv ℝ n (testSchwartz 𝕜 φ) x‖ ≤ 1) :
    tsupport (testSchwartz 𝕜' (TestFunction.postcompCLM T φ)) ⊆ Metric.closedBall 0 1 ∧
      ∀ n ≤ N, ∀ x : Euclidean d,
        ‖iteratedFDeriv ℝ n (testSchwartz 𝕜' (TestFunction.postcompCLM T φ)) x‖ ≤ 1 := by
  rw [testSchwartz_postcomp]
  refine ⟨(tsupport_comp_subset (map_zero T) _).trans hs, ?_⟩
  intro n hn x
  have hd : ContDiffAt ℝ ∞ (⇑(testSchwartz 𝕜 φ)) x := (testSchwartz 𝕜 φ).smooth'.contDiffAt
  rw [T.iteratedFDeriv_comp_left (f := ⇑(testSchwartz 𝕜 φ)) hd (by simp)]
  exact (T.norm_compContinuousMultilinearMap_le _).trans
    ((mul_le_mul hT (hb n hn x) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem NormalizedBump.ofReal {d N : ℕ} {φ : Tests ℝ (⊤ : Opens (Domain d))}
    (h : NormalizedBump N φ) :
    ExpandedFA.SingularIntegrals.NormalizedBump N (ofRealTest φ) :=
  normalized_postcomp Complex.ofRealCLM (by simp) φ h.1 h.2

theorem NormalizedBump.real {d N : ℕ} {φ : Tests ℂ (⊤ : Opens (Domain d))}
    (h : ExpandedFA.SingularIntegrals.NormalizedBump N φ) :
    NormalizedBump N (realTest φ) :=
  normalized_postcomp Complex.reCLM (by simp) φ h.1 h.2

theorem NormalizedBump.imag {d N : ℕ} {φ : Tests ℂ (⊤ : Opens (Domain d))}
    (h : ExpandedFA.SingularIntegrals.NormalizedBump N φ) :
    NormalizedBump N (imagTest φ) :=
  normalized_postcomp Complex.imCLM (by simp) φ h.1 h.2

@[simp] theorem ofRealTest_dilate {d : ℕ} (r : ℝ) (hr : r ≠ 0)
    (φ : Tests ℝ (⊤ : Opens (Domain d))) :
    ofRealTest (dilateTest r hr φ) =
      ExpandedFA.SingularIntegrals.dilateTest r hr (ofRealTest φ) := by ext x; rfl
@[simp] theorem realTest_dilate {d : ℕ} (r : ℝ) (hr : r ≠ 0)
    (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    realTest (ExpandedFA.SingularIntegrals.dilateTest r hr φ) =
      dilateTest r hr (realTest φ) := by ext x; rfl
@[simp] theorem imagTest_dilate {d : ℕ} (r : ℝ) (hr : r ≠ 0)
    (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    imagTest (ExpandedFA.SingularIntegrals.dilateTest r hr φ) =
      dilateTest r hr (imagTest φ) := by ext x; rfl

theorem BumpCancellation.complexify {d N : ℕ} {u : KernelDistribution d}
    (h : BumpCancellation u N) :
    ExpandedFA.SingularIntegrals.BumpCancellation (complexify u) N := by
  obtain ⟨C,hC,hb⟩ := h
  refine ⟨C+C, add_nonneg hC hC, ?_⟩
  intro φ hφ r hr
  simp only [complexify_apply, realTest_dilate, imagTest_dilate]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real]
  exact add_le_add (hb _ (NormalizedBump.real hφ) _ hr) (hb _ (NormalizedBump.imag hφ) _ hr)

theorem BumpCancellation.restrict {d N : ℕ}
    {K : ExpandedFA.SingularIntegrals.KernelDistribution d}
    (h : ExpandedFA.SingularIntegrals.BumpCancellation K N) :
    BumpCancellation (restrict K) N := by
  obtain ⟨C,hC,hb⟩ := h
  refine ⟨C,hC,?_⟩
  intro φ hφ r hr
  rw [restrict_apply, ofRealTest_dilate]
  exact (Complex.abs_re_le_norm _).trans (hb _ (NormalizedBump.ofReal hφ) _ hr)

theorem bumpCancellation_complexify_iff {d N : ℕ} (u : KernelDistribution d) :
    ExpandedFA.SingularIntegrals.BumpCancellation (complexify u) N ↔ BumpCancellation u N :=
  ⟨fun h => by simpa using BumpCancellation.restrict h, BumpCancellation.complexify⟩

@[simp] theorem testSchwartz_ofReal {d : ℕ} (φ : Tests ℝ (⊤ : Opens (Domain d))) (x : Euclidean d) :
    testSchwartz ℂ (ofRealTest φ) x = (testSchwartz ℝ φ x : ℂ) := rfl
@[simp] theorem testSchwartz_real {d : ℕ} (φ : Tests ℂ (⊤ : Opens (Domain d))) (x : Euclidean d) :
    testSchwartz ℝ (realTest φ) x = (testSchwartz ℂ φ x).re := rfl
@[simp] theorem testSchwartz_imag {d : ℕ} (φ : Tests ℂ (⊤ : Opens (Domain d))) (x : Euclidean d) :
    testSchwartz ℝ (imagTest φ) x = (testSchwartz ℂ φ x).im := rfl

theorem tsupport_testSchwartz_postcomp_subset {𝕜 𝕜' : Type} [RCLike 𝕜] [RCLike 𝕜'] {d : ℕ}
    (T : 𝕜 →L[ℝ] 𝕜') (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    tsupport (testSchwartz 𝕜' (TestFunction.postcompCLM T φ)) ⊆ tsupport (testSchwartz 𝕜 φ) := by
  rw [testSchwartz_postcomp]
  exact tsupport_comp_subset (map_zero T) _

theorem AgreesOffZero.restrict {d : ℕ}
    {K : ExpandedFA.SingularIntegrals.KernelDistribution d} {k : Euclidean d → ℝ}
    (h : ExpandedFA.SingularIntegrals.AgreesOffZero K (fun x => (k x : ℂ))) :
    AgreesOffZero (restrict K) k := by
  intro φ hφ
  have hz : 0 ∉ tsupport (testSchwartz ℂ (ofRealTest φ)) :=
    fun hz => hφ (tsupport_testSchwartz_postcomp_subset Complex.ofRealCLM φ hz)
  obtain ⟨hi,he⟩ := h (ofRealTest φ) hz
  have hi' : Integrable (fun x => k x * testSchwartz ℝ φ x) := by
    have ht := Complex.reCLM.integrable_comp hi
    change Integrable (fun x => (((k x : ℂ) * testSchwartz ℂ (ofRealTest φ) x)).re) at ht
    simpa only [testSchwartz_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] using ht
  refine ⟨hi',?_⟩
  rw [restrict_apply, he]
  simp only [testSchwartz_ofReal, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  rfl

theorem AgreesOffZero.complexify {d : ℕ} {u : KernelDistribution d} {k : Euclidean d → ℝ}
    (h : AgreesOffZero u k) :
    ExpandedFA.SingularIntegrals.AgreesOffZero (complexify u) (fun x => (k x : ℂ)) := by
  intro φ hφ
  have hzR : 0 ∉ tsupport (testSchwartz ℝ (realTest φ)) :=
    fun hz => hφ (tsupport_testSchwartz_postcomp_subset Complex.reCLM φ hz)
  have hzI : 0 ∉ tsupport (testSchwartz ℝ (imagTest φ)) :=
    fun hz => hφ (tsupport_testSchwartz_postcomp_subset Complex.imCLM φ hz)
  obtain ⟨hiR,heR⟩ := h (realTest φ) hzR
  obtain ⟨hiI,heI⟩ := h (imagTest φ) hzI
  have he : (fun x => (k x : ℂ) * testSchwartz ℂ φ x) =
      (fun x => ((k x * testSchwartz ℝ (realTest φ) x : ℝ) : ℂ) +
        Complex.I * ((k x * testSchwartz ℝ (imagTest φ) x : ℝ) : ℂ)) := by
    funext x
    simp only [testSchwartz_real, testSchwartz_imag, Complex.ofReal_mul]
    apply Complex.ext <;> simp <;> ring
  rw [he]
  refine ⟨hiR.ofReal.add (hiI.ofReal.const_mul Complex.I), ?_⟩
  simp only [complexify_apply, heR, heI]
  have hR : Integrable (fun x => ((k x * testSchwartz ℝ (realTest φ) x : ℝ) : ℂ)) := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hiR
  have hI : Integrable (fun x => Complex.I * ((k x * testSchwartz ℝ (imagTest φ) x : ℝ) : ℂ)) := by
    simpa only [Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.integrable_comp hiI).const_mul Complex.I
  rw [integral_add hR hI, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]


theorem agreesOffZero_complexify_iff {d : ℕ} (u : KernelDistribution d) (k : Euclidean d → ℝ) :
    ExpandedFA.SingularIntegrals.AgreesOffZero (complexify u) (fun x => (k x : ℂ)) ↔
      AgreesOffZero u k :=
  ⟨fun h => by simpa using AgreesOffZero.restrict h, AgreesOffZero.complexify⟩

def conjTest {d : ℕ} : Tests ℂ (⊤ : Opens (Domain d)) →L[ℝ] Tests ℂ (⊤ : Opens (Domain d)) :=
  TestFunction.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[simp] theorem conjTest_apply {d : ℕ} (φ : Tests ℂ (⊤ : Opens (Domain d))) (x : Domain d) :
    conjTest φ x = starRingEnd ℂ (φ x) := rfl

@[simp] theorem realTest_conjTest {d : ℕ} (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    realTest (conjTest φ) = realTest φ := by ext x; simp
@[simp] theorem imagTest_conjTest {d : ℕ} (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    imagTest (conjTest φ) = -imagTest φ := by ext x; simp
@[simp] theorem complexify_conjTest {d : ℕ} (u : KernelDistribution d)
    (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    complexify u (conjTest φ) = starRingEnd ℂ (complexify u φ) := by
  simp [complexify_apply]

def ofRealSchwartz {d : ℕ} : Schwartz ℝ d →L[ℝ] Schwartz ℂ d :=
  SchwartzMap.postcompCLM Complex.ofRealCLM

def restrictTempered {d : ℕ} (U : Tempered ℂ d) : Tempered ℝ d :=
  Complex.reCLM.comp ((U.restrictScalars ℝ).comp ofRealSchwartz)

@[simp] theorem ofRealSchwartz_testSchwartz {d : ℕ}
    (φ : Tests ℝ (⊤ : Opens (Domain d))) :
    ofRealSchwartz (testSchwartz ℝ φ) = testSchwartz ℂ (ofRealTest φ) := by ext x; rfl

theorem extendsKernel_restrictTempered {d : ℕ} {u : KernelDistribution d}
    {U : Tempered ℂ d} (hU : ExpandedFA.SingularIntegrals.ExtendsKernel U (complexify u)) :
    ∀ φ : Tests ℝ (⊤ : Opens (Domain d)), restrictTempered U (testSchwartz ℝ φ) = u φ := by
  intro φ
  change (U (ofRealSchwartz (testSchwartz ℝ φ))).re = u φ
  rw [ofRealSchwartz_testSchwartz, hU, complexify_ofRealTest, Complex.ofReal_re]
end ExpandedFA.PartIV.CzAnnularCriterion.RealScalar



open MeasureTheory FourierTransform
open scoped SchwartzMap ComplexConjugate RealInnerProductSpace
namespace RealFourierBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def conjugateSchwartz : 𝓢(E, ℂ) →L[ℝ] 𝓢(E, ℂ) :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[simp] theorem conjugateSchwartz_apply (f : 𝓢(E, ℂ)) (x : E) :
    conjugateSchwartz f x = conj (f x) := rfl

theorem fourier_conjugate_fun (f : E → ℂ) (x : E) :
    𝓕 (fun y => conj (f y)) x = conj (𝓕⁻ f x) := by
  rw [Real.fourier_eq', Real.fourierInv_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, map_mul, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

theorem fourier_conjugate_schwartz (f : 𝓢(E, ℂ)) :
    𝓕 (conjugateSchwartz f) = conjugateSchwartz (𝓕⁻ f) := by
  ext x
  change 𝓕 (fun y => conj (f y)) x = conj ((𝓕⁻ f) x)
  rw [SchwartzMap.fourierInv_coe]
  exact fourier_conjugate_fun f x

end RealFourierBridge

namespace RealFourierBridge
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def reflectedSchwartz : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv

@[simp] theorem reflectedSchwartz_apply (f : 𝓢(E, ℂ)) (x : E) :
    reflectedSchwartz f x = f (-x) := rfl

@[simp] theorem fourierInv_reflected (f : 𝓢(E, ℂ)) :
    𝓕⁻ (reflectedSchwartz f) = 𝓕 f := by
  ext x
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  change 𝓕 ((⇑f) ∘ LinearIsometryEquiv.neg ℝ) (-x) = _
  rw [Real.fourier_comp_linearIsometry]
  change 𝓕 (⇑f) (- -x) = _
  simp only [neg_neg]
  rfl

theorem conjugate_fourier_schwartz (f : 𝓢(E, ℂ)) :
    conjugateSchwartz (𝓕 f) = 𝓕 (conjugateSchwartz (reflectedSchwartz f)) := by
  rw [fourier_conjugate_schwartz, fourierInv_reflected]

/-- Conjugation of a scalar-linear tempered distribution in physical space. -/
def conjugateTempered (U : 𝓢(E, ℂ) →L[ℂ] ℂ) : 𝓢(E, ℂ) →L[ℂ] ℂ where
  toFun φ := conj (U (conjugateSchwartz φ))
  map_add' φ ψ := by simp [map_add]
  map_smul' c φ := by
    have h : conjugateSchwartz (c • φ) = conj c • conjugateSchwartz φ := by
      ext x
      simp
    simp only [h, map_smul, RingHom.id_apply, smul_eq_mul, map_mul, starRingEnd_self_apply]
  cont := Complex.continuous_conj.comp (U.continuous.comp conjugateSchwartz.continuous)

end RealFourierBridge

namespace RealFourierBridge
open ExpandedFA.Fourier ExpandedFA.SingularIntegrals

theorem represented_conjugate {d : ℕ} (U : Tempered ℂ d) (m : Euclidean d → ℂ)
    (hrep : FourierRepresentedBy U m) :
    FourierRepresentedBy (conjugateTempered U) (fun ξ => conj (m (-ξ))) := by
  intro φ
  have h := hrep (conjugateSchwartz (reflectedSchwartz φ))
  have hi : Integrable (fun x => conj (m x) * φ (-x)) := by
    convert (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h.1 using 1
    ext x
    simp [Function.comp_def]
  have hi' := (LinearIsometryEquiv.neg ℝ (E := Euclidean d)).measurePreserving.integrable_comp_of_integrable hi
  change Integrable (fun x => conj (m (-x)) * φ (- -x)) at hi'
  refine ⟨by simpa only [neg_neg] using hi', ?_⟩
  change conj (U (conjugateSchwartz (𝓕 φ))) = _
  rw [conjugate_fourier_schwartz]
  change conj (temperedFourier U (conjugateSchwartz (reflectedSchwartz φ))) = _
  rw [h.2, ← integral_conj]
  calc
    _ = ∫ x, conj (m x) * φ (-x) := by
      congr 1
      funext x
      simp
    _ = ∫ x, conj (m (-x)) * φ x := by
      have hh := ((LinearIsometryEquiv.neg ℝ (E := Euclidean d)).measurePreserving.integral_comp
          (LinearIsometryEquiv.neg ℝ (E := Euclidean d)).toHomeomorph.measurableEmbedding
          (fun x => conj (m x) * φ (-x))).symm
      change (∫ x, conj (m x) * φ (-x)) =
        ∫ x, conj (m (-x)) * φ (- -x) at hh
      simpa only [neg_neg] using hh

end RealFourierBridge

namespace RealFourierBridge
open ExpandedFA.Fourier ExpandedFA.SingularIntegrals

def realSymbol {d : ℕ} (m : Euclidean d → ℂ) : Euclidean d → ℂ :=
  fun ξ => (m ξ + conj (m (-ξ))) / 2

def realTempered {d : ℕ} (U : Tempered ℂ d) : Tempered ℂ d :=
  (1 / 2 : ℂ) • (U + conjugateTempered U)

theorem realSymbol_hermitian {d : ℕ} (m : Euclidean d → ℂ) (ξ : Euclidean d) :
    realSymbol m (-ξ) = conj (realSymbol m ξ) := by
  simp only [realSymbol, map_div₀, map_add, neg_neg, starRingEnd_self_apply, map_ofNat]
  rw [add_comm]

theorem bounded_realSymbol {d : ℕ} (m : Euclidean d → ℂ)
    (hm : BoundedFunction m) : BoundedFunction (realSymbol m) := by
  have hm' : AEStronglyMeasurable (fun ξ => conj (m (-ξ))) volume := by
    exact Complex.continuous_conj.comp_aestronglyMeasurable
      (hm.1.comp_measurePreserving (LinearIsometryEquiv.neg ℝ (E := Euclidean d)).measurePreserving)
  refine ⟨?_, ?_⟩
  · change AEStronglyMeasurable (fun ξ => (m ξ + conj (m (-ξ))) / 2) volume
    simpa only [div_eq_mul_inv, Pi.add_apply] using (hm.1.add hm').mul_const (2 : ℂ)⁻¹
  obtain ⟨M, hM, hb⟩ := hm.2
  refine ⟨M, hM, ?_⟩
  intro ξ
  calc
    ‖realSymbol m ξ‖ = ‖m ξ + conj (m (-ξ))‖ / 2 := by simp [realSymbol, norm_div]
    _ ≤ (M + M) / 2 := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add (hb _) (by simpa using hb (-ξ)))
    _ = M := by ring

theorem represented_real {d : ℕ} (U : Tempered ℂ d) (m : Euclidean d → ℂ)
    (hrep : FourierRepresentedBy U m) :
    FourierRepresentedBy (realTempered U) (realSymbol m) := by
  intro φ
  have hc := represented_conjugate U m hrep φ
  have h := hrep φ
  have heq : (fun x => realSymbol m x * φ x) =
      fun x => (1 / 2 : ℂ) * (m x * φ x + conj (m (-x)) * φ x) := by
    funext x
    dsimp [realSymbol]
    ring
  rw [heq]
  refine ⟨(h.1.add hc.1).const_mul _, ?_⟩
  change (1 / 2 : ℂ) * (temperedFourier U φ + temperedFourier (conjugateTempered U) φ) = _
  rw [h.2, hc.2, integral_const_mul, integral_add h.1 hc.1]

end RealFourierBridge


open MeasureTheory Set TopologicalSpace Function
open scoped SchwartzMap ContDiff FourierTransform Topology ComplexConjugate
namespace ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open ExpandedFA.Distributions ExpandedFA.Fourier ExpandedFA.Fourier.Examples
open ExpandedFA.SingularIntegrals RealFourierBridge

@[simp] theorem testSchwartz_conjTest {d : ℕ} (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    testSchwartz ℂ (conjTest φ) = conjugateSchwartz (testSchwartz ℂ φ) := by ext x; rfl

theorem extendsKernel_conjugate {d : ℕ} {u : KernelDistribution d} {U : Tempered ℂ d}
    (h : ExtendsKernel U (complexify u)) :
    ExtendsKernel (conjugateTempered U) (complexify u) := by
  intro φ
  change conj (U (conjugateSchwartz (testSchwartz ℂ φ))) = _
  rw [← testSchwartz_conjTest, h, complexify_conjTest, starRingEnd_self_apply]

theorem extendsKernel_realTempered {d : ℕ} {u : KernelDistribution d} {U : Tempered ℂ d}
    (h : ExtendsKernel U (complexify u)) :
    ExtendsKernel (realTempered U) (complexify u) := by
  intro φ
  change (1 / 2 : ℂ) * (U (testSchwartz ℂ φ) + conjugateTempered U (testSchwartz ℂ φ)) = _
  rw [h, extendsKernel_conjugate h]
  ring
end ExpandedFA.PartIV.CzAnnularCriterion.RealScalar


open MeasureTheory Set FourierTransform
open scoped SchwartzMap FourierTransform Topology ComplexConjugate
namespace ExpandedFA.PartIV.CzAnnularCriterion
open ExpandedFA.Fourier

abbrev ComplexL2 (d : ℕ) := Lp ℂ 2 (volume : Measure (Euclidean d))

def conjugateL2 (d : ℕ) : ComplexL2 d →L[ℝ] ComplexL2 d :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 volume

def reflectL2 (d : ℕ) : ComplexL2 d →L[ℝ] ComplexL2 d :=
  (Lp.compMeasurePreservingₗᵢ ℝ Neg.neg (Measure.measurePreserving_neg volume)).toContinuousLinearMap

def hermitianL2 (d : ℕ) : ComplexL2 d →L[ℝ] ComplexL2 d :=
  (reflectL2 d).comp (conjugateL2 d)

theorem includeRealL2_ae {d : ℕ} (f : RealL2 d) :
    includeRealL2 d f =ᵐ[volume] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL _

theorem projectRealL2_ae {d : ℕ} (f : ComplexL2 d) :
    projectRealL2 d f =ᵐ[volume] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLpL _

theorem conjugateL2_ae {d : ℕ} (f : ComplexL2 d) :
    conjugateL2 d f =ᵐ[volume] fun x => conj (f x) :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLpL _

theorem hermitianL2_ae {d : ℕ} (f : ComplexL2 d) :
    hermitianL2 d f =ᵐ[volume] fun x => conj (f (-x)) := by
  have hneg := (Measure.measurePreserving_neg (volume : Measure (Euclidean d))).quasiMeasurePreserving
  filter_upwards [Lp.coeFn_compMeasurePreserving (conjugateL2 d f)
    (Measure.measurePreserving_neg volume), hneg.ae (conjugateL2_ae f)] with x hx hy
  exact hx.trans hy

theorem conjugateL2_include {d : ℕ} (f : RealL2 d) :
    conjugateL2 d (includeRealL2 d f) = includeRealL2 d f := by
  apply Lp.ext
  filter_upwards [conjugateL2_ae (includeRealL2 d f), includeRealL2_ae f] with x hx hy
  simp only [hx, hy, Complex.conj_ofReal]

theorem include_project_eq_of_conjugate_eq {d : ℕ} (f : ComplexL2 d)
    (hf : conjugateL2 d f = f) :
    includeRealL2 d (projectRealL2 d f) = f := by
  apply Lp.ext
  have hconj := conjugateL2_ae f
  rw [hf] at hconj
  filter_upwards [includeRealL2_ae (projectRealL2 d f), projectRealL2_ae f, hconj]
    with x hx hy hz
  rw [hx, hy]
  exact Complex.conj_eq_iff_re.mp hz.symm

theorem conjugateL2_toLp {d : ℕ} (φ : Schwartz ℂ d) :
    conjugateL2 d (φ.toLp 2) = (RealFourierBridge.conjugateSchwartz φ).toLp 2 := by
  apply Lp.ext
  filter_upwards [conjugateL2_ae (φ.toLp 2), φ.coeFn_toLp 2,
    (RealFourierBridge.conjugateSchwartz φ).coeFn_toLp 2] with x hx hy hz
  simp only [hx, hy, hz, RealFourierBridge.conjugateSchwartz_apply]

theorem hermitianL2_fourier_toLp {d : ℕ} (φ : Schwartz ℂ d) :
    hermitianL2 d ((𝓕 φ).toLp 2) =
      (RealFourierBridge.conjugateSchwartz (𝓕⁻ φ)).toLp 2 := by
  apply Lp.ext
  have hneg := (Measure.measurePreserving_neg (volume : Measure (Euclidean d))).quasiMeasurePreserving
  filter_upwards [hermitianL2_ae ((𝓕 φ).toLp 2), hneg.ae ((𝓕 φ).coeFn_toLp 2 volume),
    (RealFourierBridge.conjugateSchwartz (𝓕⁻ φ)).coeFn_toLp 2] with x hx hy hz
  rw [hx, hy, hz, RealFourierBridge.conjugateSchwartz_apply]
  rfl

theorem fourier_conjugateL2 {d : ℕ} (f : ComplexL2 d) :
    𝓕 (conjugateL2 d f) = hermitianL2 d (𝓕 f) := by
  let p := fun f : ComplexL2 d => 𝓕 (conjugateL2 d f) = hermitianL2 d (𝓕 f)
  apply DenseRange.induction_on (p := p) (SchwartzMap.denseRange_toLpCLM
    (E := Euclidean d) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      ((continuous_fourier (E := ComplexL2 d)).comp (conjugateL2 d).continuous)
      ((hermitianL2 d).continuous.comp continuous_fourier)
  · intro φ
    change 𝓕 (conjugateL2 d (φ.toLp 2)) = hermitianL2 d (𝓕 (φ.toLp 2))
    rw [conjugateL2_toLp, SchwartzMap.toLp_fourier_eq,
      RealFourierBridge.fourier_conjugate_schwartz,
      SchwartzMap.toLp_fourier_eq, hermitianL2_fourier_toLp]

/-- A Hermitian multiplier preserves the real form of complex L². -/
theorem restrict_hermitian_multiplier_L2 {d : ℕ}
    (m : Euclidean d → ℂ)
    (hm : ∀ᵐ ξ ∂volume, conj (m (-ξ)) = m ξ)
    (T : ComplexL2 d →L[ℂ] ComplexL2 d) (M : ℝ) (hM : 0 ≤ M)
    (hT : ‖T‖ ≤ M)
    (hFourierT : ∀ f : ComplexL2 d, (𝓕 (T f) : ComplexL2 d) =ᵐ[volume]
      fun ξ => m ξ * (𝓕 f : ComplexL2 d) ξ) :
    ∃ S : RealL2 d →L[ℝ] RealL2 d, ‖S‖ ≤ M ∧
      ∀ f : RealL2 d, includeRealL2 d (S f) = T (includeRealL2 d f) := by
  let S := (projectRealL2 d).comp ((T.restrictScalars ℝ).comp (includeRealL2 d))
  refine ⟨S, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ hM
    intro f
    change ‖projectRealL2 d (T (includeRealL2 d f))‖ ≤ M * ‖f‖
    calc
      _ ≤ ‖T (includeRealL2 d f)‖ := by
        change ‖Complex.reCLM.compLp (T (includeRealL2 d f))‖ ≤ _
        simpa using Complex.reCLM.norm_compLp_le (T (includeRealL2 d f))
      _ ≤ M * ‖includeRealL2 d f‖ := (T.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
      _ ≤ M * ‖f‖ := by
        apply mul_le_mul_of_nonneg_left _ hM
        change ‖Complex.ofRealCLM.compLp f‖ ≤ _
        simpa using Complex.ofRealCLM.norm_compLp_le f
  · intro f
    change includeRealL2 d (projectRealL2 d (T (includeRealL2 d f))) = _
    apply include_project_eq_of_conjugate_eq
    apply (Lp.fourierTransformₗᵢ (Euclidean d) ℂ).injective
    change 𝓕 (conjugateL2 d (T (includeRealL2 d f))) = 𝓕 (T (includeRealL2 d f))
    rw [fourier_conjugateL2]
    apply Lp.ext
    have hinput := fourier_conjugateL2 (includeRealL2 d f)
    rw [conjugateL2_include] at hinput
    have hinputae := hermitianL2_ae (𝓕 (includeRealL2 d f) : ComplexL2 d)
    rw [← hinput] at hinputae
    have hneg := (Measure.measurePreserving_neg (volume : Measure (Euclidean d))).quasiMeasurePreserving
    filter_upwards [hermitianL2_ae (𝓕 (T (includeRealL2 d f)) : ComplexL2 d),
      hneg.ae (hFourierT (includeRealL2 d f)), hm, hinputae,
      hFourierT (includeRealL2 d f)] with ξ h1 h2 h3 h4 h5
    rw [h1, h2, map_mul, h3, ← h4, h5]

end ExpandedFA.PartIV.CzAnnularCriterion



open MeasureTheory
open scoped FourierTransform
namespace ExpandedFA.PartIV.CzAnnularCriterion
open ExpandedFA.Fourier

/-- Conjugating multiplication by Plancherel retains the specified symbol. -/
theorem bounded_multiplier_hasL2 {d : ℕ} (m : Euclidean d → ℂ)
    (hm : AEStronglyMeasurable m volume) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ ξ, ‖m ξ‖ ≤ M) :
    ∃ T : L2 d →L[ℂ] L2 d, ‖T‖ ≤ M ∧
      ∀ f : L2 d, (𝓕 (T f) : L2 d) =ᵐ[volume]
        fun ξ => m ξ * (𝓕 f : L2 d) ξ := by
  obtain ⟨A, hA, hAe⟩ := exists_bounded_multiply_L2 m hm M hM hbound
  let F := Lp.fourierTransformₗᵢ (Euclidean d) ℂ
  let T : L2 d →L[ℂ] L2 d :=
    F.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (A.comp F.toContinuousLinearEquiv.toContinuousLinearMap)
  have hTnorm : ‖T‖ ≤ M := by
    apply ContinuousLinearMap.opNorm_le_bound T hM
    intro f
    change ‖F.symm (A (F f))‖ ≤ M * ‖f‖
    rw [F.symm.norm_map]
    exact (A.le_opNorm _).trans (by
      rw [F.norm_map]
      exact mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  refine ⟨T, hTnorm, ?_⟩
  intro f
  have he : 𝓕 (T f) = A (𝓕 f) := F.apply_symm_apply _
  rw [he]
  exact hAe _

end ExpandedFA.PartIV.CzAnnularCriterion


open MeasureTheory Set TopologicalSpace Function
open scoped SchwartzMap ContDiff FourierTransform Topology
namespace ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open ExpandedFA.Distributions ExpandedFA.Fourier ExpandedFA.Fourier.Examples

theorem smoothKernelBounds_ofReal {d : ℕ} {k : Euclidean d → ℝ}
    (hk : SmoothKernelBounds k) :
    ExpandedFA.PartIV.CzAnnularCriterion.SmoothKernelBounds (fun x => (k x : ℂ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp_contDiffOn hk.1, ?_⟩
  intro n w
  obtain ⟨C, hC, hb⟩ := hk.2 n w
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hs := hk.1.contDiffAt (isOpen_compl_singleton.mem_nhds hx)
  have he := Complex.ofRealCLM.iteratedFDeriv_comp_left hs (i := n) (by simp)
  change ‖iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ k) x _‖ ≤ _
  rw [he]
  simpa using hb x hx

theorem annularCancellation_ofReal_iff {d : ℕ} {k : Euclidean d → ℝ} :
    ExpandedFA.PartIV.CzAnnularCriterion.AnnularCancellation (fun x => (k x : ℂ)) ↔
      AnnularCancellation k := by
  constructor
  · rintro ⟨A, hA, ha⟩
    refine ⟨A, hA, ?_⟩
    intro r R hr hrR
    obtain ⟨hi, hb⟩ := ha r R hr hrR
    refine ⟨?_, ?_⟩
    · simpa using hi.re
    · simpa only [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs] using hb
  · rintro ⟨A, hA, ha⟩
    refine ⟨A, hA, ?_⟩
    intro r R hr hrR
    obtain ⟨hi, hb⟩ := ha r R hr hrR
    refine ⟨?_, ?_⟩
    · exact Complex.ofRealCLM.integrable_comp hi
    · simpa only [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs] using hb

theorem smoothKernelBounds_ofReal_iff {d : ℕ} {k : Euclidean d → ℝ} :
    ExpandedFA.PartIV.CzAnnularCriterion.SmoothKernelBounds (fun x => (k x : ℂ)) ↔
      SmoothKernelBounds k := by
  refine ⟨?_, smoothKernelBounds_ofReal⟩
  intro hk
  have hs : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)) := by
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
      Complex.reCLM.contDiff.comp_contDiffOn hk.1
  refine ⟨hs, ?_⟩
  intro n w
  obtain ⟨C, hC, hb⟩ := hk.2 n w
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hsd := hs.contDiffAt (isOpen_compl_singleton.mem_nhds hx)
  have he := Complex.ofRealCLM.iteratedFDeriv_comp_left hsd (i := n) (by simp)
  have h := hb x hx
  change ‖iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ k) x _‖ ≤ _ at h
  rw [he] at h
  simpa using h

theorem kernelBounds_complexify_iff {d : ℕ} (u : KernelDistribution d) (k : Euclidean d → ℝ) :
    ExpandedFA.SingularIntegrals.KernelBounds (complexify u) (fun x => (k x : ℂ)) ↔
      KernelBounds u k :=
  and_congr (agreesOffZero_complexify_iff u k) smoothKernelBounds_ofReal_iff

theorem annular_necessity :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar.necessityType := by
  intro d u k hk hb
  apply annularCancellation_ofReal_iff.mp
  apply ExpandedFA.PartIV.CzAnnularCriterion.annular_necessity d (complexify u)
    (fun x => (k x : ℂ)) ((kernelBounds_complexify_iff u k).mpr hk)
  obtain ⟨N, hN⟩ := hb
  exact ⟨N, hN.complexify⟩

theorem standard_of_restrict {d : ℕ} {k : Euclidean d → ℝ}
    {K : ExpandedFA.SingularIntegrals.KernelDistribution d}
    (hK : ExpandedFA.PartIV.CzAnnularCriterion.StandardExtension (fun x => (k x : ℂ)) K) :
    StandardExtension k (restrict K) := by
  have hk : ExpandedFA.SingularIntegrals.KernelBounds (complexify (restrict K))
      (fun x => (k x : ℂ)) := ⟨(AgreesOffZero.restrict hK.1.1).complexify, hK.1.2⟩
  obtain ⟨N, hdN, hb⟩ := ExpandedFA.SingularIntegrals.bounded_to_bumps d K hK.2.hasBoundedFourier
  exact ⟨hk, ExpandedFA.SingularIntegrals.bump_to_symbol d (complexify (restrict K))
    (fun x => (k x : ℂ)) hk ⟨N, hdN, (BumpCancellation.restrict hb).complexify⟩⟩

theorem annular_criterion :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar.annularCriterionType := by
  intro d k hk
  constructor
  · rintro ⟨u, hu⟩
    apply annularCancellation_ofReal_iff.mp
    exact (ExpandedFA.PartIV.CzAnnularCriterion.annular_criterion d
      (fun x => (k x : ℂ)) (smoothKernelBounds_ofReal hk)).mp ⟨complexify u, hu⟩
  · intro ha
    obtain ⟨K, hK⟩ := (ExpandedFA.PartIV.CzAnnularCriterion.annular_criterion d
      (fun x => (k x : ℂ)) (smoothKernelBounds_ofReal hk)).mpr
        (annularCancellation_ofReal_iff.mpr ha)
    exact ⟨restrict K, standard_of_restrict hK⟩

theorem zero_dimension_criterion :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar.zeroDimensionType := by
  intro k
  obtain ⟨ha, K, hK⟩ := ExpandedFA.PartIV.CzAnnularCriterion.zero_dimension_criterion
    (fun x => (k x : ℂ))
  exact ⟨annularCancellation_ofReal_iff.mp ha, restrict K, standard_of_restrict hK⟩

theorem extension_unique_modulo_dirac :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar.uniquenessType := by
  intro d k u v hu hv
  obtain ⟨c, hc⟩ := ExpandedFA.PartIV.CzAnnularCriterion.extension_unique_modulo_dirac
    d (fun x => (k x : ℂ)) (complexify u) (complexify v) hu hv
  refine ⟨c.re, ?_⟩
  ext φ
  have h := congrArg (fun K : ExpandedFA.SingularIntegrals.KernelDistribution d =>
    (K (ofRealTest φ)).re) hc
  simpa [coordinateJet_apply, iteratedFDeriv_zero_apply] using h

theorem complexify_add_dirac {d : ℕ} (u : KernelDistribution d) (c : ℝ) :
    complexify (u + c • coordinateJet ℝ ⊤ (0 : Domain d)
      (Fin.elim0 : Fin 0 → Fin d)) =
    complexify u + (c : ℂ) • coordinateJet ℂ ⊤ (0 : Domain d)
      (Fin.elim0 : Fin 0 → Fin d) := by
  ext φ
  simp only [complexify_apply, add_apply, smul_apply,
    coordinateJet_apply, iteratedFDeriv_zero_apply, realTest_apply, imagTest_apply,
    smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
  conv_rhs => rw [← Complex.re_add_im (φ 0)]
  ring

theorem dirac_stability :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar.diracStabilityType := by
  intro d k u hu c
  unfold StandardExtension
  rw [complexify_add_dirac]
  exact ExpandedFA.PartIV.CzAnnularCriterion.dirac_stability d (fun x => (k x : ℂ))
    (complexify u) hu (c : ℂ)

end ExpandedFA.PartIV.CzAnnularCriterion.RealScalar


open MeasureTheory Set TopologicalSpace Function
open scoped SchwartzMap ContDiff FourierTransform Topology
namespace ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open ExpandedFA.Distributions ExpandedFA.Fourier ExpandedFA.Fourier.Examples

theorem support_complexify_subset {d : ℕ} (u : KernelDistribution d) :
    distributionSupport (complexify u) ⊆ distributionSupport u := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro hv
  obtain ⟨V, hV, hxV⟩ := Set.mem_sUnion.mp hv
  apply hx.2
  apply Set.mem_sUnion.mpr
  refine ⟨V, ⟨hV.1, hV.2.1, ?_⟩, hxV⟩
  intro φ hφ
  have hR : tsupport (realTest φ) ⊆ tsupport φ :=
    tsupport_comp_subset (map_zero Complex.reCLM) _
  have hI : tsupport (imagTest φ) ⊆ tsupport φ :=
    tsupport_comp_subset (map_zero Complex.imCLM) _
  simp [complexify_apply, hV.2.2 _ (hR.trans hφ), hV.2.2 _ (hI.trans hφ)]

theorem point_support_bumps :
    ∀ (d N : ℕ) (u : KernelDistribution d),
      distributionSupport u ⊆ {0} → BumpCancellation u N →
      ∃ c : ℝ, u = c • coordinateJet ℝ ⊤ (0 : Domain d) (Fin.elim0 : Fin 0 → Fin d) := by
  intro d N u hs hb
  obtain ⟨c,hc⟩ := ExpandedFA.PartIV.CzAnnularCriterion.point_support_bumps d N (complexify u)
    ((support_complexify_subset u).trans hs) (BumpCancellation.complexify hb)
  refine ⟨c.re, ?_⟩
  ext φ
  have h := congrArg (fun K : ExpandedFA.SingularIntegrals.KernelDistribution d =>
    (K (ofRealTest φ)).re) hc
  simpa [ExpandedFA.Distributions.coordinateJet_apply, iteratedFDeriv_zero_apply,
    smul_apply, smul_eq_mul, Complex.mul_re] using h
end ExpandedFA.PartIV.CzAnnularCriterion.RealScalar



open MeasureTheory Set TopologicalSpace Function
open scoped SchwartzMap ContDiff FourierTransform Topology ComplexConjugate
namespace ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open ExpandedFA.Distributions ExpandedFA.Fourier ExpandedFA.Fourier.Examples
open ExpandedFA.SingularIntegrals RealFourierBridge

/-- Choosing the Hermitian representative gives a genuine operator on the
real L² space and retains a global Fourier representation. -/
theorem bounded_complexification_hasL2 {d : ℕ} {u : KernelDistribution d}
    (hu : HasBoundedFourier (complexify u)) : HasL2Realization u := by
  obtain ⟨U, m, hU, hm, hrep⟩ := hu
  have hmR := bounded_realSymbol m hm
  obtain ⟨M, hM, hbound⟩ := hmR.2
  obtain ⟨T, hT, hFT⟩ := bounded_multiplier_hasL2 (realSymbol m) hmR.1 M hM hbound
  have hs (ξ : Euclidean d) : conj (realSymbol m (-ξ)) = realSymbol m ξ := by
    rw [realSymbol_hermitian, starRingEnd_self_apply]
  obtain ⟨S, hS, hST⟩ := restrict_hermitian_multiplier_L2 (realSymbol m)
    (Filter.Eventually.of_forall hs) T M hM hT hFT
  exact ⟨realTempered U, realSymbol m, T, S, M, extendsKernel_realTempered hU,
    hmR, represented_real U m hrep, hs, hM, hbound, hT, hS, hFT, hST⟩

theorem standard_consequences :
    Specs.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar.standardConsequencesType := by
  intro d k u hu
  have hkb := (kernelBounds_complexify_iff u k).mp hu.1
  obtain ⟨U, m, hU, hm, hrep⟩ := hu.2.hasBoundedFourier
  obtain ⟨N, hdN, hb⟩ := bounded_to_bumps d (complexify u) hu.2.hasBoundedFourier
  exact ⟨hkb, ⟨restrictTempered U, extendsKernel_restrictTempered hU⟩,
    ⟨N, hdN, (bumpCancellation_complexify_iff u).mp hb⟩,
    bounded_complexification_hasL2 hu.2.hasBoundedFourier⟩

/-- The complexification definition agrees with the physical real bump
criterion; it does not impose an extra scalar-field hypothesis. -/
theorem standard_iff_bumps {d : ℕ} {k : Euclidean d → ℝ} {u : KernelDistribution d}
    (hk : KernelBounds u k) :
    StandardExtension k u ↔ ∃ N : ℕ, d < N ∧ BumpCancellation u N := by
  constructor
  · intro hu
    exact (standard_consequences d k u hu).2.2.1
  · rintro ⟨N, hdN, hb⟩
    have hkc := (kernelBounds_complexify_iff u k).mpr hk
    exact ⟨hkc, bump_to_symbol d (complexify u) (fun x => (k x : ℂ)) hkc
      ⟨N, hdN, hb.complexify⟩⟩

end ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
