import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.JensenCenterBoundary
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.PoissonJensen
import Mathlib.Analysis.Complex.JensenFormula

noncomputable section
open Complex Metric Set Filter MeromorphicOn MeasureTheory Real
open scoped Topology Classical

namespace D12Complex.JensenCenterBoundary
open PoissonJensen

theorem elementary_log_mean :
    Specs.D12Complex.Ch17.JensenCenterBoundary.elementary_log_mean_type := by
  intro R hR a
  refine ⟨circleIntegrable_log_norm_sub_const R, ?_⟩
  change circleAverage (fun z : ℂ => Real.log ‖z - a‖) 0 R = _
  by_cases ha : ‖a‖ ≤ R
  · rw [max_eq_left ha]
    apply circleAverage_log_norm_sub_const_of_mem_closedBall
    simpa [abs_of_pos hR] using ha
  · have hRa : R < ‖a‖ := lt_of_not_ge ha
    rw [max_eq_right hRa.le,
      circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR.ne']
    simp only [zero_sub, norm_neg]
    have hlarge : 1 ≤ |R⁻¹ * ‖a‖| := by
      rw [abs_of_nonneg (by positivity), ← div_eq_inv_mul]
      exact (one_le_div hR).mpr hRa.le
    rw [Real.posLog_eq_log hlarge, Real.log_mul (inv_ne_zero hR.ne')
        (ne_of_gt (hR.trans hRa)), Real.log_inv]
    ring

theorem boundary_integrable :
    Specs.D12Complex.Ch17.JensenCenterBoundary.boundary_integrable_type := by
  intro U F R hF hR hsub
  have hf : MeromorphicOn (scalarFinitePart F) (sphere 0 R) :=
    fun z hz => disk_meromorphic hF hsub z (sphere_subset_closedBall hz)
  exact hf.circleIntegrable_log_norm_of_nonneg hR.le

/-- Propagate a single finite order through the connected closed disk. This
does not impose any condition on other components of U. -/
lemma disk_order_eq_of_center {U : Set ℂ} {F : ℂ → RiemannSphere} {R : ℝ}
    (hF : ScalarMeromorphicOn U F) (hR : 0 < R) (hsub : closedBall (0 : ℂ) R ⊆ U)
    (h0 : meromorphicOrderAt (scalarFinitePart F) 0 ≠ ⊤)
    {a : ℂ} (ha : a ∈ closedBall (0 : ℂ) R) :
    meromorphicOrderAt (scalarFinitePart F) a = (diskDivisor F R a : WithTop ℤ) := by
  have hf := disk_meromorphic hF hsub
  have hfin := hf.meromorphicOrderAt_ne_top_of_isPreconnected
    (convex_closedBall (0 : ℂ) R).isPreconnected (mem_closedBall_self hR.le) ha h0
  rw [diskDivisor, divisor_apply hf ha, WithTop.coe_untop₀_of_ne_top hfin]

lemma center_order_and_coefficient {U V : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn U F) (hU : (0 : ℂ) ∈ U)
    {g : ℂ → ℂ} {m : ℤ} (hV : (0 : ℂ) ∈ V) (hg : HolomorphicOn V g)
    (hg0 : g 0 ≠ 0)
    (he : scalarFinitePart F =ᶠ[𝓝[≠] 0] fun z => z ^ m * g z) :
    meromorphicOrderAt (scalarFinitePart F) 0 = (m : WithTop ℤ) ∧
    meromorphicTrailingCoeffAt (scalarFinitePart F) 0 = g 0 := by
  have hga := (LocalZeroFactorization.holomorphicNear_iff_analyticAt g 0).mp ⟨V, hV, hg⟩
  have he' : scalarFinitePart F =ᶠ[𝓝[≠] 0] fun z => (z - 0) ^ m • g z := by
    simpa only [sub_zero, smul_eq_mul] using he
  exact ⟨(meromorphicOrderAt_eq_int_iff
      (LocalQuotientsArithmetic.scalar_meromorphicAt U F hF 0 hU)).mpr ⟨g, hga, hg0, he'⟩,
    hga.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hg0 he'⟩

theorem jensen_center_boundary :
    Specs.D12Complex.Ch17.JensenCenterBoundary.jensen_center_boundary_type := by
  intro U F R hF hR hsub V g m hV hg hg0 he
  have hc : (0 : ℂ) ∈ closedBall (0 : ℂ) R := mem_closedBall_self hR.le
  obtain ⟨ho, hcoef⟩ := center_order_and_coefficient hF (hsub hc) hV hg hg0 he
  have h0 : meromorphicOrderAt (scalarFinitePart F) 0 ≠ ⊤ := by
    rw [ho]; exact WithTop.coe_ne_top
  have hd0 : diskDivisor F R 0 = m := by
    rw [← WithTop.coe_eq_coe, ← disk_order_eq_of_center hF hR hsub h0 hc, ho]
  let φ : ℂ → ℝ := fun a => if a ∈ ball 0 R ∧ a ≠ 0 then Real.log (R / ‖a‖) else 0
  have hs : (∑ᶠ a : ℂ, (diskDivisor F R a : ℝ) *
      Real.log (R * ‖(0 : ℂ) - a‖⁻¹)) = ∑ᶠ a : ℂ, (diskDivisor F R a : ℝ) * φ a := by
    apply finsum_congr
    intro a
    by_cases had : diskDivisor F R a = 0
    · simp [had]
    have hac := (diskDivisor F R).supportWithinDomain had
    have han : ‖a‖ ≤ R := by simpa using hac
    by_cases ha0 : a = 0
    · simp [ha0, φ]
    by_cases hai : a ∈ ball (0 : ℂ) R
    · have hφ : φ a = Real.log (R / ‖a‖) := by
        exact ite_eq_left (show a ∈ ball 0 R ∧ a ≠ 0 from ⟨hai, ha0⟩)
      rw [hφ]
      simp only [zero_sub, norm_neg, div_eq_mul_inv]
    · have han' : ¬ ‖a‖ < R := by simpa using hai
      have hab : ‖a‖ = R := le_antisymm han (not_lt.mp han')
      have hφ : φ a = 0 := ite_eq_right (fun h => hai h.1)
      rw [hφ]
      simp only [zero_sub, norm_neg, hab, mul_inv_cancel₀ hR.ne', Real.log_one, mul_zero]
  have hf : MeromorphicOn (scalarFinitePart F) (closedBall 0 |R|) := by
    simpa only [abs_of_pos hR] using disk_meromorphic hF hsub
  have hj := hf.circleAverage_log_norm hR.ne'
  rw [abs_of_pos hR] at hj
  change boundaryMean F R =
    (∑ᶠ a : ℂ, (diskDivisor F R a : ℝ) * Real.log (R * ‖(0 : ℂ) - a‖⁻¹)) +
      (diskDivisor F R 0 : ℝ) * Real.log R +
      Real.log ‖meromorphicTrailingCoeffAt (scalarFinitePart F) 0‖ at hj
  rw [hs, hd0, hcoef, signed_sum_eq_difference F R φ] at hj
  have hz : (∑ᶠ a : ℂ, (zeroMultiplicity F R a : ℝ) * φ a) =
      ∑ᶠ a : ℂ, if a ∈ ball 0 R ∧ a ≠ 0 then
        (zeroMultiplicity F R a : ℝ) * Real.log (R / ‖a‖) else 0 := by
    apply finsum_congr; intro a; simp only [φ]; split_ifs <;> simp
  have hp : (∑ᶠ a : ℂ, (poleMultiplicity F R a : ℝ) * φ a) =
      ∑ᶠ a : ℂ, if a ∈ ball 0 R ∧ a ≠ 0 then
        (poleMultiplicity F R a : ℝ) * Real.log (R / ‖a‖) else 0 := by
    apply finsum_congr; intro a; simp only [φ]; split_ifs <;> simp
  rw [hz, hp] at hj
  linarith

theorem boundary_divisor_terms_zero :
    Specs.D12Complex.Ch17.JensenCenterBoundary.boundary_divisor_terms_zero_type := by
  intro F R a hR ha
  have han : ‖a‖ = R := by simpa using ha
  simp [han, hR.ne']

theorem finite_divisor :
    Specs.D12Complex.Ch17.JensenCenterBoundary.finite_divisor_type := by
  intro U F R hF hR hsub hn
  have hc : (0 : ℂ) ∈ closedBall (0 : ℂ) R := mem_closedBall_self hR.le
  have h0 : meromorphicOrderAt (scalarFinitePart F) 0 ≠ ⊤ := by
    intro he
    exact hn ((scalarSignedOrder_none_iff U F hF 0 (hsub hc)).mp he)
  have hD := (diskDivisor F R).finiteSupport (isCompact_closedBall 0 R)
  refine ⟨hD.subset multiplicity_support.1, hD.subset multiplicity_support.2, ?_⟩
  intro a ha
  have ho := disk_order_eq_of_center hF hR hsub h0 ha
  have hP : F a = sphereInfty ↔ diskDivisor F R a < 0 := by
    have he : F a = LocalQuotientsArithmetic.fill (scalarFinitePart F) a :=
      LocalQuotientsArithmetic.scalar_eq_fill U F hF (hsub ha)
    rw [he, LocalQuotientsArithmetic.fill_eq_infty_iff, ho]
    exact WithTop.coe_lt_coe
  have hZ : 0 < diskDivisor F R a ↔ F a = sphereFinite 0 := by
    by_cases hi : F a = sphereInfty
    · have hd := hP.mp hi
      simp only [hi, show sphereInfty ≠ sphereFinite 0 from (OnePoint.coe_ne_infty 0).symm,
        iff_false]
      omega
    · have han := scalarMeromorphicOn_finite_analytic U F hF a (hsub ha) hi
      have hdn : 0 ≤ diskDivisor F R a := by
        have := han.meromorphicOrderAt_nonneg
        rw [ho] at this
        exact WithTop.coe_le_coe.mp this
      have hd0 : diskDivisor F R a = 0 ↔ scalarFinitePart F a ≠ 0 := by
        have he := han.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff
        rw [ho] at he
        simpa using he
      have hval : F a = sphereFinite (scalarFinitePart F a) := by
        rcases sphere_eq_infty_or_finite (F a) with h | ⟨c, hc⟩
        · exact (hi h).elim
        · simp [scalarFinitePart, hc]
      constructor
      · intro hd
        have hf0 : scalarFinitePart F a = 0 := by
          by_contra hn
          have := hd0.mpr hn
          omega
        simpa [hf0] using hval
      · intro he
        have hf0 : scalarFinitePart F a = 0 := by simp [scalarFinitePart, he]
        have hne : diskDivisor F R a ≠ 0 := fun h => (hd0.mp h) hf0
        omega
  refine ⟨ho, ?_, ?_⟩
  · have ht : 0 < (diskDivisor F R a).toNat ↔ 0 < diskDivisor F R a := by omega
    exact ht.trans hZ
  · have ht : 0 < (-diskDivisor F R a).toNat ↔ diskDivisor F R a < 0 := by omega
    exact ht.trans hP.symm

theorem boundary_redefinition :
    Specs.D12Complex.Ch17.JensenCenterBoundary.boundary_redefinition_type := by
  intro U F R hF hR hsub hn φ hφ
  have hd := finite_divisor U F R hF hR hsub hn
  let E := (diskDivisor F R).support
  have hE : E.Finite := (diskDivisor F R).finiteSupport (isCompact_closedBall 0 R)
  have hnull : volume {t : ℝ | circleMap 0 R t ∈ E} = 0 :=
    (hE.countable.preimage_circleMap 0 hR.ne').measure_zero _
  have hae : (fun t : ℝ => φ (circleMap 0 R t)) =ᵐ[volume]
      (fun t : ℝ => Real.log ‖scalarFinitePart F (circleMap 0 R t)‖) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht
    have hζ := circleMap_mem_sphere (0 : ℂ) hR.le t
    have hD : diskDivisor F R (circleMap 0 R t) = 0 := not_not.mp ht
    have hz : zeroMultiplicity F R (circleMap 0 R t) = 0 := by
      simp only [zeroMultiplicity, hD, Int.toNat_zero]
    have hp : poleMultiplicity F R (circleMap 0 R t) = 0 := by
      simp only [poleMultiplicity, hD, neg_zero, Int.toNat_zero]
    have hm := hd.2.2 (circleMap 0 R t) (sphere_subset_closedBall hζ)
    apply hφ _ hζ
    · intro he
      have := hm.2.2.mpr he
      omega
    · intro he
      have := hm.2.1.mpr he
      omega
  refine ⟨(boundary_integrable U F R hF hR hsub).congr_ae
    (ae_restrict_of_ae hae.symm), ?_⟩
  unfold boundaryMean
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hae] with t ht using fun _ => ht

end D12Complex.JensenCenterBoundary
