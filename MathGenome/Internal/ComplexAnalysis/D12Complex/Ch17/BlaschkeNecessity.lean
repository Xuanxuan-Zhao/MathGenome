import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.BlaschkeNecessity
import Mathlib.Analysis.Complex.JensenFormula
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.DiscreteCountableZeros

noncomputable section
open Complex Metric Set Filter MeromorphicOn MeasureTheory Real
open scoped Topology Classical

namespace D12Complex.BlaschkeNecessity

lemma analytic_disk {f : ℂ → ℂ} (hf : HolomorphicOn (ball 0 1) f) :
    AnalyticOnNhd ℂ f (ball 0 1) := by
  intro a ha
  exact (LocalZeroFactorization.holomorphicNear_iff_analyticAt f a).mp
    ⟨ball 0 1, ha, hf⟩

lemma finite_order {f : ℂ → ℂ} (hf : HolomorphicOn (ball 0 1) f)
    (hn : ¬ EqOn f (fun _ => 0) (ball 0 1)) {a : ℂ} (ha : a ∈ ball 0 1) :
    analyticOrderAt f a ≠ ⊤ := by
  intro ht
  exact hn ((analytic_disk hf).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected ha (analyticOrderAt_eq_top.mp ht))

lemma divisor_eq_nat {f : ℂ → ℂ} {r : ℝ}
    (hf : HolomorphicOn (ball 0 1) f) (hn : ¬ EqOn f (fun _ => 0) (ball 0 1))
    (hr : r < 1) {a : ℂ} (ha : a ∈ closedBall (0 : ℂ) r) :
    divisor f (closedBall (0 : ℂ) r) a = ((analyticOrderAt f a).toNat : ℤ) := by
  have hs : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr
  have hf' := (analytic_disk hf).mono hs
  rw [hf'.divisor_apply ha, ← ENat.natCast_toNat (finite_order hf hn (hs ha))]
  simp

/-- Jensen at an interior radius, retaining the center term separately. -/
lemma radius_bound {f : ℂ → ℂ} {M r : ℝ}
    (hf : HolomorphicOn (ball 0 1) f) (hn : ¬ EqOn f (fun _ => 0) (ball 0 1))
    (_hM : 0 < M) (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M)
    (hr : 0 < r) (hr1 : r < 1) (s : Finset ℂ)
    (hs : ∀ a ∈ s, a ≠ 0 ∧ ‖a‖ ≤ r) :
    (∑ a ∈ s, ((analyticOrderAt f a).toNat : ℝ) * Real.log (r / ‖a‖)) +
        ((analyticOrderAt f 0).toNat : ℝ) * Real.log r ≤
      Real.log M - Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  let D := divisor f (closedBall (0 : ℂ) r)
  let w : ℂ → ℝ := fun a => (D a : ℝ) * Real.log (r * ‖(0 : ℂ) - a‖⁻¹)
  have han : AnalyticOnNhd ℂ f (closedBall 0 r) :=
    (analytic_disk hf).mono (closedBall_subset_ball hr1)
  have hw : Function.HasFiniteSupport w :=
    (D.finiteSupport (isCompact_closedBall 0 r)).subset (by
      intro a ha
      contrapose! ha
      change ¬ D a ≠ 0 at ha
      simp [w, not_not.mp ha])
  have hw0 (a : ℂ) : 0 ≤ w a := by
    by_cases hd : D a = 0
    · simp [w, hd]
    by_cases ha0 : a = 0
    · simp [w, ha0]
    have ha := D.supportWithinDomain hd
    have hnrm : ‖a‖ ≤ r := by simpa using ha
    have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    apply mul_nonneg (by exact_mod_cast han.divisor_nonneg a)
    simp only [zero_sub, norm_neg, ← div_eq_mul_inv]
    exact Real.log_nonneg ((one_le_div hpos).mpr hnrm)
  have hsum : (∑ a ∈ s, ((analyticOrderAt f a).toNat : ℝ) * Real.log (r / ‖a‖)) ≤
      ∑ᶠ a, w a := by
    let t := hw.toFinset ∪ s
    rw [finsum_eq_sum_of_support_subset _ (show Function.support w ⊆ t by
      intro a ha; exact Finset.mem_union_left _ (hw.mem_toFinset.mpr ha))]
    calc
      _ = ∑ a ∈ s, w a := by
        apply Finset.sum_congr rfl
        intro a ha
        have hac : a ∈ closedBall (0 : ℂ) r := by simpa using (hs a ha).2
        simp only [w, D, divisor_eq_nat hf hn hr1 hac, Int.cast_natCast,
          zero_sub, norm_neg, div_eq_mul_inv]
      _ ≤ ∑ a ∈ t, w a := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_union_right) (fun a _ _ => hw0 a)
  have hj := (show MeromorphicOn f (closedBall 0 |r|) by
    simpa only [abs_of_pos hr] using han.meromorphicOn).circleAverage_log_norm hr.ne'
  rw [abs_of_pos hr] at hj
  have hmean : circleAverage (fun z => Real.log ‖f z‖) 0 r ≤ Real.log M := by
    have hdomain : IsDomain (ball (0 : ℂ) 1) :=
      ⟨⟨0, by simp⟩, isOpen_ball, (convex_ball (0 : ℂ) 1).isPreconnected⟩
    have hcount := DiscreteCountableZeros.zeros_countable (ball 0 1) f hdomain hf hn
    have hnull : volume {t : ℝ | circleMap 0 r t ∈ {z | z ∈ ball 0 1 ∧ f z = 0}} = 0 :=
      (hcount.preimage_circleMap 0 hr.ne').measure_zero _
    have hae : (fun t : ℝ => Real.log ‖f (circleMap 0 r t)‖) ≤ᵐ[volume]
        (fun _ => Real.log M) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht
      have hzt : circleMap (0 : ℂ) r t ∈ ball 0 1 :=
        (closedBall_subset_ball hr1) (sphere_subset_closedBall (circleMap_mem_sphere 0 hr.le t))
      have hne : f (circleMap 0 r t) ≠ 0 := fun h => ht ⟨hzt, h⟩
      exact Real.log_le_log (norm_pos_iff.mpr hne) (hbound _ hzt)
    have hi := (han.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm_of_nonneg hr.le
    rw [← circleAverage_const (Real.log M) (0 : ℂ) r]
    unfold circleAverage
    simp only [smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact intervalIntegral.integral_mono_ae (by positivity) hi intervalIntegrable_const hae
  have hc : divisor f (closedBall (0 : ℂ) r) 0 =
      ((analyticOrderAt f 0).toNat : ℤ) :=
    divisor_eq_nat hf hn hr1 (mem_closedBall_self hr.le)
  rw [hc] at hj
  change circleAverage (fun z => Real.log ‖f z‖) 0 r =
    (∑ᶠ a, w a) + ((analyticOrderAt f 0).toNat : ℝ) * Real.log r +
      Real.log ‖meromorphicTrailingCoeffAt f 0‖ at hj
  linarith


/-- Passage to the boundary uses limits of finite sums only. No boundary
extension or integrability hypothesis on the unit circle is used. -/
lemma finite_log_bound_trailing {f : ℂ → ℂ} {M : ℝ}
    (hf : HolomorphicOn (ball 0 1) f) (hn : ¬ EqOn f (fun _ => 0) (ball 0 1))
    (hM : 0 < M) (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M)
    (s : Finset ℂ) (hs : ∀ a ∈ s, a ≠ 0 ∧ ‖a‖ < 1) :
    ∑ a ∈ s, ((analyticOrderAt f a).toNat : ℝ) * Real.log (1 / ‖a‖) ≤
      Real.log M - Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have he : ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ a ∈ s, ‖a‖ ≤ r := by
    rw [Filter.eventually_all_finset]
    intro a ha
    exact ((eventually_gt_nhds (hs a ha).2).filter_mono nhdsWithin_le_nhds).mono
      (fun _ h => h.le)
  have hcont : ContinuousAt (fun r : ℝ =>
      (∑ a ∈ s, ((analyticOrderAt f a).toNat : ℝ) * Real.log (r / ‖a‖)) +
        ((analyticOrderAt f 0).toNat : ℝ) * Real.log r) 1 := by
    apply ContinuousAt.add
    · apply tendsto_finsetSum s
      intro a ha
      exact continuousAt_const.mul ((continuousAt_id.div_const ‖a‖).log
        (div_ne_zero one_ne_zero (norm_ne_zero_iff.mpr (hs a ha).1)))
    · exact continuousAt_const.mul (Real.continuousAt_log one_ne_zero)
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  simp only [Real.log_one, mul_zero, add_zero] at hlim
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num), he] with r hr hsr
  exact radius_bound hf hn hM hbound hr.1 hr.2 s
    (fun a ha => ⟨(hs a ha).1, hsr a ha⟩)

theorem finite_log_bound :
    Specs.D12Complex.Ch17.BlaschkeNecessity.finite_log_bound_type := by
  intro f M hf hn hM hbound
  have h0 : (0 : ℂ) ∈ ball 0 1 := by simp
  have hfin := finite_order hf hn h0
  obtain ⟨g, hg, hg0, he⟩ := ((analytic_disk hf) 0 h0).analyticOrderAt_ne_top.mp hfin
  let m := (analyticOrderAt f 0).toNat
  have heq : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z ^ m * g z := by
    simpa only [Filter.EventuallyEq, sub_zero, smul_eq_mul, analyticOrderNatAt, m] using he
  have hc : meromorphicTrailingCoeffAt f 0 = g 0 := by
    apply hg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := (m : ℤ)) hg0
    simpa only [Filter.EventuallyEq, sub_zero, zpow_natCast, smul_eq_mul] using
      heq.filter_mono nhdsWithin_le_nhds
  refine ⟨m, g, (LocalZeroFactorization.holomorphicNear_iff_analyticAt g 0).mpr hg,
    hg0, heq, ENat.natCast_toNat hfin |>.symm, ?_⟩
  intro s hs
  simpa only [hc] using finite_log_bound_trailing hf hn hM hbound s hs

theorem multiplicity :
    Specs.D12Complex.Ch17.BlaschkeNecessity.multiplicity_type := by
  intro f hf hn a ha
  have hfin := finite_order hf hn ha
  refine ⟨hfin, ?_⟩
  have horder : (analyticOrderAt f a).toNat = 0 ↔ f a ≠ 0 := by
    rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_zero, ENat.natCast_toNat hfin]
    exact ((analytic_disk hf) a ha).analyticOrderAt_eq_zero
  simpa only [Nat.pos_iff_ne_zero, not_iff_not, not_not] using not_congr horder

theorem blaschke_necessity :
    Specs.D12Complex.Ch17.BlaschkeNecessity.blaschke_necessity_type := by
  intro f hf hn hb
  obtain ⟨M, hM⟩ := hb
  let C := max 1 M
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ C :=
    fun z hz => (hM z hz).trans (le_max_right _ _)
  obtain ⟨m, g, hg, hg0, he, hm, hlog⟩ := finite_log_bound f C hf hn hC hbound
  apply summable_of_sum_le (c := Real.log C - Real.log ‖g 0‖)
  · intro a
    change 0 ≤ if a ≠ 0 ∧ ‖a‖ < 1 then
      ((analyticOrderAt f a).toNat : ℝ) * (1 - ‖a‖) else 0
    split_ifs with ha
    · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr ha.2.le)
    · exact le_rfl
  · intro s
    let t := s.filter (fun a => a ≠ 0 ∧ ‖a‖ < 1)
    have ht : ∀ a ∈ t, a ≠ 0 ∧ ‖a‖ < 1 := fun a ha => (Finset.mem_filter.mp ha).2
    calc
      _ = ∑ a ∈ t, ((analyticOrderAt f a).toNat : ℝ) * (1 - ‖a‖) := by
        rw [Finset.sum_filter]
      _ ≤ ∑ a ∈ t, ((analyticOrderAt f a).toNat : ℝ) * Real.log (1 / ‖a‖) := by
        apply Finset.sum_le_sum
        intro a ha
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [one_div, Real.log_inv]
        linarith [Real.log_le_sub_one_of_pos (norm_pos_iff.mpr (ht a ha).1)]
      _ ≤ _ := hlog t ht

theorem repeated_zeros :
    Specs.D12Complex.Ch17.BlaschkeNecessity.repeated_zeros_type := by
  intro f hf hn hb
  apply (summable_sigma_of_nonneg (fun p => sub_nonneg.mpr p.1.2.2.1.le)).mpr
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  have hs := (blaschke_necessity f hf hn hb).subtype
    {a : ℂ | a ≠ 0 ∧ ‖a‖ < 1 ∧ f a = 0}
  apply hs.congr
  intro a
  simp [a.2.1, a.2.2.1, mul_sub]

end D12Complex.BlaschkeNecessity
