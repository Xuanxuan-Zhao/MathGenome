import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.BoundaryFactorProduct
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.CanonicalFactors
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.HolomorphicProducts
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Data.ENat.BigOperators

noncomputable section
open Set Metric Filter
open scoped Topology
namespace D12Complex.BoundaryFactorProduct

abbrev Admissible := Specs.D12Complex.Ch16.BoundaryFactorProduct.Admissible_value
abbrev Nearest := Specs.D12Complex.Ch16.BoundaryFactorProduct.Nearest_value
abbrev boundaryFactor := Specs.D12Complex.Ch16.BoundaryFactorProduct.boundaryFactor_value
abbrev product := Specs.D12Complex.Ch16.BoundaryFactorProduct.product_value

theorem exists_nearest : Specs.D12Complex.Ch16.BoundaryFactorProduct.exists_nearest_type := by
  intro G z h
  have hn : ∀ n, ∃ x ∈ Gᶜ, dist (z n) x = infDist (z n) Gᶜ := by
    intro n
    obtain ⟨x, hx, heq⟩ := h.2.2.1.exists_infDist_eq_dist h.2.2.2.1 (z n)
    exact ⟨x, hx, heq.symm⟩
  choose b hb using hn
  exact ⟨b, hb⟩

theorem nearest_bounded : Specs.D12Complex.Ch16.BoundaryFactorProduct.nearest_bounded_type := by
  intro G z b h hb
  exact h.2.2.1.isBounded.subset (by rintro _ ⟨n, rfl⟩; exact (hb n).1)

theorem distances_tendsto_zero :
    Specs.D12Complex.Ch16.BoundaryFactorProduct.distances_tendsto_zero_type := by
  intro G z h
  obtain ⟨R, hR⟩ := h.2.2.2.2.1.subset_closedBall (0 : ℂ)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let K : Set ℂ := closedBall 0 R ∩ {w | ε ≤ infDist w Gᶜ}
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right
    (isClosed_le continuous_const (continuous_infDist_pt Gᶜ))
  have hKG : K ⊆ G := by
    intro w hw
    by_contra hn
    have hz : infDist w Gᶜ = 0 := infDist_zero_of_mem hn
    have hh : ε ≤ infDist w Gᶜ := hw.2
    linarith
  have hfin := h.2.2.2.2.2.2 K hK hKG
  have hev : ∀ᶠ n : ℕ in atTop, z n ∉ K :=
    Nat.cofinite_eq_atTop ▸ hfin.eventually_cofinite_notMem
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg]
  by_contra hh
  exact hN n hn ⟨hR (mem_range_self n), le_of_not_gt hh⟩

theorem nearest_distances_tendsto_zero :
    Specs.D12Complex.Ch16.BoundaryFactorProduct.nearest_distances_tendsto_zero_type := by
  intro G z b h hb
  have heq : (fun n => ‖z n - b n‖) = (fun n => infDist (z n) Gᶜ) := by
    funext n
    exact (dist_eq_norm (z n) (b n)).symm.trans (hb n).2
  rw [heq]
  exact distances_tendsto_zero G z h

lemma numerator_ne_zero {G : Set ℂ} {z b : ℕ → ℂ}
    (hz : ∀ n, z n ∈ G) (hb : Nearest G z b) (n : ℕ) : z n - b n ≠ 0 := by
  intro he
  exact (hb n).1 (sub_eq_zero.mp he ▸ hz n)

lemma denominator_ne_zero {G : Set ℂ} {z b : ℕ → ℂ}
    (hb : Nearest G z b) {w : ℂ} (hw : w ∈ G) (n : ℕ) : w - b n ≠ 0 := by
  intro he
  exact (hb n).1 (sub_eq_zero.mp he ▸ hw)

lemma factor_holomorphic {G : Set ℂ} {z b : ℕ → ℂ}
    (hG : IsOpen G) (hb : Nearest G z b) (n : ℕ) :
    HolomorphicOn G (boundaryFactor z b n) := by
  refine ⟨hG, fun w hw => ?_⟩
  exact ((CanonicalFactors.factor_entire (n+1)).2 _ (mem_univ _)).comp w
    ((differentiableAt_const (z n - b n)).div (differentiableAt_id.sub_const _) (denominator_ne_zero hb hw n))

lemma factor_eq_zero_iff {G : Set ℂ} {z b : ℕ → ℂ}
    (hb : Nearest G z b) {w : ℂ} (hw : w ∈ G) (n : ℕ) :
    boundaryFactor z b n w = 0 ↔ z n = w := by
  change CanonicalFactors.factor (n+1) ((z n - b n) / (w - b n)) = 0 ↔ _
  rw [CanonicalFactors.factor_eq_zero_iff,
    div_eq_one_iff_eq (denominator_ne_zero hb hw n), sub_left_inj]

theorem normal_product : Specs.D12Complex.Ch16.BoundaryFactorProduct.normal_product_type := by
  intro G z b h hb K hK hKG
  classical
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨d, hd, hdK⟩ := hK.exists_forall_le'
    (continuous_infDist_pt Gᶜ).continuousOn (fun w hw =>
      (h.1.isClosed_compl.notMem_iff_infDist_pos h.2.2.2.1).mp (by simpa using hKG hw))
  have hev : ∀ᶠ n : ℕ in atTop, infDist (z n) Gᶜ < d / 2 :=
    (distances_tendsto_zero G z h).eventually (Iio_mem_nhds (by linarith))
  have harg : ∀ᶠ n : ℕ in atTop, ∀ w ∈ K, ‖(z n - b n) / (w - b n)‖ ≤ 1/2 := by
    filter_upwards [hev] with n hn w hw
    rw [norm_div, ← dist_eq_norm, (hb n).2]
    have hden : d ≤ ‖w - b n‖ := (hdK w hw).trans (by simpa only [dist_eq_norm] using (infDist_le_dist_of_mem (x := w) (hb n).1))
    exact (div_le_iff₀ (lt_of_lt_of_le hd hden)).mpr (by linarith)
  have hgeom : Summable (fun n : ℕ => 6 * (1/2 : ℝ) ^ (n+2)) :=
    ((summable_nat_add_iff 2).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))).mul_left 6
  apply hgeom.of_norm_bounded_eventually_nat
  filter_upwards [harg] with n hn
  have hc : ContinuousOn (fun w => ‖boundaryFactor z b n w - 1‖) K :=
    fun w hw => (((factor_holomorphic h.1 hb n).2 w (hKG hw)).continuousAt.sub
      continuousAt_const).norm.continuousWithinAt
  have hnonneg : 0 ≤ sSup ((fun w => ‖boundaryFactor z b n w - 1‖) '' K) := by
    obtain ⟨w, hw⟩ := hne
    exact (norm_nonneg _).trans (le_csSup (hK.bddAbove_image hc) (mem_image_of_mem _ hw))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  apply csSup_le (hne.image _)
  rintro _ ⟨w, hw, rfl⟩
  exact (CanonicalFactors.norm_factor_sub_one_le (n+1) _ (hn w hw)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hn w hw) _) (by norm_num))

theorem product_holomorphic : Specs.D12Complex.Ch16.BoundaryFactorProduct.product_holomorphic_type := by
  intro G z b h hb
  exact HolomorphicProducts.holomorphic_product_limit G _ h.1
    (factor_holomorphic h.1 hb) (normal_product G z b h hb)

theorem product_zeros : Specs.D12Complex.Ch16.BoundaryFactorProduct.product_zeros_type := by
  intro G z b h hb a ha
  exact (HolomorphicProducts.product_eq_zero_iff G _ (normal_product G z b h hb) a ha).trans
    (exists_congr (fun n => factor_eq_zero_iff hb ha n))


lemma factor_order {G : Set ℂ} {z b : ℕ → ℂ}
    (h : Admissible G z) (hb : Nearest G z b) {a : ℂ} (ha : a ∈ G) (n : ℕ) :
    analyticOrderAt (boundaryFactor z b n) a = (if z n = a then 1 else 0 : ℕ∞) := by
  classical
  have hden := denominator_ne_zero hb ha n
  by_cases he : z n = a
  · rw [ite_eq_left he]
    let q : ℂ → ℂ := fun w => (z n - b n) / (w - b n)
    have hq : AnalyticAt ℂ q a :=
      analyticAt_const.div (analyticAt_id.sub analyticAt_const) hden
    have hd : deriv q a = -(z n - b n) / (a - b n)^2 := by
      dsimp [q]
      rw [deriv_const_div (d := fun w : ℂ => w - b n) (z n - b n)
        (differentiableAt_id.sub_const (b n)) hden]
      simp
    have hdn : deriv q a ≠ 0 := by
      rw [hd]
      exact div_ne_zero (neg_ne_zero.mpr (numerator_ne_zero h.2.2.2.2.2.1 hb n)) (pow_ne_zero _ hden)
    change analyticOrderAt (CanonicalFactors.factor (n+1) ∘ q) a = 1
    rw [analyticOrderAt_comp_of_deriv_ne_zero hq hdn,
      show q a = 1 by simp [q, he, hden]]
    exact CanonicalFactors.factor_simple_zero (n+1)
  · rw [ite_eq_right he]
    exact (HolomorphicProducts.analyticAt_of_holomorphic (factor_holomorphic h.1 hb n) ha).analyticOrderAt_eq_zero.mpr
      (fun hz => he ((factor_eq_zero_iff hb ha n).mp hz))

theorem product_multiplicity :
    Specs.D12Complex.Ch16.BoundaryFactorProduct.product_multiplicity_type := by
  intro G z b h hb a ha
  classical
  have hn := normal_product G z b h hb
  have hu := factor_holomorphic h.1 hb
  have hau : ∀ n, AnalyticAt ℂ (boundaryFactor z b n) a :=
    fun n => HolomorphicProducts.analyticAt_of_holomorphic (hu n) ha
  have hfin : {n : ℕ | z n = a}.Finite := by
    simpa using h.2.2.2.2.2.2 {a} isCompact_singleton (singleton_subset_iff.mpr ha)
  obtain ⟨N, hN⟩ := HolomorphicProducts.tail_nonvanishing_on_compact G _ h.1 hu hn {a}
    isCompact_singleton (singleton_subset_iff.mpr ha)
  have htail := hN N le_rfl a (mem_singleton a)
  have hta := HolomorphicProducts.analyticAt_of_holomorphic
    (HolomorphicProducts.holomorphic_tail_limit G _ h.1 hu hn N).2 ha
  have htailorder := hta.analyticOrderAt_eq_zero.mpr htail.2
  have heq : product z b =ᶠ[𝓝 a]
      (fun w => (∏ k ∈ Finset.range N, boundaryFactor z b k w) * (∏' k, boundaryFactor z b (k+N) w)) :=
    eventually_of_mem (h.1.mem_nhds ha) (fun w hw =>
      HolomorphicProducts.product_prefix_tail G _ h.1 hu hn N w hw)
  have horder : analyticOrderAt (product z b) a =
      ∑ k ∈ Finset.range N, analyticOrderAt (boundaryFactor z b k) a := by
    rw [analyticOrderAt_congr heq]
    change analyticOrderAt ((fun w => ∏ k ∈ Finset.range N, boundaryFactor z b k w) *
      (fun w => ∏' k, boundaryFactor z b (k+N) w)) a = _
    rw [analyticOrderAt_mul ((Finset.range N).analyticAt_fun_prod (fun k _ => hau k)) hta,
      htailorder, add_zero, HolomorphicProducts.order_partial_product _ a hau N]
  have hlate : ∀ n, n ∉ Finset.range N → analyticOrderAt (boundaryFactor z b n) a = 0 := by
    intro n hn
    exact (hau n).analyticOrderAt_eq_zero.mpr (htail.1 n (by simpa using hn))
  refine ⟨hfin, ?_, ?_⟩
  · have hs : (∑' n, analyticOrderAt (boundaryFactor z b n) a) =
        ∑ n ∈ Finset.range N, analyticOrderAt (boundaryFactor z b n) a := tsum_eq_sum hlate
    rw [horder, ← hs]
    exact tsum_congr (factor_order h hb ha)
  · rw [horder]
    apply ENat.sum_ne_top.mpr
    intro n _
    rw [factor_order h hb ha n]
    split_ifs <;> simp


/-- A bound on every argument controls the full product through an absolutely
summable series of the normalized logarithms of the elementary factors. -/
lemma product_close_to_one (z b : ℕ → ℂ) {w : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1/2)
    (hq : ∀ n, ‖(z n - b n) / (w - b n)‖ ≤ δ) :
    ‖product z b w - 1‖ ≤ 4 * δ := by
  let q : ℕ → ℂ := fun n => (z n - b n) / (w - b n)
  let l : ℕ → ℂ := fun n => CanonicalFactors.logFactor (n+1) (q n)
  have hg0 : HasSum (fun n : ℕ => (1/2 : ℝ) ^ (n+1)) 1 := by
    apply (hasSum_nat_add_iff 1).mpr
    convert hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1) using 1; norm_num
  have hg : HasSum (fun n : ℕ => (2*δ) * (1/2 : ℝ) ^ (n+1)) (2*δ) := by
    simpa using hg0.mul_left (2*δ)
  have hl : ∀ n, ‖l n‖ ≤ (2*δ) * (1/2 : ℝ) ^ (n+1) := by
    intro n
    have hp : ‖q n‖ ^ (n+1+1) ≤ δ * (1/2 : ℝ) ^ (n+1) := by
      rw [pow_succ, mul_comm]
      exact mul_le_mul (hq n) (pow_le_pow_left₀ (norm_nonneg _) ((hq n).trans hδsmall) _)
        (pow_nonneg (norm_nonneg _) _) hδ.le
    exact (CanonicalFactors.norm_logFactor_le (n+1) (q n) ((hq n).trans hδsmall)).trans
      (by nlinarith)
  have hs : Summable l := hg.summable.of_norm_bounded hl
  have hsum : ‖∑' n, l n‖ ≤ 2*δ := hs.hasSum.norm_le_of_bounded hg hl
  have he : product z b w = Complex.exp (∑' n, l n) := by
    calc
      product z b w = ∏' n, Complex.exp (l n) := by
        apply tprod_congr
        intro n
        exact (CanonicalFactors.exp_logFactor (n+1) (q n)
          (lt_of_le_of_lt ((hq n).trans hδsmall) (by norm_num))).symm
      _ = _ := hs.hasSum.cexp.tprod_eq
  rw [he]
  exact (Complex.norm_exp_sub_one_le (hsum.trans (by linarith))).trans (by linarith)

theorem product_limit_at_infinity :
    Specs.D12Complex.Ch16.BoundaryFactorProduct.product_limit_at_infinity_type := by
  intro G z b h hb ε hε
  obtain ⟨C, hC, hzC⟩ := h.2.2.2.2.1.exists_pos_norm_le
  obtain ⟨B, hB, hbB⟩ := (nearest_bounded G z b h hb).exists_pos_norm_le
  obtain ⟨R₀, hR₀, hExt⟩ := h.2.1
  let δ : ℝ := min (1/4) (ε/8)
  have hd : 0 < δ := lt_min (by norm_num) (by positivity)
  have hdsmall : δ ≤ 1/2 := (min_le_left _ _).trans (by norm_num)
  have hde : 4*δ < ε := by
    have : δ ≤ ε/8 := min_le_right _ _
    linarith
  let R := (C+B)/δ + B + R₀ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, fun w hw => ⟨hExt w ?_, lt_of_le_of_lt ?_ hde⟩⟩
  · have : 0 < (C+B)/δ := div_pos (by linarith) hd
    dsimp [R] at hw
    linarith
  · apply product_close_to_one z b hd hdsmall
    intro n
    have hz : ‖z n‖ ≤ C := hzC _ (mem_range_self n)
    have hb' : ‖b n‖ ≤ B := hbB _ (mem_range_self n)
    have hnum : ‖z n - b n‖ ≤ C+B := (norm_sub_le _ _).trans (add_le_add hz hb')
    have hden : ‖w‖ - B ≤ ‖w - b n‖ := by
      have := norm_sub_norm_le w (b n)
      linarith
    have hlarge : (C+B)/δ < ‖w‖ - B := by
      dsimp [R] at hw
      linarith
    have hpos : 0 < ‖w - b n‖ := by
      have : 0 < (C+B)/δ := div_pos (by linarith) hd
      linarith
    rw [norm_div]
    apply (div_le_iff₀ hpos).mpr
    have hmul : C+B < (‖w‖-B)*δ := (div_lt_iff₀ hd).mp hlarge
    have : (‖w‖-B)*δ ≤ ‖w-b n‖*δ := mul_le_mul_of_nonneg_right hden hd.le
    nlinarith

end D12Complex.BoundaryFactorProduct
