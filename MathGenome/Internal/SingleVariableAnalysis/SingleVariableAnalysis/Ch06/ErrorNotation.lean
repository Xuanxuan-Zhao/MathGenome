import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.OAlgebra
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.ErrorNotation

/-!
# Comparing error orders

K03.06.error_notation, paper.tex:2888–2896. All approaches below are real,
two-sided and punctured. The normed scalar formulation covers ℝ and ℂ.
For the strictness witness, the two norm ratios are |h|^α and |h|^(α-1).
The first tends to zero and the second to positive infinity. Norms retain
the absolute values needed for odd n on the negative side of zero.

Library provenance: `Asymptotics.isLittleO_pow_pow` proves the integer-power
comparison by factoring powers and multiplying a bounded factor by a factor
tending to zero. `tendsto_rpow_neg_nhdsGT_zero` uses reciprocation and
positive-power growth. The accepted real-power bridge identifies these
canonical real powers with the source exp/log construction at positive bases.
-/

namespace SingleVariableAnalysis
open Filter
open scoped Topology

theorem nextOrder_bigO_implies_littleO {K : Type} [RCLike K]
    (n : ℕ) (r : ℝ → K)
    (hr : ScalarBigO (𝓝[≠] (0 : ℝ)) r (fun h => (h : K) ^ (n + 1))) :
    ScalarLittleO (𝓝[≠] (0 : ℝ)) r (fun h => (h : K) ^ n) := by
  apply (scalarLittleO_iff_isLittleO _ _ _).mpr
  apply ((scalarBigO_iff_isBigO _ _ _).mp hr).trans_isLittleO
  apply (Asymptotics.isLittleO_pow_pow (𝕜 := K) (Nat.lt_succ_self n)).comp_tendsto
  simpa using (RCLike.continuous_ofReal (K := K)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)

/-- Exact norm ratio on the punctured domain, for any integer comparison order. -/
lemma fractionalPower_norm_ratio (n k : ℕ) (α h : ℝ) (hh : h ≠ 0) :
    ‖|h| ^ ((n : ℝ) + α)‖ / ‖h ^ k‖ =
      |h| ^ ((n : ℝ) + α - (k : ℝ)) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _),
    Real.norm_eq_abs, abs_pow, ← Real.rpow_natCast,
    ← Real.rpow_sub (abs_pos.mpr hh)]

theorem fractionalOrder_real_littleO (n : ℕ) (α : ℝ) (hα : 0 < α) (_hα1 : α < 1) :
    ScalarLittleO (𝓝[≠] (0 : ℝ))
      (fun h => |h| ^ ((n : ℝ) + α)) (fun h => h ^ n) := by
  have hlim : Tendsto (fun h : ℝ => |h| ^ α) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    (tendsto_abs_nhdsNE_zero.mono_right nhdsWithin_le_nhds).rpow_const_nhds_zero hα
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε), self_mem_nhdsWithin] with h hb hh
  have hne : h ≠ 0 := by simpa using hh
  have hratio : ‖|h| ^ ((n : ℝ) + α)‖ / ‖h ^ n‖ < ε := by
    rw [fractionalPower_norm_ratio n n α h hne]
    simpa only [add_sub_cancel_left] using hb
  exact (div_le_iff₀ (norm_pos_iff.mpr (pow_ne_zero n hne))).mp hratio.le

/-- The norm ratio to the next power is unbounded in the two-sided approach. -/
lemma fractionalOrder_ratio_tendsto_atTop (n : ℕ) (α : ℝ) (hα1 : α < 1) :
    Tendsto (fun h : ℝ => ‖|h| ^ ((n : ℝ) + α)‖ / ‖h ^ (n + 1)‖)
      (𝓝[≠] (0 : ℝ)) atTop := by
  have hlim := (tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hα1)).comp
    tendsto_abs_nhdsNE_zero
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := by simpa using hh
  change |h| ^ (α - 1) = _
  rw [fractionalPower_norm_ratio n (n + 1) α h hne]
  congr 1
  push_cast
  ring

theorem fractionalOrder_real_not_bigO (n : ℕ) (α : ℝ) (_hα : 0 < α) (hα1 : α < 1) :
    ¬ ScalarBigO (𝓝[≠] (0 : ℝ))
      (fun h => |h| ^ ((n : ℝ) + α)) (fun h => h ^ (n + 1)) := by
  rintro ⟨C, _hC, hbound⟩
  have hlarge := (fractionalOrder_ratio_tendsto_atTop n α hα1).eventually_gt_atTop C
  obtain ⟨h, hb, hl, hh⟩ :=
    (hbound.and (hlarge.and self_mem_nhdsWithin)).exists
  have hne : h ≠ 0 := by simpa using hh
  have hle := (div_le_iff₀ (norm_pos_iff.mpr (pow_ne_zero (n + 1) hne))).mpr hb
  exact (not_lt_of_ge hle) hl

/-- The real strictness witness, embedded in either manuscript scalar field. -/
theorem fractionalOrder_littleO {K : Type} [RCLike K]
    (n : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ScalarLittleO (𝓝[≠] (0 : ℝ))
      (fun h => ((|h| ^ ((n : ℝ) + α) : ℝ) : K)) (fun h => (h : K) ^ n) := by
  intro ε hε
  filter_upwards [fractionalOrder_real_littleO n α hα hα1 ε hε] with h hh
  simpa only [norm_pow, Real.norm_eq_abs, RCLike.norm_ofReal] using hh

theorem fractionalOrder_not_bigO {K : Type} [RCLike K]
    (n : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ¬ ScalarBigO (𝓝[≠] (0 : ℝ))
      (fun h => ((|h| ^ ((n : ℝ) + α) : ℝ) : K)) (fun h => (h : K) ^ (n + 1)) := by
  rintro ⟨C, hC, hb⟩
  apply fractionalOrder_real_not_bigO n α hα hα1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with h hh
  simpa only [norm_pow, Real.norm_eq_abs, RCLike.norm_ofReal] using hh

end SingleVariableAnalysis
