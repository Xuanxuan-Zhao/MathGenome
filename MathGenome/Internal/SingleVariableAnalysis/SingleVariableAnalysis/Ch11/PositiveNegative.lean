import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Absolute
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Nonnegative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PositiveNegative
import Mathlib.Order.OrderIsoNat

/-!
# The one-sided parts of a conditionally convergent real series

K03.11.rearrange_conditional, first proof paragraph (paper.tex:1097–1104).
If either part had a finite ordinary sum, the identities
`|a| = 2*p - a = a + 2*q` would force absolute convergence. Nonnegative
monotone convergence then gives divergence of both parts to +∞. Finiteness
of either sign set would give an eventually zero part, a contradiction.
The increasing enumerations of these infinite sets are exhaustive, and the
ordinary term test supplies their vanishing magnitudes.
-/

namespace SingleVariableAnalysis

open scoped BigOperators Topology ENNReal

noncomputable def positivePart (a : ℕ → ℝ) (n : ℕ) : ℝ := max (a n) 0
noncomputable def negativePart (a : ℕ → ℝ) (n : ℕ) : ℝ := max (-a n) 0

theorem positive_negative_part_identities (a : ℕ → ℝ) (n : ℕ) :
    0 ≤ positivePart a n ∧ 0 ≤ negativePart a n ∧
    a n = positivePart a n - negativePart a n ∧
    |a n| = positivePart a n + negativePart a n := by
  dsimp [positivePart, negativePart]
  rcases le_total 0 (a n) with h | h
  · simp [abs_of_nonneg h, h]
  · simp [abs_of_nonpos h, h]

private theorem abs_eq_twice_positive_sub (a : ℕ → ℝ) :
    (fun n => |a n|) = fun n => 2 * positivePart a n - a n := by
  funext n
  obtain ⟨_, _, h₁, h₂⟩ := positive_negative_part_identities a n
  linarith

private theorem abs_eq_add_twice_negative (a : ℕ → ℝ) :
    (fun n => |a n|) = fun n => a n + 2 * negativePart a n := by
  funext n
  obtain ⟨_, _, h₁, h₂⟩ := positive_negative_part_identities a n
  linarith

/-- Neither one-sided nonnegative part can have a finite ordinary sum. -/
theorem conditional_parts_not_convergent (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) :
    ¬ RealSeriesConverges (positivePart a) ∧
    ¬ RealSeriesConverges (negativePart a) := by
  obtain ⟨⟨S, hS⟩, hAbs⟩ := ha
  have hSt := (realSequenceConverges_iff _ _).mp hS
  constructor
  · rintro ⟨P, hP⟩
    apply hAbs
    refine ⟨2 * P - S, (realSequenceConverges_iff _ _).mpr ?_⟩
    have ht := (((realSequenceConverges_iff _ _).mp hP).const_mul 2).sub hSt
    change Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), |a n|)
      Filter.atTop (𝓝 (2 * P - S))
    simp_rw [congrFun (abs_eq_twice_positive_sub a)]
    simpa only [realPartialSum, Finset.sum_sub_distrib,
      ← Finset.mul_sum] using ht
  · rintro ⟨Q, hQ⟩
    apply hAbs
    refine ⟨S + 2 * Q, (realSequenceConverges_iff _ _).mpr ?_⟩
    have ht := hSt.add (((realSequenceConverges_iff _ _).mp hQ).const_mul 2)
    change Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), |a n|)
      Filter.atTop (𝓝 (S + 2 * Q))
    simp_rw [congrFun (abs_eq_add_twice_negative a)]
    simpa only [realPartialSum, Finset.sum_add_distrib,
      ← Finset.mul_sum] using ht

theorem conditional_parts_diverge (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) :
    DivergesToPosInfinity (realPartialSum (positivePart a)) ∧
    DivergesToPosInfinity (realPartialSum (negativePart a)) := by
  have hn := conditional_parts_not_convergent a ha
  exact ⟨nonnegative_series_diverges_to_posInfinity _
      (fun n => (positive_negative_part_identities a n).1) hn.1,
    nonnegative_series_diverges_to_posInfinity _
      (fun n => (positive_negative_part_identities a n).2.1) hn.2⟩

theorem conditional_parts_extendedSum (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) :
    nonnegativeExtendedSum (positivePart a) = ∞ ∧
    nonnegativeExtendedSum (negativePart a) = ∞ := by
  have hn := conditional_parts_not_convergent a ha
  exact ⟨(nonnegative_extendedSum_eq_top_iff _
      (fun n => (positive_negative_part_identities a n).1)).mpr hn.1,
    (nonnegative_extendedSum_eq_top_iff _
      (fun n => (positive_negative_part_identities a n).2.1)).mpr hn.2⟩

theorem conditional_negative_terms_diverge (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) :
    DivergesToNegInfinity (realPartialSum (fun n => -negativePart a n)) := by
  intro B
  obtain ⟨N, hN⟩ := (conditional_parts_diverge a ha).2 (-B)
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  dsimp [realPartialSum] at *
  rw [Finset.sum_neg_distrib]
  linarith

/-- A nonnegative series with only finitely many nonzero terms has a finite sum. -/
theorem nonnegative_series_infinite_positive_indices (b : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hd : ¬ RealSeriesConverges b) :
    Set.Infinite {n | 0 < b n} := by
  intro hf
  obtain ⟨m, hm⟩ := hf.bddAbove
  apply hd
  apply (real_series_finite_changes_iff (fun _ => 0) b m ?_).mp
  · refine ⟨0, ?_⟩
    intro ε hε
    exact ⟨0, fun n _ => by simpa [realPartialSum] using hε⟩
  · intro n hn
    have hnot : ¬ 0 < b n := fun h => (not_le_of_gt hn) (hm h)
    exact le_antisymm (le_of_not_gt hnot) (hb n)

theorem conditional_sign_sets_infinite (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) :
    Set.Infinite {n | 0 < a n} ∧ Set.Infinite {n | a n < 0} := by
  have hn := conditional_parts_not_convergent a ha
  have hp := nonnegative_series_infinite_positive_indices (positivePart a)
    (fun n => (positive_negative_part_identities a n).1) hn.1
  have hq := nonnegative_series_infinite_positive_indices (negativePart a)
    (fun n => (positive_negative_part_identities a n).2.1) hn.2
  simpa only [positivePart, negativePart, lt_max_iff, lt_self_iff_false, or_false,
    neg_pos] using And.intro hp hq

theorem conditional_list_magnitudes_tendToZero (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) (r : ℕ → ℕ) (hr : StrictMono r) :
    RealSequenceConverges (fun j => |a (r j)|) 0 := by
  have h := real_series_term_limit a ha.1
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun j hj => ?_⟩
  simpa only [sub_zero, abs_abs] using hN (r j) (hj.trans (hr.id_le j))

theorem conditional_sign_lists (a : ℕ → ℝ)
    (ha : RealSeriesConditionallyConverges a) :
    ∃ r s : ℕ → ℕ, StrictMono r ∧ StrictMono s ∧
      Set.range r = {n | 0 < a n} ∧ Set.range s = {n | a n < 0} ∧
      RealSequenceConverges (fun j => |a (r j)|) 0 ∧
      RealSequenceConverges (fun j => |a (s j)|) 0 := by
  classical
  have hi := conditional_sign_sets_infinite a ha
  have := hi.1.to_subtype
  have := hi.2.to_subtype
  let r := Nat.orderEmbeddingOfSet {n | 0 < a n}
  let s := Nat.orderEmbeddingOfSet {n | a n < 0}
  exact ⟨r, s, r.strictMono, s.strictMono,
    Nat.orderEmbeddingOfSet_range _, Nat.orderEmbeddingOfSet_range _,
    conditional_list_magnitudes_tendToZero a ha r r.strictMono,
    conditional_list_magnitudes_tendToZero a ha s s.strictMono⟩

end SingleVariableAnalysis
