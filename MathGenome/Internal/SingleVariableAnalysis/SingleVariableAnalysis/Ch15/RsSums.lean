import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsSums
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Partitions
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Archimedean
import Mathlib.Tactic.Linarith

/-! K03.15.rs_sums: refinement Stieltjes sums and their Cauchy criterion.
Completeness is supplied by the proved real/complex sequence criteria. No
monotonicity, variation, continuity, or mesh convergence is assumed. -/
namespace SingleVariableAnalysis.Stieltjes
open Riemann
universe u
namespace S
export Specs.SingleVariableAnalysis.Ch15.RsSums
  (boundedOnValue sumValue limitValue cauchyForwardValue integralValue cauchyValue)
end S

abbrev BoundedOn := @S.boundedOnValue
noncomputable abbrev taggedSum := @S.sumValue
abbrev RefinementLimit := @S.limitValue
abbrev RefinementCauchy := @S.cauchyForwardValue
abbrev HasIntegral := @S.integralValue
abbrev CauchySums := @S.cauchyValue

variable {E : Type u} [NormedAddCommGroup E] [Module ℝ E]

omit [Module ℝ E] in
private theorem triangle (x y z : E) : ‖x-z‖ ≤ ‖x-y‖ + ‖y-z‖ := by
  simpa only [sub_add_sub_cancel] using norm_add_le (x-y) (y-z)

/-- Uniqueness uses a tag on the union of the two controlling partitions. -/
theorem refinementLimit_unique {a b : ℝ} {f : ℝ → E} {α : ℝ → ℝ} {I J : E}
    (hI : RefinementLimit a b f α I) (hJ : RefinementLimit a b f α J) : I = J := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨P, hP⟩ := hI (ε/2) (half_pos hε)
  obtain ⟨Q, hQ⟩ := hJ (ε/2) (half_pos hε)
  obtain ⟨R, _, hRP, hRQ⟩ := common_refinement P Q
  obtain ⟨t⟩ := tags_exist R
  have h₁ := hP R hRP t
  have h₂ := hQ R hRQ t
  have ht := triangle I (taggedSum R t f α) J
  have h₁' : ‖I - taggedSum R t f α‖ < ε/2 := by
    rw [norm_sub_rev]; exact h₁
  linarith

theorem refinementCauchy_of_limit {a b : ℝ} {f : ℝ → E} {α : ℝ → ℝ} {I : E}
    (h : RefinementLimit a b f α I) : RefinementCauchy a b f α := by
  intro ε hε
  obtain ⟨P₀, hP₀⟩ := h (ε/2) (half_pos hε)
  refine ⟨P₀, ?_⟩
  intro P hP t Q hQ v
  have h₁ := hP₀ P hP t
  have h₂ := hP₀ Q hQ v
  have ht := triangle (taggedSum P t f α) I (taggedSum Q v f α)
  rw [norm_sub_rev I] at ht
  linarith

private theorem reciprocal_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, 1 / ((n : ℝ)+1) < ε := by
  obtain ⟨N, _, hN⟩ := reciprocal_tail ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h := hN (n+1) (by omega)
  simpa only [Nat.cast_add, Nat.cast_one, abs_of_pos (one_div_pos.mpr (by positivity :
    0 < (n : ℝ)+1))] using h

/-- A directed Cauchy family gives a Cauchy sequence by choosing controlling
partitions at errors 1/(n+1). To compare two selected sums, take a common
refinement and use one error from each controlling partition. This avoids
requiring that the selected partitions themselves form a cofinal sequence. -/
theorem exists_refinementLimit_of_cauchy
    (complete : ∀ s : ℕ → E,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖s n-s m‖ < ε) →
      ∃ I : E, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖s n-I‖ < ε)
    {a b : ℝ} {f : ℝ → E} {α : ℝ → ℝ}
    (hc : RefinementCauchy a b f α) : ∃ I, RefinementLimit a b f α I := by
  classical
  have hp (n : ℕ) : 0 < 1 / ((n : ℝ)+1) := by positivity
  choose P hP using fun (n : ℕ) => hc (1 / ((n : ℝ)+1)) (hp n)
  let t : ∀ n, Tagging (P n) := fun n => Classical.choice (tags_exist (P n))
  let s : ℕ → E := fun n => taggedSum (P n) (t n) f α
  have compare (n m : ℕ) : ‖s n-s m‖ < 1/((n : ℝ)+1) + 1/((m : ℝ)+1) := by
    obtain ⟨R, _, hRn, hRm⟩ := common_refinement (P n) (P m)
    obtain ⟨v⟩ := tags_exist R
    have hn := hP n (P n) (refinement_laws (P n) (P n) (P n)).1 (t n) R hRn v
    have hm := hP m R hRm v (P m) (refinement_laws (P m) (P m) (P m)).1 (t m)
    exact (triangle _ (taggedSum R v f α) _).trans_lt (add_lt_add hn hm)
  have hs : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖s n-s m‖ < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := reciprocal_small (ε/2) (half_pos hε)
    refine ⟨N, ?_⟩
    intro m hm n hn
    have h₁ := hN n hn
    have h₂ := hN m hm
    have h₃ := compare n m
    linarith
  obtain ⟨I, hI⟩ := complete s hs
  refine ⟨I, ?_⟩
  intro ε hε
  have hthird : 0 < ε/3 := by linarith
  obtain ⟨N, hN⟩ := reciprocal_small (ε/3) hthird
  obtain ⟨M, hM⟩ := hI (ε/3) hthird
  let m := max N M
  refine ⟨P N, ?_⟩
  intro Q hQ v
  obtain ⟨R, _, hRQ, hRm⟩ := common_refinement Q (P m)
  obtain ⟨w⟩ := tags_exist R
  have hRN : Refines R (P N) := Finset.Subset.trans hQ hRQ
  have h₁ := hP N Q hQ v R hRN w
  have h₂ := hP m R hRm w (P m) (refinement_laws (P m) (P m) (P m)).1 (t m)
  have h₃ := hM m (le_max_right N M)
  have h₄ := hN N le_rfl
  have h₅ := hN m (le_max_left N M)
  have ht₁ := triangle (taggedSum Q v f α) (taggedSum R w f α) (s m)
  have ht₂ := triangle (taggedSum Q v f α) (s m) I
  dsimp [s] at ht₁ ht₂ h₃
  linarith

theorem integral_unique : Specs.SingleVariableAnalysis.Ch15.RsSums.unique := by
  intro E _ _ a b f α I J hI hJ
  have hi := hI.2.2
  have hj := hJ.2.2
  by_cases hab : a ≤ b
  · simp only [ite_eq_left hab] at hi hj
    exact refinementLimit_unique hi hj
  · simp only [ite_eq_right hab] at hi hj
    exact neg_injective (refinementLimit_unique hi hj)

private theorem cauchy_criterion
    (complete : ∀ s : ℕ → E,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖s n-s m‖ < ε) →
      ∃ I : E, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖s n-I‖ < ε)
    (a b : ℝ) (f : ℝ → E) (α : ℝ → ℝ) :
    (∃ I, HasIntegral a b f α I) ↔ CauchySums a b f α := by
  constructor
  · rintro ⟨I, hf, hα, hI⟩
    refine ⟨hf, hα, ?_⟩
    by_cases hab : a ≤ b
    · simp only [ite_eq_left hab] at hI ⊢
      exact refinementCauchy_of_limit hI
    · simp only [ite_eq_right hab] at hI ⊢
      exact refinementCauchy_of_limit hI
  · rintro ⟨hf, hα, hc⟩
    by_cases hab : a ≤ b
    · simp only [ite_eq_left hab] at hc
      obtain ⟨I, hI⟩ := exists_refinementLimit_of_cauchy complete hc
      exact ⟨I, hf, hα, by simpa only [ite_eq_left hab] using hI⟩
    · simp only [ite_eq_right hab] at hc
      obtain ⟨I, hI⟩ := exists_refinementLimit_of_cauchy complete hc
      exact ⟨-I, hf, hα, by simpa only [ite_eq_right hab, neg_neg] using hI⟩

theorem real_cauchy_criterion : Specs.SingleVariableAnalysis.Ch15.RsSums.realCauchy := by
  apply cauchy_criterion
  intro s hs
  have hs' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m ≥ N, ∀ n ≥ N, |s n-s m| < ε := by
    simpa only [Real.norm_eq_abs] using hs
  obtain ⟨I, hI⟩ := (SingleVariableAnalysis.real_cauchy_criterion s).mpr hs'
  refine ⟨I, ?_⟩
  simpa only [RealSequenceConverges, SequenceEventually, Real.norm_eq_abs] using hI

theorem complex_cauchy_criterion : Specs.SingleVariableAnalysis.Ch15.RsSums.complexCauchy := by
  apply cauchy_criterion
  intro s hs
  exact (SingleVariableAnalysis.complex_cauchy_criterion s).mpr hs

theorem degenerate_sum : Specs.SingleVariableAnalysis.Ch15.RsSums.degenerateSum := by
  intro E _ _ a P t f α
  have : IsEmpty (Fin P.n) := Fin.isEmpty_iff.mpr (n_eq_zero_of_degenerate a P)
  simp [S.sumValue]

omit [Module ℝ E] in
private theorem boundedOn_singleton (a : ℝ) (f : ℝ → E) : BoundedOn a a f := by
  refine ⟨‖f a‖, ?_⟩
  intro x hx
  have hx' : x = a := le_antisymm hx.2 hx.1
  simpa only [hx'] using (le_rfl : ‖f a‖ ≤ ‖f a‖)

private theorem integral_zero_singleton (a : ℝ) (f : ℝ → E) (α : ℝ → ℝ) :
    HasIntegral a a f α 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [min_self, max_self] using boundedOn_singleton a f
  · simpa only [min_self, max_self] using boundedOn_singleton a α
  · simp only [ite_eq_left le_rfl]
    intro ε hε
    refine ⟨emptyPartition a, ?_⟩
    intro P _ t
    rw [degenerate_sum a P t f α, sub_self, norm_zero]
    exact hε

theorem degenerate_integral : Specs.SingleVariableAnalysis.Ch15.RsSums.degenerateIntegral := by
  intro E _ _ a f α I
  constructor
  · intro hI
    exact integral_unique a a f α I 0 hI (integral_zero_singleton a f α)
  · rintro rfl
    exact integral_zero_singleton a f α

theorem reverse_orientation : Specs.SingleVariableAnalysis.Ch15.RsSums.orientation := by
  intro E _ _ a b f α I
  rcases lt_trichotomy a b with hab | rfl | hba
  · simp only [S.integralValue, ite_eq_left (le_of_lt hab), ite_eq_right (not_le.mpr hab),
      min_eq_left (le_of_lt hab), min_eq_right (le_of_lt hab),
      max_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab), neg_neg]
  · rw [degenerate_integral, degenerate_integral]
    exact neg_eq_zero.symm
  · simp only [S.integralValue, ite_eq_left (le_of_lt hba), ite_eq_right (not_le.mpr hba),
      min_eq_left (le_of_lt hba), min_eq_right (le_of_lt hba),
      max_eq_left (le_of_lt hba), max_eq_right (le_of_lt hba)]

open scoped BigOperators

theorem real_sum_formula : Specs.SingleVariableAnalysis.Ch15.RsSums.realSumFormula := by
  intro a b P t f α
  simp only [S.sumValue, smul_eq_mul, mul_comm]

theorem complex_sum_formula : Specs.SingleVariableAnalysis.Ch15.RsSums.complexSumFormula := by
  intro a b P t f α
  unfold S.sumValue
  apply Finset.sum_congr rfl
  intro i _
  change ((α (P.point i.succ) - α (P.point i.castSucc) : ℝ) : ℂ) * f (t i) = _
  exact mul_comm _ _

theorem integral_iff_of_le : Specs.SingleVariableAnalysis.Ch15.RsSums.forwardIntegralIff := by
  intro E _ _ a b hab f α I
  simp only [S.integralValue, min_eq_left hab, max_eq_right hab, ite_eq_left hab,
    S.limitValue]

end SingleVariableAnalysis.Stieltjes
