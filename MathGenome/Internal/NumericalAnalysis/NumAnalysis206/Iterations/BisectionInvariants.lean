import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.BisectionInvariants
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Iterations.BracketExistence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NumAnalysis206.Iterations.BisectionInvariants

open Specs.NumAnalysis206.Iterations.BisectionInvariants

/-- One of the two exact halves has a nonpositive endpoint product. -/
theorem legal_half_exists (f : ℝ → ℝ) (a b : ℝ) (hsign : f a * f b ≤ 0) :
    ∃ c d, LegalHalf f a b c d := by
  have h : f a * f (midpoint a b) ≤ 0 ∨ f (midpoint a b) * f b ≤ 0 := by
    rcases mul_nonpos_iff.mp hsign with h | h
    · by_cases hm : 0 ≤ f (midpoint a b)
      · exact Or.inr (mul_nonpos_of_nonneg_of_nonpos hm h.2)
      · exact Or.inl (mul_nonpos_of_nonneg_of_nonpos h.1 (le_of_not_ge hm))
    · by_cases hm : 0 ≤ f (midpoint a b)
      · exact Or.inl (mul_nonpos_of_nonpos_of_nonneg h.1 hm)
      · exact Or.inr (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hm) h.2)
  rcases h with h | h
  · exact ⟨a, midpoint a b, Or.inl ⟨rfl, rfl⟩, h⟩
  · exact ⟨midpoint a b, b, Or.inr ⟨rfl, rfl⟩, h⟩

theorem step_available : stepAvailability := by
  intro f a b _ hsign
  refine ⟨legal_half_exists f a b hsign, ?_, ?_, ?_⟩
  · intro h; exact ⟨Or.inl rfl, h⟩
  · intro h; exact ⟨Or.inr (Or.inl rfl), h⟩
  · intro h; exact ⟨Or.inr (Or.inr rfl), h⟩

theorem half_properties : halfProperties := by
  intro f a b c d hab h
  rcases h with ⟨hshape, hsign⟩
  rcases hshape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨?_, ?_, hsign, ?_⟩
    · dsimp [midpoint]; linarith
    · intro x hx
      dsimp [midpoint] at hx
      exact ⟨hx.1, by linarith [hx.2]⟩
    · dsimp [midpoint]; ring
  · refine ⟨?_, ?_, hsign, ?_⟩
    · dsimp [midpoint]; linarith
    · intro x hx
      dsimp [midpoint] at hx
      exact ⟨by linarith [hx.1], hx.2⟩
    · dsimp [midpoint]; ring

/-- Induction on completed updates; no continuity is needed for these invariants. -/
theorem interval_invariants (f : ℝ → ℝ) (a b : ℝ) (N : ℕ)
    (hab : a < b) (hsign : f a * f b ≤ 0) (r : FiniteRun f a b N) :
    ∀ n, n ≤ N →
      r.left n < r.right n ∧
      Set.Icc (r.left n) (r.right n) ⊆ Set.Icc a b ∧
      f (r.left n) * f (r.right n) ≤ 0 ∧
      r.right n - r.left n = (1 / 2 : ℝ)^n * (b-a) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [r.left_zero, r.right_zero, pow_zero, one_mul]
    exact ⟨hab, Set.Subset.rfl, hsign, rfl⟩
  | succ n ih =>
    intro hn
    have hn' : n < N := Nat.lt_of_succ_le hn
    obtain ⟨hlt, hsub, hsign', hwidth⟩ := ih (Nat.le_of_lt hn')
    obtain ⟨hlt', hsub', hsign'', hhalf⟩ :=
      half_properties f (r.left n) (r.right n) (r.left (n+1)) (r.right (n+1))
        hlt (r.step n hn')
    refine ⟨hlt', hsub'.trans hsub, hsign'', ?_⟩
    rw [hhalf, hwidth, pow_succ]
    ring

/-- Any point in a real interval is at distance at most half its width
from its exact midpoint. -/
theorem midpoint_distance (a b p : ℝ) (hp : p ∈ Set.Icc a b) :
    |midpoint a b - p| ≤ (b-a)/2 := by
  apply abs_le.mpr
  dsimp [midpoint]
  constructor <;> linarith [hp.1, hp.2]

theorem finite_invariants : finiteInvariants := by
  intro f a b N hab hf hsign r
  constructor
  · intro n hn
    obtain ⟨hlt, hsub, hsign', hwidth⟩ := interval_invariants f a b N hab hsign r n hn
    refine ⟨hlt, hsub, hsign', hwidth, ?_⟩
    obtain ⟨p, hp, hroot⟩ := BracketExistence.root_exists_closed
      (r.left n) (r.right n) f hlt (hf.mono hsub) hsign'
    refine ⟨p, hp, hroot, ?_⟩
    calc
      |midpoint (r.left n) (r.right n) - p| ≤ (r.right n - r.left n)/2 :=
        midpoint_distance _ _ _ hp
      _ = (1 / 2 : ℝ)^(n+1) * (b-a) := by rw [hwidth, pow_succ]; ring
  · intro n hn
    have hlt := (interval_invariants f a b N hab hsign r n (Nat.le_of_lt hn)).1
    exact (half_properties f _ _ _ _ hlt (r.step n hn)).2.1

theorem return_correctness : returnCorrectness := by
  intro f a b N hab _ hsign r n hn p hp
  obtain ⟨hlt, hsub, _, _⟩ := interval_invariants f a b N hab hsign r n hn
  have hmem : p ∈ Set.Icc (r.left n) (r.right n) := by
    rcases hp.1 with h | h | h
    · subst p; exact ⟨le_rfl, hlt.le⟩
    · rw [h]; dsimp [midpoint]; constructor <;> linarith
    · subst p; exact ⟨hlt.le, le_rfl⟩
  exact ⟨hmem, hsub hmem, hp.2⟩

end NumAnalysis206.Iterations.BisectionInvariants
