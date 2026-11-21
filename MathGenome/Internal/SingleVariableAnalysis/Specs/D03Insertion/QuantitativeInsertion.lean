import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.LocalizedComparison

/-! The complete insertion theorem, including both quantitative bounds and
the exact zero-error case. Real normed spaces include ℝ and ℂ with their
usual norms and real scalar multiplication. No regularity of f is assumed. -/

namespace D03Insertion.Specification

def quantitative_insertionType : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
    {a b : ℝ}, a < b → ∀ {s n : ℕ}, 1 ≤ s → 1 ≤ n →
    ∀ (p : Fin (s + 1) → ℝ) (q : Fin (n + 1) → ℝ),
    StrictMono p → StrictMono q →
    p 0 = a → p (Fin.last s) = b →
    q 0 = a → q (Fin.last n) = b →
    ∀ (f : Set.Icc a b → K) (M : ℝ), 0 ≤ M →
    (∀ x, ‖f x‖ ≤ M) →
    ∀ ξ : Fin n → Set.Icc a b, Legal q ξ →
    ∃ (t : ℕ) (r : Fin (t + 1) → ℝ) (ζ : Fin t → Set.Icc a b),
      1 ≤ t ∧ StrictMono r ∧ r 0 = a ∧ r (Fin.last t) = b ∧
      nodes r = nodes p ∪ nodes q ∧ Legal r ζ ∧
      (∀ i, i ∉ marked p q → ∃ j,
        r j.castSucc = q i.castSucc ∧ r j.succ = q i.succ ∧ ζ j = ξ i) ∧
      ‖taggedSum f q ξ - taggedSum f r ζ‖ ≤
        2 * M * ((s - 1 : ℕ) : ℝ) * mesh q ∧
      ‖taggedSum f q ξ - taggedSum f r ζ‖ ≤
        4 * M * ((s - 1 : ℕ) : ℝ) * mesh q ∧
      (M * ((s - 1 : ℕ) : ℝ) = 0 →
        taggedSum f q ξ = taggedSum f r ζ)

end D03Insertion.Specification
