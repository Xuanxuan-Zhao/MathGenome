import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.IntervalCalculus
import Mathlib.Data.List.Pairwise

/-! Independent statement of paper.tex, Lemma `p206:repeated-rolle`.
A marked point is paired with its positive multiplicity. The jet is the
closed-interval derivative data, including its one-sided endpoint values. -/
namespace NumAnalysis206.Approximation.RepeatedRolleSpec
open Set

def repeated_rolle_type : Prop :=
  ∀ {a b : ℝ} {N : ℕ} {g : ℝ → ℝ} {D : ℕ → ℝ → ℝ}
    (l : List (ℝ × ℕ)) (hne : l ≠ []),
    a ≤ b → 1 ≤ N →
    IntervalCalculusSpec.jetValue a b (N - 1) g D →
    l.Pairwise (fun p q => p.1 < q.1) →
    (∀ p ∈ l, 0 < p.2) →
    (∀ p ∈ l, p.1 ∈ Icc a b) →
    (l.map Prod.snd).sum = N →
    (∀ p ∈ l, ∀ j < p.2, D j p.1 = 0) →
    ∃ ξ ∈ Icc (l.head hne).1 (l.getLast hne).1, D (N - 1) ξ = 0

end NumAnalysis206.Approximation.RepeatedRolleSpec
