import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Pi

/-! Independent specification of Lemma 1.3, paper.tex, dense transversal tuples.
Parts are finite sets; no disjointness assumption is imposed. -/

universe u
namespace Specs.P205.Extremal

/-- Every fixed positive density in a bounded product contains a fixed finite box. -/
def TransversalDensityStatement : Prop :=
  ∀ (r t : ℕ), 1 ≤ r → 1 ≤ t → ∀ (c : ℝ), 0 < c → c ≤ 1 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (α : Type u) [DecidableEq α]
        (V : Fin r → Finset α) (E : Finset (Fin r → α)),
        (∀ i, (V i).card ≤ n) →
        (∀ x ∈ E, ∀ i, x i ∈ V i) →
        c * (n : ℝ) ^ r ≤ (E.card : ℝ) →
        ∃ T : Fin r → Finset α,
          (∀ i, T i ⊆ V i ∧ (T i).card = t) ∧
          ∀ x : Fin r → α, (∀ i, x i ∈ T i) → x ∈ E

end Specs.P205.Extremal
