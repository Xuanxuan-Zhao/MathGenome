import MathGenome.Internal.Specs.D05.M02.Independence

/-!
Independent statement of K05.02.exchange (paper.tex:475–481).
Both lists use `Fin` indices, retaining repeated occurrences. An embedding
selects distinct positions in the original spanning list. The new list has
the same length, has `v i` at each selected position, and agrees with `w`
at every other position. No finite-dimensional instance or characteristic
restriction is assumed; finite generation is the stated spanning hypothesis.
-/

namespace Specs.D05.M02.Exchange

/-- The length inequality and replacement of exactly `r` distinct occurrences
of a spanning list by the given independent list, preserving spanning. -/
def exchange : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (r s : ℕ) (v : Fin r → V) (w : Fin s → V),
    LinearIndependent K v → Submodule.span K (Set.range w) = ⊤ →
      r ≤ s ∧ ∃ (e : Fin r ↪ Fin s) (u : Fin s → V),
        (∀ i, u (e i) = v i) ∧
        (∀ j, j ∉ Set.range e → u j = w j) ∧
        Submodule.span K (Set.range u) = ⊤

end Specs.D05.M02.Exchange
