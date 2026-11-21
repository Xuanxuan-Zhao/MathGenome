import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.TutteDefinition
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.MinorRank
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Cocircuits

/-! W77: deletion–contraction as identities of bivariate integer polynomials.
The element belongs to the ground; no positivity or nonemptiness is imposed
on the minors. Loop and coloop have the original singleton-circuit and
all-bases definitions from W68. -/
namespace FiniteCombinatorics.Matroid.Expected
open scoped _root_.Matroid
universe u

def tutteLoop : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (e : α), e ∈ M.E →
    Loop M e → tutte M = MvPolynomial.X 1 * tutte (M ＼ {e})

def tutteColoop : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (e : α), e ∈ M.E →
    Coloop M e → tutte M = MvPolynomial.X 0 * tutte (M ／ {e})

def tutteDeletionContraction : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (e : α), e ∈ M.E →
    ¬ Loop M e → ¬ Coloop M e →
      tutte M = tutte (M ＼ {e}) + tutte (M ／ {e})

end FiniteCombinatorics.Matroid.Expected
