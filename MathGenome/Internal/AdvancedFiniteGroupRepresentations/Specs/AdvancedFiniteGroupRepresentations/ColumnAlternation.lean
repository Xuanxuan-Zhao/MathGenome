import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtModules
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.RowColumnTest

/-! Column alternation in FR A05, including its arbitrary-shape test.
The action and first-linear Hermitian form are the canonical upstream objects. -/
namespace Specs.AdvancedFiniteGroupRepresentations

def columnAlternator_collisionType : Prop :=
  ∀ {n : ℕ} {p q : Partition n} (t : Tableau p) (u : Tableau q),
    RowColumnCollision t u →
      groupAlgebraAction q (columnAlternator t) (MonoidAlgebra.single (tabloid u) 1) = 0

def columnAlternator_column_tabloidType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p) (c : columnSubgroup t),
    groupAlgebraAction p (columnAlternator t)
      (MonoidAlgebra.single (tabloid (c.val • t)) 1) =
        permutationSign c.val • polytabloid t

def columnAlternator_rank_oneType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p) (x : PermutationModule p),
    groupAlgebraAction p (columnAlternator t) x =
      tabloidHermitian x (polytabloid t) • polytabloid t

end Specs.AdvancedFiniteGroupRepresentations
