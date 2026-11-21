import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Tabloids

/-! FR A03 (row--column test). A collision is witnessed by two distinct labels
in one column of the first tableau and one row of the second. -/
namespace Specs.AdvancedFiniteGroupRepresentations

def RowColumnCollision {n : ℕ} {p q : Partition n} (t : Tableau p) (u : Tableau q) : Prop :=
  ∃ a b : Fin n, a ≠ b ∧ labelColumn t a = labelColumn t b ∧ labelRow u a = labelRow u b

def RowColumnCollisionType :=
  {n : ℕ} → {p q : Partition n} → Tableau p → Tableau q → Prop

def row_column_testType : Prop :=
  ∀ {n : ℕ} {p q : Partition n} (t : Tableau p) (u : Tableau q),
    ¬ dominates p q → RowColumnCollision t u

def row_column_uniqueType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t u : Tableau p),
    ¬ RowColumnCollision t u →
      ∃! c : columnSubgroup t, tabloid u = tabloid (c.val • t)

end Specs.AdvancedFiniteGroupRepresentations
