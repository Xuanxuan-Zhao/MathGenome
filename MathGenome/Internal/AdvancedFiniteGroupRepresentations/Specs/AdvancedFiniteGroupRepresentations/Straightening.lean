import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.GarnirRelations

/-! FR-B02 (source lines 505–558): the Garnir relation is the upstream
`garnir_relationType`, with arbitrary left transversals and its full descent
hypotheses. This module states the remaining straightening conclusion for
all tableaux of every partition, including the partition of zero. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The complex span of the polytabloids indexed by standard tableaux. -/
def standardPolytabloidSpan {n : ℕ} (p : Partition n) : Submodule ℂ (PermutationModule p) :=
  Submodule.span ℂ (Set.range (fun t : StandardTableau p => polytabloid t.val))

def standardPolytabloidSpanType :=
  {n : ℕ} → (p : Partition n) → Submodule ℂ (PermutationModule p)

def polytabloid_straighteningType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p), polytabloid t ∈ standardPolytabloidSpan p

def standardPolytabloids_spanType : Prop :=
  ∀ {n : ℕ} (p : Partition n), standardPolytabloidSpan p = spechtSpan p

def polytabloid_linearCombinationType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p),
    ∃ (s : Finset (StandardTableau p)) (a : StandardTableau p → ℂ),
      polytabloid t = ∑ u ∈ s, a u • polytabloid u.val

end Specs.AdvancedFiniteGroupRepresentations
