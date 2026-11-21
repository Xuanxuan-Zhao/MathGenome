import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtModules
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StandardTableaux

/-! FR B01: independence in the original complex permutation module,
indexed by all standard tableaux of each partition, including size zero. -/
namespace Specs.AdvancedFiniteGroupRepresentations

def standard_polytabloids_linearIndependentType : Prop :=
  ∀ {n : ℕ} (p : Partition n),
    LinearIndependent ℂ (fun t : StandardTableau p => polytabloid t.val)

end Specs.AdvancedFiniteGroupRepresentations
