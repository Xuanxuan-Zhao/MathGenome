import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.YoungPermutationCharacter
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CharacteristicIsometry

/-! Young's rule (FR-C06, source lines 1099–1112). The ordered content is
`μ : Fin r → ℕ`; no positive-row or length restriction is imposed. In
particular empty rows and the empty alphabet are retained. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Multiplicity is the dimension of the actual space of equivariant maps
from the Specht representation to the ordered-row permutation module. -/
def orderedYoungMultiplicity {n r : ℕ} (lam : Partition n) (μ : Fin r → ℕ)
    (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule lam)) : ℕ :=
  Module.finrank ℂ (Representation.IntertwiningMap ρ (orderedRowRepresentation μ))

/-- Count fillings of the actual diagram which are weak along rows, strict
down columns, and have the prescribed ordered content. -/
def semistandardContentCount {n r : ℕ} (lam : Partition n) (μ : Fin r → ℕ) : ℕ :=
  Nat.card {T : SemistandardFilling lam r //
    tableauContent T = Finsupp.equivFunOnFinite.symm μ}

def orderedYoungMultiplicityType := ∀ {n r : ℕ} (lam : Partition n) (_μ : Fin r → ℕ),
  Representation ℂ (SymmetricGroup n) (SpechtModule lam) → ℕ

def semistandardContentCountType := {n r : ℕ} → Partition n → (Fin r → ℕ) → ℕ

def young_rule_coefficientType : Prop := ∀ {n r : ℕ} (lam : Partition n)
    (μ : Fin r → ℕ), (∑ i, μ i) = n →
    ∀ (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule lam)),
      InheritedSpechtAction lam ρ →
      (orderedYoungMultiplicity lam μ ρ : ℂ) =
        naturalCoefficient μ (schurPolynomial lam r)

def young_rule_tableauxType : Prop := ∀ {n r : ℕ} (lam : Partition n)
    (μ : Fin r → ℕ), (∑ i, μ i) = n →
    ∀ (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule lam)),
      InheritedSpechtAction lam ρ →
      orderedYoungMultiplicity lam μ ρ = semistandardContentCount lam μ

end Specs.AdvancedFiniteGroupRepresentations
