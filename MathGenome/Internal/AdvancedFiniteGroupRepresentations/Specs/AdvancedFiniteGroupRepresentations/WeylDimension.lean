import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SchurWeylCharacter
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SchurAlternant

/-! FR-D08, source lines 1585–1632. Indices `i,j : Fin d` are the printed
indices minus one. Row lengths include all padded zero rows. Differences
are taken in ℂ, so no truncated natural subtraction enters the formula.
The product is empty (hence one) for d = 0 or d = 1. -/
noncomputable section
open scoped BigOperators
universe u
namespace Specs.AdvancedFiniteGroupRepresentations

def weylDimensionProduct {n : ℕ} (p : Partition n) (d : ℕ) : ℂ :=
  ∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
    ((rowLength p i.val : ℂ) - (rowLength p j.val : ℂ) +
      (j.val : ℂ) - (i.val : ℂ)) / ((j.val : ℂ) - (i.val : ℂ))

def weylDimensionProductType := {n : ℕ} → Partition n → ℕ → ℂ

def schur_at_one_weyl_productType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (d : ℕ), length p ≤ d →
    MvPolynomial.eval (fun _ : Fin d => (1 : ℂ)) (schurPolynomial p d) =
      weylDimensionProduct p d

def schurWeyl_dimension_productType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ} (p : Partition n), length p ≤ Module.finrank ℂ V →
    (Module.finrank ℂ (TensorMultiplicity V p) : ℂ) =
      weylDimensionProduct p (Module.finrank ℂ V)

def schurWeyl_dimension_length_cutoffType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ} (p : Partition n), Module.finrank ℂ V < length p →
    Module.finrank ℂ (TensorMultiplicity V p) = 0

/-- Retain the diagonal character as the other assertion of FR-D08. -/
def weyl_diagonal_characterType : Prop := schurWeyl_diagonal_characterType.{u}

def schurWeyl_empty_dimensionType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    Module.finrank ℂ (TensorMultiplicity V emptyPartition) = 1

def weylDimensionProduct_emptyType : Prop :=
  ∀ d : ℕ, weylDimensionProduct emptyPartition d = 1

def weylDimensionProduct_smallType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (d : ℕ), d ≤ 1 → weylDimensionProduct p d = 1

end Specs.AdvancedFiniteGroupRepresentations
