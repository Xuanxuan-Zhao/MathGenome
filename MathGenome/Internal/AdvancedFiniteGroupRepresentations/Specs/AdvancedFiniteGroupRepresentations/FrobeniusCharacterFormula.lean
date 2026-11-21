import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtClassification
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.AlternatingCauchyKernel
import Mathlib.RepresentationTheory.Character

/-! FR-C03 (source lines 925–971). The representation in the theorem acts on
exactly the polytabloid span, and is required to restrict the tabloid action.
Thus the left side is its trace character, not a polynomial definition of it.
The extra representation parameter avoids assuming stability as a certificate
inside an independent definition: every inherited action has the stated trace. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The literal coefficient in the descending Vandermonde convention. -/
def frobeniusCoefficient {n : ℕ} (r : ℕ) (lam nu : Partition n) : ℂ :=
  naturalCoefficient (shiftedPartition r lam) (vandermonde r * partitionPowerSum r nu)

def frobeniusCoefficientType := {n : ℕ} → ℕ → Partition n → Partition n → ℂ

def frobenius_character_formulaType : Prop :=
  ∀ {n : ℕ} (lam nu : Partition n) (r : ℕ),
    1 ≤ r → length lam ≤ r →
    ∀ (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule lam)),
    InheritedSpechtAction lam ρ →
    ∀ (g : SymmetricGroup n), cyclePartition g = nu →
      ρ.character g = frobeniusCoefficient r lam nu

/-- Removing or appending any number of padded zero rows has no effect. -/
def frobeniusCoefficient_paddingType : Prop :=
  ∀ {n : ℕ} (lam nu : Partition n) (r s : ℕ),
    length lam ≤ r → r ≤ s →
      frobeniusCoefficient s lam nu = frobeniusCoefficient r lam nu

/-- The zero-variable boundary case also gives the actual empty Specht trace. -/
def frobenius_character_emptyType : Prop :=
  ∀ (ρ : Representation ℂ (SymmetricGroup 0) (SpechtModule emptyPartition)),
    InheritedSpechtAction emptyPartition ρ →
    ∀ g : SymmetricGroup 0,
      ρ.character g = frobeniusCoefficient 0 emptyPartition emptyPartition ∧
      frobeniusCoefficient 0 emptyPartition emptyPartition = 1

/-- Polynomial orthogonality, extracted from the accepted Cauchy identities.
This is an auxiliary result, not an assumed character identification. -/
def frobeniusCoefficient_orthogonalType : Prop :=
  ∀ {n : ℕ} (r : ℕ), 1 ≤ r → ∀ lam mu : Partition n,
    length lam ≤ r → length mu ≤ r →
    (∑ nu : Partition n, (zFactor nu : ℂ)⁻¹ *
      frobeniusCoefficient r lam nu * frobeniusCoefficient r mu nu) =
        if lam = mu then 1 else 0

end Specs.AdvancedFiniteGroupRepresentations
