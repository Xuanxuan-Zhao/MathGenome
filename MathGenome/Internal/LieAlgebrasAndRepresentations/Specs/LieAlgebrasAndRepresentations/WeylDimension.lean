import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WeylDenominatorData
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestWeightCasimir
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient

/-! LA-H04, with the weight-form and coroot conventions of the source. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.WeylDimension

open SolvableRadical (IsSemisimple_value)
open SerreRelations VermaModules SimpleHighestWeightQuotient
open HighestWeightCasimir (weightForm_value)
open IntegrableHighestWeightQuotient (IsDominant)
open RootForm (rootForm_value coroot_value)
open _root_.LieAlgebrasAndRepresentations.WeylDenominatorSpecs (cartanRho)
open scoped BigOperators

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

/-- The coroot normalization for a choice of weight form, allowing independent
normalizations on the simple factors. -/
def CorootCompatible (H : LieSubalgebra ℂ L) (φ : Direction H)
    (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H)) : Prop :=
  ∀ α ∈ positive H φ, B α α ≠ 0 ∧
    ∀ μ, μ (coroot_value H α) = 2 * B μ α / B α α

/-- The dimension of the canonical simple quotient, in both source forms.
The product runs over the entire positive system, also for reducible systems. -/
def DimensionFormula (H : LieSubalgebra ℂ L) (φ : Direction H) (lam : Module.Dual ℂ H)
    (χ : U (borel_value H φ) →ₐ[ℂ] ℂ) : Prop :=
  ∃ (fd : FiniteDimensional ℂ (simpleQuotient_value H φ χ))
    (hS : (positive H φ).Finite),
    letI := fd
    let ρ := cartanRho H φ hS
    let n := Module.finrank ℂ (simpleQuotient_value H φ χ)
    (∀ α ∈ positive H φ,
      rootForm_value H ρ α ≠ 0 ∧ ρ (coroot_value H α) ≠ 0) ∧
    (n : ℂ) = ∏ α ∈ hS.toFinset, rootForm_value H (lam + ρ) α / rootForm_value H ρ α ∧
    (n : ℂ) = ∏ α ∈ hS.toFinset, (lam + ρ) (coroot_value H α) / ρ (coroot_value H α) ∧
    (∀ B : LinearMap.BilinForm ℂ (Module.Dual ℂ H), CorootCompatible H φ B →
      (∀ α ∈ positive H φ, B ρ α ≠ 0) ∧
      (n : ℂ) = ∏ α ∈ hS.toFinset, B (lam + ρ) α / B ρ α) ∧
    (∀ B : LinearMap.BilinForm ℂ L, B.lieInvariant L → B.Nondegenerate →
      let C := weightForm_value H B
      (∀ α ∈ positive H φ, C ρ α ≠ 0) ∧
      (n : ℂ) = ∏ α ∈ hS.toFinset, C (lam + ρ) α / C ρ α) ∧
    (lam = 0 → n = 1) ∧
    (positive H φ = ∅ → n = 1) ∧
    (Subsingleton L → n = 1)

def formulaType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
      IsDominant H φ lam → IsWeightCharacter H φ lam χ → DimensionFormula H φ lam χ

def formulaForDominantType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H), IsDominant H φ lam →
      ∃ χ, IsWeightCharacter H φ lam χ ∧ DimensionFormula H φ lam χ

end Specs.LieAlgebrasAndRepresentations.WeylDimension
