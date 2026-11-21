import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WeylDenominatorData
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient

/-! The partition function and the multiplicity formula of LA-H06.
The weight argument ranges over the full complex Cartan dual. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.KostantMultiplicity

open SolvableRadical (IsSemisimple_value)
open VermaModules VermaWeightsUniversal SerreRelations SimpleHighestWeightQuotient
open IntegrableHighestWeightQuotient (IsDominant)
open FormalCharacters
open FiniteModuleWeights (weightWeylGroup)
open _root_.LieAlgebrasAndRepresentations.WeylDenominatorSpecs (cartanRho cartanSign)

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)

/-- An unordered decomposition is specified by the number of copies of each
positive root. The sum is over the finite positive root system in the theorem. -/
def Decomposition (β : Module.Dual ℂ H) :=
  {n : positive H φ → ℕ // (∑ᶠ a, n a • a.val) = β}

/-- The number of unordered decompositions into positive roots. -/
def partition (β : Module.Dual ℂ H) : ℕ :=
  Nat.card (Decomposition H φ β)

def partitionType :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H),
    Module.Dual ℂ H → ℕ

def partitionPropertiesType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
      (positive H φ).Finite ∧ (∀ β, Finite (Decomposition H φ β)) ∧
      partition H φ 0 = 1 ∧ ∀ β ∉ cone H φ, partition H φ β = 0

variable [FiniteDimensional ℂ L]

/-- The signed partition count gives each multiplicity in the canonical simple quotient. -/
def MultiplicityFormula (lam : Module.Dual ℂ H)
    (χ : U (borel_value H φ) →ₐ[ℂ] ℂ) : Prop :=
  ∃ (_fd : FiniteDimensional ℂ (simpleQuotient_value H φ χ))
    (hS : (positive H φ).Finite),
    Finite (weightWeylGroup H) ∧
    letI := inducedLieRingModule H φ χ
    letI := inducedLieModule H φ χ
    ∀ μ : Module.Dual ℂ H,
      (multiplicity H (simpleQuotient_value H φ χ) μ =
        ∑ᶠ w : weightWeylGroup H, cartanSign H w *
          (partition H φ
            (w.val (lam + cartanRho H φ hS) - (μ + cartanRho H φ hS)) : ℤ)) ∧
      (lam - μ ∉ cone H φ → multiplicity H (simpleQuotient_value H φ χ) μ = 0)

def formulaType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
      IsDominant H φ lam → IsWeightCharacter H φ lam χ → MultiplicityFormula H φ lam χ

def formulaForDominantType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H), IsDominant H φ lam →
      ∃ χ, IsWeightCharacter H φ lam χ ∧ MultiplicityFormula H φ lam χ

end Specs.LieAlgebrasAndRepresentations.KostantMultiplicity
