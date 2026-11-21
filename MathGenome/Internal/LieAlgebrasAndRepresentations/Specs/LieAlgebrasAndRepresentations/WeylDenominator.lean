import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WeylDenominatorData

/-! Determinant and Weyl denominator identities for LA-H02. -/

noncomputable section

namespace LieAlgebrasAndRepresentations.WeylDenominatorSpecs

open scoped Classical

universe u

def signCastType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {R : Set E},
    IsRootSystem R → ∀ w : rootWeylGroup R, (sign w : ℝ) = LinearMap.det w.val.toLinearMap

section Cartan

open _root_.Specs.LieAlgebrasAndRepresentations
open FormalCharacters FiniteModuleWeights VermaModules SerreRelations RootDecomposition

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

/-- The Weyl denominator identity, with its actual integral exponents and
Cartan Weyl group. The finiteness and integrality witnesses are conclusions. -/
def cartanIdentityType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
      ∃ (hS : (positive H φ).Finite) (hρ : cartanRho H φ hS ∈ integralWeights H φ)
        (hP : ∀ a ∈ positive H φ, a ∈ integralWeights H φ)
        (hW : ∀ w : weightWeylGroup H, ∀ x ∈ integralWeights H φ,
          w.val x ∈ integralWeights H φ),
        Finite (weightWeylGroup H) ∧
        (∀ w : weightWeylGroup H, (cartanSign H w : ℂ) = LinearMap.det w.val.toLinearMap) ∧
        cartanDenominator H φ hS hρ hP =
          cartanAlternant H φ hW ⟨cartanRho H φ hS, hρ⟩

/-- Empty root system specialization of the product. The identity then gives
the same unit for the alternating expression. -/
def cartanRankZeroType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (φ : Direction H) (hS : (positive H φ).Finite)
    (hρ : cartanRho H φ hS ∈ integralWeights H φ)
    (hP : ∀ a ∈ positive H φ, a ∈ integralWeights H φ),
    rootSet_value H = ∅ → cartanDenominator H φ hS hρ hP = 1

end Cartan

end LieAlgebrasAndRepresentations.WeylDenominatorSpecs
