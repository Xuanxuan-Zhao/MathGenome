import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WeylDenominator
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalCharacters

/-! The Weyl character formula of LA-H03 in the integral group ring.
The source allows the quotient to be expressed after multiplication by its
denominator. We state both the product and alternating-sum versions. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.WeylCharacter

open SolvableRadical (IsSemisimple_value)
open VermaModules VermaWeightsUniversal SerreRelations SimpleHighestWeightQuotient
open IntegrableHighestWeightQuotient (IsDominant)
open FormalCharacters
open _root_.LieAlgebrasAndRepresentations.WeylDenominatorSpecs
open FiniteModuleWeights (weightWeylGroup)

universe u

/-- Both denominator-cleared equalities for the canonical simple quotient. -/
def ClearedFormula {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H) (lam : Module.Dual ℂ H)
    (χ : U (borel_value H φ) →ₐ[ℂ] ℂ) : Prop :=
  ∃ (fd : FiniteDimensional ℂ (simpleQuotient_value H φ χ))
    (hS : (positive H φ).Finite) (hρ : cartanRho H φ hS ∈ integralWeights H φ)
    (hP : ∀ a ∈ positive H φ, a ∈ integralWeights H φ)
    (hW : ∀ w : weightWeylGroup H, ∀ a ∈ integralWeights H φ,
      w.val a ∈ integralWeights H φ)
    (htop : lam + cartanRho H φ hS ∈ integralWeights H φ),
    letI := inducedLieRingModule H φ χ
    letI := inducedLieModule H φ χ
    letI := fd
    let F := character H φ (simpleQuotient_value H φ χ)
    let A := cartanAlternant H φ hW ⟨lam + cartanRho H φ hS, htop⟩
    cartanDenominator H φ hS hρ hP * F = A ∧
      cartanAlternant H φ hW ⟨cartanRho H φ hS, hρ⟩ * F = A

/-- The formula for any realization of the prescribed Borel character. -/
def formulaType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
      IsDominant H φ lam → IsWeightCharacter H φ lam χ → ClearedFormula H φ lam χ

/-- Every dominant integral weight has the character asserted by the formula. -/
def formulaForDominantType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H), IsDominant H φ lam →
      ∃ χ, IsWeightCharacter H φ lam χ ∧ ClearedFormula H φ lam χ

end Specs.LieAlgebrasAndRepresentations.WeylCharacter
