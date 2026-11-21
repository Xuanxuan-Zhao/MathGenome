import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.KostantMultiplicity
import Mathlib.Algebra.Lie.DirectSum
import Mathlib.Algebra.Lie.TensorProduct

/-! LA-H09, source lines 3992–3998. The count is over the summands of an
actual finite internal Lie module decomposition of the tensor product. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.SteinbergTensorMultiplicity

open SolvableRadical (IsSemisimple_value)
open VermaModules VermaWeightsUniversal SimpleHighestWeightQuotient
open IntegrableHighestWeightQuotient (IsDominant)
open FiniteModuleWeights (weightWeylGroup)
open SerreRelations (positive)
open _root_.LieAlgebrasAndRepresentations.WeylDenominatorSpecs (cartanRho cartanSign)
open scoped Classical DirectSum TensorProduct

universe u v

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

variable [FiniteDimensional ℂ L]

/-- A finite internal direct sum labelled by the dominant weights of its simple summands. -/
def IsDecomposition {V : Type v} [AddCommGroup V] [Module ℂ V]
    [LieRingModule L V] [LieModule ℂ L V] (S : Set (LieSubmodule ℂ L V))
    (label : S → {a : Module.Dual ℂ H // IsDominant H φ a}) : Prop :=
  S.Finite ∧
    (∃ e : (⨁ i : S, ↥i.val) ≃ₗ⁅ℂ,L⁆ V,
      e.toLinearEquiv.toLinearMap = DirectSum.coeLinearMap (fun i : S => i.val.toSubmodule)) ∧
    ∀ i : S, ∃ χ : U (borel_value H φ) →ₐ[ℂ] ℂ,
      IsWeightCharacter H φ (label i).val χ ∧
        Nonempty (↥i.val ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ χ)

/-- The signed double sum of Kostant partition numbers. -/
def signedPartitionSum (hS : (positive H φ).Finite)
    (lam mu nu : Module.Dual ℂ H) : ℤ :=
  let ρ := cartanRho H φ hS
  ∑ᶠ u : weightWeylGroup H, ∑ᶠ w : weightWeylGroup H,
    cartanSign H u * cartanSign H w *
      (KostantMultiplicity.partition H φ
        (u.val (lam + ρ) + w.val (mu + ρ) - (nu + 2 • ρ)) : ℤ)

/-- The formula for every realization of the two simple factors. Such a
decomposition exists, and the number of summands isomorphic to the simple
module of each dominant weight is independent of the decomposition. -/
def TensorFormula (lam mu : Module.Dual ℂ H)
    (χ ψ : U (borel_value H φ) →ₐ[ℂ] ℂ) : Prop :=
  let V := simpleQuotient_value H φ χ ⊗[ℂ] simpleQuotient_value H φ ψ
  ∃ hS : (positive H φ).Finite,
    Finite (weightWeylGroup H) ∧
    (∃ (S : Set (LieSubmodule ℂ L V)) (label : S → {a // IsDominant H φ a}),
      IsDecomposition H φ S label) ∧
    ∀ (S : Set (LieSubmodule ℂ L V)) (label : S → {a // IsDominant H φ a}),
      IsDecomposition H φ S label →
      ∀ (nu : {a : Module.Dual ℂ H // IsDominant H φ a})
        (η : U (borel_value H φ) →ₐ[ℂ] ℂ), IsWeightCharacter H φ nu.val η →
        (Nat.card {i : S // Nonempty (↥i.val ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ η)} : ℤ) =
          signedPartitionSum H φ hS lam mu nu.val

def formula_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ (lam mu : Module.Dual ℂ H) (χ ψ : U (borel_value H φ) →ₐ[ℂ] ℂ),
      IsDominant H φ lam → IsDominant H φ mu →
      IsWeightCharacter H φ lam χ → IsWeightCharacter H φ mu ψ → TensorFormula H φ lam mu χ ψ

def formula_for_dominant_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ lam mu : Module.Dual ℂ H, IsDominant H φ lam → IsDominant H φ mu →
      ∃ χ ψ, IsWeightCharacter H φ lam χ ∧ IsWeightCharacter H φ mu ψ ∧
        TensorFormula H φ lam mu χ ψ

end Specs.LieAlgebrasAndRepresentations.SteinbergTensorMultiplicity
