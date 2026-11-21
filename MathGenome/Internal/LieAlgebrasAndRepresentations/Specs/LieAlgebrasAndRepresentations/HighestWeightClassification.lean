import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CompleteReducibility
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
import Mathlib.Algebra.Lie.DirectSum

/-! LA-G06, source lines 3345–3371, with the conventions at 3107–3121.
The classification is stated by existence and uniqueness of the dominant
weight of each isomorphism class and by the isomorphism criterion for the
canonical simple quotients. Module universes are independent. -/

noncomputable section

open scoped Classical DirectSum

namespace Specs.LieAlgebrasAndRepresentations.HighestWeightClassification

open SolvableRadical (IsSemisimple_value)
open VermaModules VermaWeightsUniversal SimpleHighestWeightQuotient
open SerreRelations (simple)
open IntegrableHighestWeightQuotient

universe u v

local instance {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    {H : LieSubalgebra ℂ L} {φ : Direction H} {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ

local instance {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    {H : LieSubalgebra ℂ L} {φ : Direction H} {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

/-- The simple quotient belonging to a weight is finite dimensional and
simple exactly when the weight is dominant integral. -/
def finite_simple_iff_dominant_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ →
    ((FiniteDimensional ℂ (simpleQuotient_value H φ χ) ∧
      IsSimpleOrder (LieSubmodule ℂ L (simpleQuotient_value H φ χ))) ↔ IsDominant H φ lam)

/-- Every dominant integral label has its canonical finite-dimensional
simple representative. -/
def dominant_has_simple_quotient_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H), IsDominant H φ lam →
    ∃ χ : U (borel_value H φ) →ₐ[ℂ] ℂ, IsWeightCharacter H φ lam χ ∧
      FiniteDimensional ℂ (simpleQuotient_value H φ χ) ∧
      IsSimpleOrder (LieSubmodule ℂ L (simpleQuotient_value H φ χ))

/-- Equality of the labels is precisely isomorphism of the simple quotients. -/
def simple_quotients_equiv_iff_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam mu : Module.Dual ℂ H) (χ ψ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ → IsWeightCharacter H φ mu ψ →
    (Nonempty (simpleQuotient_value H φ χ ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ ψ) ↔ lam = mu)

/-- Each nonzero finite-dimensional simple module has a unique dominant
integral label. The existence of the Verma character is included. -/
def finite_simple_classification_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
      [FiniteDimensional ℂ V] [IsSimpleOrder (LieSubmodule ℂ L V)],
    ∃! lam : {lam : Module.Dual ℂ H // IsDominant H φ lam},
      ∃ χ : U (borel_value H φ) →ₐ[ℂ] ℂ, IsWeightCharacter H φ lam.val χ ∧
        Nonempty (V ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ χ)

/-- The comparison of the two quotients commutes with the quotient maps
from the Verma module. -/
def integrable_quotient_equiv_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ →
    ∀ (hd : IsDominant H φ lam) (e f : simple H φ → L), Normalized H φ e f →
    ∃ i : quotient_value H φ χ hd f ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ χ,
      ∀ m, i (LieSubmodule.Quotient.mk' (relationSubmodule_value H φ χ hd f) m) =
        quotientMap H φ χ m

/-- The canonical highest vector generates the simple quotient and satisfies
the three families of relations. A vector satisfying those relations in
any Lie module determines exactly one map out of the simple quotient. -/
def defining_relations_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ →
    ∀ (hd : IsDominant H φ lam) (e f : simple H φ → L), Normalized H φ e f →
    let S := simpleQuotient_value H φ χ
    let x := quotientHighestVector H φ χ
    IsHighestWeight e lam x ∧
    (∀ i, (LieModule.toEnd ℂ L S (f i) ^ (simpleCoordinate H φ hd i + 1)) x = 0) ∧
    ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
      (y : V), (∀ h : H, ⁅(h : L), y⁆ = lam h • y) → (∀ i, ⁅e i, y⁆ = 0) →
      (∀ i, (LieModule.toEnd ℂ L V (f i) ^ (simpleCoordinate H φ hd i + 1)) y = 0) →
      ∃! p : S →ₗ⁅ℂ,L⁆ V, p x = y

/-- A finite internal direct sum of actual invariant submodules, each
isomorphic to a simple highest-weight module with dominant integral weight.
The empty family is allowed. -/
def finite_decomposition_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
      [FiniteDimensional ℂ V],
    ∃ S : Set (LieSubmodule ℂ L V), S.Finite ∧
      (∃ i : (⨁ W : S, ↥W.val) ≃ₗ⁅ℂ,L⁆ V,
        i.toLinearEquiv.toLinearMap = DirectSum.coeLinearMap (fun W : S => W.val.toSubmodule)) ∧
      ∀ W ∈ S, ∃ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
        IsDominant H φ lam ∧ IsWeightCharacter H φ lam χ ∧
        Nonempty (W ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ χ)

end Specs.LieAlgebrasAndRepresentations.HighestWeightClassification
