import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedCenter
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedPolynomialBasis
import Mathlib.LinearAlgebra.Dimension.Finite

/-! The reduced PBW theorem for the canonical quotient of the ordinary enveloping algebra. -/

namespace Specs.LieNotes.SuperRestricted.ReducedPbw

open _root_.Shared.Lie (U)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.ReducedEnveloping
open _root_.Specs.LieNotes.SuperRestricted.RestrictedCenter
open _root_.Specs.LieNotes.SuperRestricted.RestrictedPolynomialBasis
open _root_.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary
  (restrictedEnvelopingValue)

universe u v w

/-- The basis relations generate the same two-sided ideal as the relations for all Lie elements. -/
def reducedRelations_eq_span_basisType : Prop :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {n p : ℕ} [CharP k p] [NeZero p] (power : restrictedPowerValue k p G)
    (b : Module.Basis (Fin n) k G) (χ : G →ₗ[k] k),
    reducedRelationsValue power χ =
      (TwoSidedIdeal.span (Set.range fun i =>
        pCenterElementValue power (b i) - algebraMap k (U k G) (χ (b i) ^ p))).asIdeal

/-- The quotient images of the bounded ordered words form a basis for every character. -/
def reducedBasisType : Prop :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {n p : ℕ} [CharP k p] [NeZero p] (power : restrictedPowerValue k p G)
    (b : Module.Basis (Fin n) k G) (χ : G →ₗ[k] k),
    ∃ B : Module.Basis (Fin n → Fin p) k (reducedEnvelopingValue power χ),
      ∀ r, B r = quotientMapValue power χ (restrictedMonomialValue b r)

/-- The dimension of the actual reduced enveloping algebra, including dimension zero for the
input Lie algebra. -/
def reducedFinrankType : Prop :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {p : ℕ} [CharP k p] [NeZero p] [Module.Finite k G] (power : restrictedPowerValue k p G)
    (χ : G →ₗ[k] k),
    Module.Finite k (reducedEnvelopingValue power χ) ∧
      Module.finrank k (reducedEnvelopingValue power χ) = p ^ Module.finrank k G

/-- The polynomial p-center and reduced PBW theorem, with the zero-character identification
induced by the identity on the ordinary enveloping algebra. -/
def polynomialCenterAndReducedPbwType : Prop :=
  pCenterElement_commuteType.{u,v} ∧ pCenter_le_centerType.{u,v} ∧
  pCenterElement_addType.{u,v} ∧ pCenterElement_smulType.{u,v} ∧
  pCenter_eq_adjoin_basisType.{u,v,w} ∧
  polynomialBasisType.{u,v} ∧ centerBasisType.{u,v} ∧
  reducedRelations_eq_span_basisType.{u,v} ∧ reducedBasisType.{u,v} ∧
  reducedFinrankType.{u,v} ∧
  (∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {p : ℕ} [CharP k p] [NeZero p] (power : restrictedPowerValue k p G),
    ∃ e : reducedEnvelopingValue power 0 ≃ₐ[k] restrictedEnvelopingValue k p power,
      ∀ a : U k G, e (quotientMapValue power 0 a) =
        _root_.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary.quotientMapValue
          k p power a)

end Specs.LieNotes.SuperRestricted.ReducedPbw
