import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.ReducedEnveloping
import Mathlib.LinearAlgebra.Basis.Defs

/-! Specifications for the centrality, semilinearity, and generators of the p-center. -/

namespace Specs.LieNotes.SuperRestricted.RestrictedCenter

open _root_.Shared.Lie (U)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.ReducedEnveloping (pCenterElementValue pCenterValue)

universe u v w

/-- Every p-center generator commutes with every element of the ordinary enveloping algebra. -/
def pCenterElement_commuteType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G]
    (power : restrictedPowerValue k p G) (x : G) (a : U k G),
    Commute (pCenterElementValue power x) a

/-- The full p-center subalgebra lies in the center of the ordinary enveloping algebra. -/
def pCenter_le_centerType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G]
    (power : restrictedPowerValue k p G),
    pCenterValue power ≤ Subalgebra.center k (U k G)

/-- The map from the Lie algebra to the p-center is additive. -/
def pCenterElement_addType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G]
    (power : restrictedPowerValue k p G) (x y : G),
    pCenterElementValue power (x + y) = pCenterElementValue power x + pCenterElementValue power y

/-- Scalar multiplication is transported by the p-th power on the ground field. -/
def pCenterElement_smulType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G]
    (power : restrictedPowerValue k p G) (a : k) (x : G),
    pCenterElementValue power (a • x) = a ^ p • pCenterElementValue power x

/-- The images of any basis under the p-center map generate the p-center over the field. -/
def pCenter_eq_adjoin_basisType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G]
    (power : restrictedPowerValue k p G) {ι : Type w} (b : Module.Basis ι k G),
    pCenterValue power = Algebra.adjoin k (Set.range fun i => pCenterElementValue power (b i))

end Specs.LieNotes.SuperRestricted.RestrictedCenter
