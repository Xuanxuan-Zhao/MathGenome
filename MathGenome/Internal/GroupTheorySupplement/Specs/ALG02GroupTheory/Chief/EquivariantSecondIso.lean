import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Chief.Series
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The equivariant quotient comparisons in the proof of chief-series uniqueness. -/

namespace Specs.ALG02GroupTheory.Chief.EquivariantSecondIso

open Specs.ALG02GroupTheory.Chief.Series

universe u

variable {G : Type u} [Group G]

/-- The subgroup `L/K` inside `G/K`, given by the image of `L`. -/
abbrev quotientImage (K L : Subgroup G) [K.Normal] : Subgroup (G ⧸ K) :=
  L.map (QuotientGroup.mk' K)

/-- The action of `G` on the image is conjugation by the projected element of `G/K`. -/
abbrev quotientImageAction (K L : Subgroup G) [K.Normal] [L.Normal] :
    gGroupValue G (quotientImage K L) :=
  MulDistribMulAction.compHom _
    ((MulAut.conjNormal (H := quotientImage K L)).comp (QuotientGroup.mk' K))

def FactorQuotientImageEquiv : Prop :=
  ∀ {G : Type u} [Group G] (K L : Subgroup G) [K.Normal] [L.Normal], K ≤ L →
    letI := quotientImageAction K L
    ∃ e : gEquivValue G (factorValue K L) (quotientImage K L),
      ∀ x : L, (e.1 (factorMkValue K L x) : G ⧸ K) = QuotientGroup.mk' K (x : G)

def SecondIso : Prop :=
  ∀ {G : Type u} [Group G] (X Y L N : Subgroup G)
    [X.Normal] [Y.Normal] [L.Normal] [N.Normal],
    X ⊓ Y = L → ∀ hN : X ⊔ Y = N,
    ∃ e : gEquivValue G (factorValue L Y) (factorValue X N),
      ∀ y : Y, e.1 (factorMkValue L Y y) =
        factorMkValue X N (Subgroup.inclusion (hN ▸ le_sup_right) y)

def SecondIsoImage : Prop :=
  ∀ {G : Type u} [Group G] (X Y L N : Subgroup G)
    [X.Normal] [Y.Normal] [L.Normal] [N.Normal],
    X ⊓ Y = L → X ⊔ Y = N →
    letI := quotientImageAction X N
    ∃ e : gEquivValue G (factorValue L Y) (quotientImage X N),
      ∀ y : Y, (e.1 (factorMkValue L Y y) : G ⧸ X) = QuotientGroup.mk' X (y : G)

def AmbientDiamond : Prop :=
  ∀ {G : Type u} [Group G] (X Y N : Subgroup G) [X.Normal] [Y.Normal],
    ambientCovByValue X N → ambientCovByValue Y N → X ≠ Y →
    X ⊔ Y = N ∧ ambientCovByValue (X ⊓ Y) X ∧ ambientCovByValue (X ⊓ Y) Y

def DiamondFactorEquivs : Prop :=
  ∀ {G : Type u} [Group G] (X Y N : Subgroup G) [X.Normal] [Y.Normal] [N.Normal],
    ∀ (hX : ambientCovByValue X N) (hY : ambientCovByValue Y N), X ≠ Y →
      (∃ e : gEquivValue G (factorValue (X ⊓ Y) Y) (factorValue X N),
        ∀ y : Y, e.1 (factorMkValue (X ⊓ Y) Y y) =
          factorMkValue X N (Subgroup.inclusion hY.1.le y)) ∧
      (∃ e : gEquivValue G (factorValue (X ⊓ Y) X) (factorValue Y N),
        ∀ x : X, e.1 (factorMkValue (X ⊓ Y) X x) =
          factorMkValue Y N (Subgroup.inclusion hX.1.le x))

end Specs.ALG02GroupTheory.Chief.EquivariantSecondIso
