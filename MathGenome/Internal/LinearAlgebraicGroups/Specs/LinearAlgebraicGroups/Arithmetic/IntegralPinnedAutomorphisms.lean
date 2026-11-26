import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.IntegralPinnedAutomorphisms

open IntegralSemisimpleModel
open Pinning (BasedRootDatum PinnedIso RootCoordinate transportCharacter)
open RationalRealization (Realization)
open RootGroups (rootPoint)
open CharacterPairing (characterValue)

noncomputable section

attribute [local instance 100] integerAlgebra

variable {D : BasedRootDatum.{u}}

/-- The integral torus action precomposes evaluations by inverse transport of characters. -/
def torusValuesMap (τ : D ⟶ D) (R : IntegralAlgebra.{u}) (v : TorusValues D R) :
    TorusValues D R :=
  v.comp τ.val.weightEquiv.symm.toAddEquiv.toMultiplicative.toMonoidHom

/-- The specified action on the marked torus and the pinned simple coordinates. -/
def ActsOnPinning (M : IntegralMarking D) (τ : D ⟶ D)
    (f : M.group ⟶ M.group) : Prop :=
  (∀ (R : IntegralAlgebra.{u}) (v : TorusValues D R),
    (torusPoint D R v ≫ M.torus.hom.hom) ≫ f.hom.hom =
      torusPoint D R (torusValuesMap τ R v) ≫ M.torus.hom.hom) ∧
  (∀ (a : D.base.support) (R : IntegralAlgebra.{u}) (r : R),
    (M.line.point R r ≫ (M.root a.val).hom.hom) ≫ f.hom.hom =
      M.line.point R r ≫ (M.root (τ.val.indexEquiv a.val)).hom.hom)

/-- Every marked absolute root parameter is transported by an integral unit. -/
def ActsOnRoots (M : IntegralMarking D) (τ : D ⟶ D)
    (f : M.group ⟶ M.group) : Prop :=
  ∃ c : D.I → Integers.{u}ˣ, ∀ (a : D.I) (R : IntegralAlgebra.{u}) (r : R),
    (M.line.point R r ≫ (M.root a).hom.hom) ≫ f.hom.hom =
      M.line.point R (algebraMap Integers.{u} R (c a : Integers.{u}) * r) ≫
        (M.root (τ.val.indexEquiv a)).hom.hom

/-- A chosen comparison of the integral fibre with its pinned realization, with
the torus and root compatibilities of `Model.fieldFibre`. -/
structure FibreMarking (M : IntegralMarking D) (k : Type u) [Field k] where
  line : RootGroups.AdditiveLine k
  realization : Realization D line
  groupIso : (fibre k).obj M.group ≅ realization.pinned.pair.G.val
  torusIso : (fibre k).obj (splitTorus D) ≅ realization.pinned.pair.T.group
  root : ∀ a : D.I, RootCoordinate line realization.pinned.pair.T
    (realization.pinned.roots (realization.datumIso.val.indexEquiv a)).val
    (realization.datumIso.val.indexEquiv a).val
  torus_comm : (fibre k).map M.torus ≫ groupIso.hom =
    torusIso.hom ≫ realization.pinned.pair.T.inclusion
  simple_root : ∀ a : D.base.support, root a.val = realization.pinned.pin (realization.simpleRoot a)
  torus_points : ∀ (R : TestAlgebra k)
      (s : AdjointRepresentation.GroupPoints ((fibre k).obj (splitTorus D)) R)
      (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
    forgetFibrePoint (splitTorus D) R s = torusPoint D (CommAlgCat.of Integers.{u} R) v →
    ∀ x : D.X, characterValue (Additive.toMul (realization.datumIso.val.weightEquiv x)) R
      (s ≫ torusIso.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R)
  root_points : ∀ (a : D.I) (R : TestAlgebra k) (r : R),
    forgetFibrePoint M.group R
      (rootPoint ((root a).val.hom ≫
        (realization.pinned.roots (realization.datumIso.val.indexEquiv a)).val.inclusion ≫
          groupIso.inv) R r) =
      M.line.point (CommAlgCat.of Integers.{u} R) r ≫ (M.root a).hom.hom

/-- The actual pinned field lift uses the chosen identification of the
character lattice with the characters of the realized torus. -/
def Induces {M : IntegralMarking D} {k : Type u} [Field k]
    (C : FibreMarking M k) (τ : D ⟶ D)
    (g : PinnedIso C.realization.pinned C.realization.pinned) : Prop :=
  ∀ x : D.X,
    transportCharacter g.torus (Additive.toMul (C.realization.datumIso.val.weightEquiv x)) =
      Additive.toMul (C.realization.datumIso.val.weightEquiv (τ.val.weightEquiv x))

/-- Specialization agrees as a group-scheme map, over a field of any characteristic. -/
def FibreCompatibility (M : IntegralMarking D) (τ : D ⟶ D)
    (f : M.group ⟶ M.group) : Prop :=
  ∀ (k : Type u) [Field k] (C : FibreMarking M k),
    ∃ g : PinnedIso C.realization.pinned C.realization.pinned,
      Induces C τ g ∧ (fibre k).map f ≫ C.groupIso.hom = C.groupIso.hom ≫ g.group.hom

/-- The pinned automorphisms of the given integral model, with their marked
actions, uniqueness, composition, and field comparison. -/
def Statement : Prop :=
  ∀ (D : BasedRootDatum.{u}) (M : Model D),
    ∃ lift : (D ⟶ D) → (M.group ≅ M.group),
      (∀ τ, ActsOnPinning M.toIntegralMarking τ (lift τ).hom ∧
        ActsOnRoots M.toIntegralMarking τ (lift τ).hom ∧
        FibreCompatibility M.toIntegralMarking τ (lift τ).hom) ∧
      (∀ (τ : D ⟶ D) (f : M.group ≅ M.group),
        ActsOnPinning M.toIntegralMarking τ f.hom → f = lift τ) ∧
      lift (𝟙 D) = Iso.refl M.group ∧
      ∀ τ σ, lift (τ ≫ σ) = lift τ ≪≫ lift σ

end

end LinearAlgebraicGroups.Specs.IntegralPinnedAutomorphisms
