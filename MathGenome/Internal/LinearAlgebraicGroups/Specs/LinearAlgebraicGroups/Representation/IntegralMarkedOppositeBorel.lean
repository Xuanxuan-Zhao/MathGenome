import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagLineBundle
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ArithmeticCohomologyBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ArithmeticProjectiveFiniteness

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000

namespace LinearAlgebraicGroups.Specs.IntegralMarkedOppositeBorel

noncomputable section

open Pinning (BasedRootDatum RootCoordinate)
open RationalRealization (Realization)
open IntegralSemisimpleModel (Integers splitTorus fibre forgetFibrePoint torusPoint)
open FlagLineBundle (OppositeBorelPair BorelProjection)
open ArithmeticCohomologyBaseChange (changeBase fibreProjection)
open OrderedCechComparison (SchemeOverRing)

abbrev BaseRing (m : ℕ) : Type u := ArithmeticProjectiveFiniteness.BaseRing.{u} m

abbrev integerMap (m : ℕ) : Integers.{u} →+* BaseRing.{u} m := algebraMap _ _

variable {D : BasedRootDatum.{u}} (I : IntegralSemisimpleModel.Model D)

/-- The scalar extension of the supplied marked group over the integers. -/
abbrev relativeGroup (m : ℕ) := (changeBase (integerMap.{u} m)).mapGrp.obj I.group

/-- A smooth affine closed subgroup and a multiplicative unit on its global sections. -/
structure RelativeBorel (m : ℕ) where
  borel : Grp (SchemeOverRing (BaseRing.{u} m))
  inclusion : borel ⟶ relativeGroup I m
  closed : IsClosedImmersion inclusion.hom.hom.left
  smooth : Smooth borel.X.hom
  affine : IsAffine borel.X.left
  character : Γ(borel.X.left, ⊤)ˣ
  characterMultiplicative :
    μ[borel.X].left.appTop (character : Γ(borel.X.left, ⊤)) =
      (fst borel.X borel.X).left.appTop (character : Γ(borel.X.left, ⊤)) *
        (snd borel.X borel.X).left.appTop (character : Γ(borel.X.left, ⊤))

/-- The comparison uses the integral fibre isomorphism with its torus,
character-lattice and simple-root markings. -/
structure FieldComparison {m : ℕ} {k : Type u} [Field k] (φ : BaseRing.{u} m →+* k)
    (w : D.X) (H : RelativeBorel I m) where
  additive : RootGroups.AdditiveLine k
  realization : Realization D additive
  pair : OppositeBorelPair realization.pinned.pair.G
  torus_eq : pair.torus = realization.pinned.pair.T
  positive_eq : pair.positive = realization.pinned.pair.B
  projection : BorelProjection pair
  integralIso : (fibre k).obj I.group ≅ realization.pinned.pair.G.val
  torusIso : (fibre k).obj (splitTorus D) ≅ realization.pinned.pair.T.group
  torus_marking : ((fibre k).map I.torus) ≫ integralIso.hom =
    torusIso.hom ≫ realization.pinned.pair.T.inclusion
  rootCoordinate : ∀ a : D.I, RootCoordinate additive realization.pinned.pair.T
    (realization.pinned.roots (realization.datumIso.val.indexEquiv a)).val
    (realization.datumIso.val.indexEquiv a).val
  simple_marking : ∀ a : D.base.support,
    rootCoordinate a.val = realization.pinned.pin (realization.simpleRoot a)
  root_marking : ∀ (a : D.I) (R : TestAlgebra k) (r : R),
    letI : Algebra Integers.{u} R := IntegralSemisimpleModel.integerAlgebra R
    forgetFibrePoint I.group R
      (RootGroups.rootPoint ((rootCoordinate a).val.hom ≫
        (realization.pinned.roots (realization.datumIso.val.indexEquiv a)).val.inclusion ≫
          integralIso.inv) R r) =
      I.line.point (CommAlgCat.of Integers.{u} R) r ≫ (I.root a).hom.hom
  weight_marking : ∀ (R : TestAlgebra k)
      (s : AdjointRepresentation.GroupPoints ((fibre k).obj (splitTorus D)) R),
    letI : Algebra Integers.{u} R := IntegralSemisimpleModel.integerAlgebra R
    ∀ v : IntegralSemisimpleModel.TorusValues D (CommAlgCat.of Integers.{u} R),
      forgetFibrePoint (splitTorus D) R s = torusPoint D (CommAlgCat.of Integers.{u} R) v →
      ∀ x : D.X, CharacterPairing.characterValue
        (Additive.toMul (realization.datumIso.val.weightEquiv x)) R
        (s ≫ torusIso.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R)
  groupIso : (changeBase φ).mapGrp.obj (relativeGroup I m) ≅ realization.pinned.pair.G.val
  group_composition :
    groupIso.inv.hom.hom.left ≫ fibreProjection φ (relativeGroup I m).X ≫
      fibreProjection (integerMap m) I.group.X =
      integralIso.inv.hom.hom.left ≫
        (letI : Algebra Integers.{u} k := IntegralSemisimpleModel.integerAlgebra k
         fibreProjection (algebraMap Integers.{u} k) I.group.X)
  borelIso : (changeBase φ).mapGrp.obj H.borel ≅ pair.negative.group
  inclusion_eq : ((changeBase φ).mapGrp.map H.inclusion) ≫ groupIso.hom =
    borelIso.hom ≫ pair.negative.inclusion
  character_eq :
    let χ : CharacterDescent.Character pair.torus.group :=
      torus_eq.symm ▸ Additive.toMul (realization.datumIso.val.weightEquiv w)
    let b : pair.negative.group.X.left ⟶ H.borel.X.left :=
      borelIso.inv.hom.hom.left ≫ fibreProjection φ H.borel.X
    let r := (𝟙 pair.negative.group.X)⁻¹ ≫ (projection.projection ≫ χ).hom.hom
    let L := DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters
    b.appTop (H.character⁻¹ : Γ(H.borel.X.left, ⊤)ˣ) =
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ r.left.appTop)
        (MonoidAlgebra.single DiagonalizableGroups.integerGenerator (1 : k))

/-- One arithmetic localization carries the subgroup and its prescribed
character, with the claimed comparison for every field over that base. -/
def Statement : Prop :=
  ∀ (D : BasedRootDatum.{u}), RootData.rationalRootAnnihilator D.datum = ⊥ →
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    ∀ (I : IntegralSemisimpleModel.Model D) (w : D.X),
      ∃ m : ℕ, m ≠ 0 ∧ ∃ H : RelativeBorel I m,
        ∀ (k : Type u) [Field k] (φ : BaseRing.{u} m →+* k),
          Nonempty (FieldComparison I φ w H)

end

end LinearAlgebraicGroups.Specs.IntegralMarkedOppositeBorel
