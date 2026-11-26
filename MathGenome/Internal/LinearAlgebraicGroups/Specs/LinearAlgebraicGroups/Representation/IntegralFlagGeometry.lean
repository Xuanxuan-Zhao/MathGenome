import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.RelativeCovarianceLine
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.RationalRealization
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ArithmeticCohomologyBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ArithmeticProjectiveFiniteness

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.IntegralFlagGeometry

noncomputable section

open RationalRealization (RationalField Realization)
open Pinning (BasedRootDatum)
open FlagCohomology
open FlagLineBundle (OppositeBorelPair BorelProjection)
open QuotientEmbedding (Presentation)

/-- The arithmetic base on which the single integer `m` is inverted. -/
abbrev BaseRing (m : ℕ) : Type u := ArithmeticProjectiveFiniteness.BaseRing.{u} m

/-- The field at the non-inverted prime `p`, in the universe of the flag. -/
abbrev PrimeField (p : ℕ) : Type u := ULift.{u} (ZMod p)

abbrev rationalMap {m : ℕ} (hm : m ≠ 0) : BaseRing.{u} m →+* RationalField.{u} :=
  ArithmeticCohomologyBaseChange.rationalMap (m := (m : ℤ)) (by exact_mod_cast hm)

abbrev primeMap {m p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ m) :
    BaseRing.{u} m →+* PrimeField.{u} p :=
  ArithmeticCohomologyBaseChange.primeMap (m := (m : ℤ)) (by exact_mod_cast hp)

section BaseChange

variable {A B : Type u} [CommRing A] [CommRing B]

abbrev changeBase (φ : A →+* B) :=
  ArithmeticCohomologyBaseChange.changeBase φ

abbrev fibreProjection (φ : A →+* B) (Y : SchemeOverRing A) :=
  ArithmeticCohomologyBaseChange.fibreProjection φ Y

abbrev fibreProjection_over (φ : A →+* B) (Y : SchemeOverRing A) :=
  ArithmeticCohomologyBaseChange.fibreProjection_over φ Y

abbrev fibreSheaf (φ : A →+* B) (Y : SchemeOverRing A) (L : Y.left.Modules) :=
  ArithmeticCohomologyBaseChange.fibreSheaf φ Y L

end BaseChange

abbrev homogeneousGrading := ArithmeticProjectiveFiniteness.homogeneousGrading
abbrev homogeneousConstants := ArithmeticProjectiveFiniteness.homogeneousConstants
abbrev projectiveSpace := ArithmeticProjectiveFiniteness.projectiveSpace

variable {A : Type u} [CommRing A]

/-- A closed embedding in finite-dimensional projective space over the base. -/
def IsProjectiveOver (Y : SchemeOverRing A) : Prop :=
  ∃ (n : ℕ) (j : Y ⟶ projectiveSpace A n), IsClosedImmersion j.left

abbrev IsLineBundleOn (Y : SchemeOverRing A) (L : Y.left.Modules) : Prop :=
  ArithmeticProjectiveFiniteness.IsLineBundleOn A Y L

/-- The right multiplication morphism used in the quotient's kernel pair. -/
abbrev rightMultiply {G H : Grp (SchemeOverRing A)} (b : H ⟶ G) : G.X ⨯ H.X ⟶ G.X :=
  RelativeCovarianceLine.rightMultiply b

/-- A smooth flat projective quotient and the actual covariance torsor for its
line. The torsor carries the inverse character on its right overlap. -/
structure Model (A : Type u) [CommRing A] where
  torsor : RelativeCovarianceLine.Torsor A
  flat : Flat torsor.quotient.hom
  projective : IsProjectiveOver torsor.quotient
  action : ModObj torsor.group.X torsor.quotient
  quotientEquivariant : μ[torsor.group.X] ≫ torsor.projection =
    (𝟙 torsor.group.X ⊗ₘ torsor.projection) ≫ action.smul

namespace Model

variable (M : Model A)

abbrev group := M.torsor.group
abbrev borel := M.torsor.subgroup
abbrev inclusion := M.torsor.inclusion
abbrev closedSubgroup := M.torsor.closedSubgroup
abbrev smoothGroup := M.torsor.smoothGroup
abbrev smoothBorel := M.torsor.smoothSubgroup
abbrev affineGroup := M.torsor.affineGroup
abbrev flag := M.torsor.quotient
abbrev smooth := M.torsor.smoothQuotient
abbrev quotient := M.torsor.projection
abbrev quotientSurjective := M.torsor.surjectiveProjection
abbrev kernelPair := M.torsor.kernelPair
abbrev character := M.torsor.character
abbrev characterMultiplicative := M.torsor.character_mul

theorem quotientFlat : Flat M.quotient.left := by
  have : Smooth M.quotient.left := M.torsor.smoothProjection
  infer_instance

theorem quotientLfp : LocallyOfFinitePresentation M.quotient.left := by
  have : Smooth M.quotient.left := M.torsor.smoothProjection
  infer_instance

abbrev lineData : CovarianceData M.flag := M.torsor.lineData
abbrev line := M.lineData.sheaf
abbrev IsLineBundle : Prop := IsLineBundleOn M.flag M.line

/-- The linearization is induced by left multiplication on covariant
functions and satisfies its identity and composition equations. -/
abbrev HasEquivariantLine : Prop := M.torsor.HasEquivariantLine M.action

end Model

/-- An identification of the fibre action, the opposite Borel quotient and
the actual character line sheaf with those of a pinned realization of `D`. -/
structure FibreIdentification {k : Type u} [Field k] (φ : A →+* k) (M : Model A)
    (D : BasedRootDatum.{u}) (weight : D.X) where
  additive : RootGroups.AdditiveLine k
  realization : Realization D additive
  pair : OppositeBorelPair realization.pinned.pair.G
  torus_eq : pair.torus = realization.pinned.pair.T
  positive_eq : pair.positive = realization.pinned.pair.B
  projection : BorelProjection pair
  presentation : Presentation pair.negative
  kernelPair : FlagKernelPair presentation
  flagAction : ModObj realization.pinned.pair.G.val.X presentation.scheme
  flagAction_quotient :
    μ[realization.pinned.pair.G.val.X] ≫ presentation.projection =
      (𝟙 _ ⊗ₘ presentation.projection) ≫ flagAction.smul
  groupIso : (changeBase φ).mapGrp.obj M.group ≅ realization.pinned.pair.G.val
  borelIso : (changeBase φ).mapGrp.obj M.borel ≅ pair.negative.group
  flagIso : (changeBase φ).obj M.flag ≅ presentation.scheme
  inclusion_eq :
    ((changeBase φ).mapGrp.map M.inclusion) ≫ groupIso.hom =
      borelIso.hom ≫ pair.negative.inclusion
  quotient_eq : (changeBase φ).map M.quotient ≫ flagIso.hom =
    groupIso.hom.hom.hom ≫ presentation.projection
  action_eq :
    Functor.LaxMonoidal.μ (changeBase φ) M.group.X M.flag ≫
        (changeBase φ).map M.action.smul ≫ flagIso.hom =
      (groupIso.hom.hom.hom ⊗ₘ flagIso.hom) ≫ flagAction.smul
  character_eq :
    let χ : CharacterDescent.Character pair.torus.group :=
      torus_eq.symm ▸ Additive.toMul (realization.datumIso.val.weightEquiv weight)
    let b : pair.negative.group.X.left ⟶ M.borel.X.left :=
      borelIso.inv.hom.hom.left ≫ fibreProjection φ M.borel.X
    let r := (𝟙 pair.negative.group.X)⁻¹ ≫ (projection.projection ≫ χ).hom.hom
    let L := DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters
    b.appTop (M.character⁻¹ : Γ(M.borel.X.left, ⊤)ˣ) =
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ r.left.appTop)
        (MonoidAlgebra.single DiagonalizableGroups.integerGenerator (1 : k))
  lineIso :
    let χ : CharacterDescent.Character pair.torus.group :=
      torus_eq.symm ▸ Additive.toMul (realization.datumIso.val.weightEquiv weight)
    let f := flagIso.inv.left ≫ fibreProjection φ M.flag
    let g := groupIso.inv.hom.hom.left ≫ fibreProjection φ M.group.X
    ∃ (h : g ≫ M.quotient.left = presentation.projection.left ≫ f)
      (e : (Scheme.Modules.pullback f).obj M.line ≅
        flagLineSheaf presentation projection χ kernelPair),
      M.lineData.IsPullbackMap (flagLineData presentation projection χ kernelPair) f g h
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ e.hom)

open IntegralSemisimpleModel (Integers splitTorus forgetFibrePoint)

/-- The projection from the field fibre to the group over the integers. -/
abbrev integralFibreProjection {k : Type u} [Field k]
    (G : IntegralSemisimpleModel.IntegralGroup.{u}) :
    ((IntegralSemisimpleModel.fibre k).obj G).X.left ⟶ G.X.left :=
  letI : Algebra Integers.{u} k := IntegralSemisimpleModel.integerAlgebra k
  pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k)))

/-- The pins in the fibre are induced by the torus and root coordinates of
the same integer model that supplies the relative group. -/
structure MarkedIntegralFibre {k : Type u} [Field k] (φ : A →+* k)
    {D : BasedRootDatum.{u}} {weight : D.X} (M : Model A)
    (I : IntegralSemisimpleModel.Model D) (integersToBase : Integers.{u} →+* A)
    (e : (changeBase integersToBase).mapGrp.obj I.group ≅ M.group)
    (F : FibreIdentification φ M D weight) where
  groupIso : (IntegralSemisimpleModel.fibre k).obj I.group ≅ F.realization.pinned.pair.G.val
  torusIso : (IntegralSemisimpleModel.fibre k).obj (splitTorus D) ≅
    F.realization.pinned.pair.T.group
  rootCoordinate : ∀ a : D.I, Pinning.RootCoordinate F.additive F.realization.pinned.pair.T
    (F.realization.pinned.roots (F.realization.datumIso.val.indexEquiv a)).val
    (F.realization.datumIso.val.indexEquiv a).val
  group_eq :
    F.groupIso.inv.hom.hom.left ≫ fibreProjection φ M.group.X ≫ e.inv.hom.hom.left ≫
        fibreProjection integersToBase I.group.X =
      groupIso.inv.hom.hom.left ≫ integralFibreProjection (k := k) I.group
  torus_eq : ((IntegralSemisimpleModel.fibre k).map I.torus) ≫ groupIso.hom =
    torusIso.hom ≫ F.realization.pinned.pair.T.inclusion
  pin_eq : ∀ a : D.base.support, rootCoordinate a.val =
    F.realization.pinned.pin (F.realization.simpleRoot a)
  weight_eq : ∀ (R : TestAlgebra k)
      (s : AdjointRepresentation.GroupPoints ((IntegralSemisimpleModel.fibre k).obj (splitTorus D)) R),
    letI : Algebra Integers.{u} R := IntegralSemisimpleModel.integerAlgebra R
    ∀ v : IntegralSemisimpleModel.TorusValues D (CommAlgCat.of Integers.{u} R),
      forgetFibrePoint (splitTorus D) R s = IntegralSemisimpleModel.torusPoint D _ v →
      ∀ x : D.X, CharacterPairing.characterValue
        (Additive.toMul (F.realization.datumIso.val.weightEquiv x)) R
        (s ≫ torusIso.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R)
  root_eq : ∀ (a : D.I) (R : TestAlgebra k) (r : R),
    letI : Algebra Integers.{u} R := IntegralSemisimpleModel.integerAlgebra R
    forgetFibrePoint I.group R
      (RootGroups.rootPoint ((rootCoordinate a).val.hom ≫
        (F.realization.pinned.roots (F.realization.datumIso.val.indexEquiv a)).val.inclusion ≫
          groupIso.inv) R r) =
      I.line.point (CommAlgCat.of Integers.{u} R) r ≫ (I.root a).hom.hom

/-- The integral marking for the actual integer localization of the model. -/
abbrev IntegralPinning {m : ℕ} {k : Type u} [Field k] (φ : BaseRing.{u} m →+* k)
    {D : BasedRootDatum.{u}} {weight : D.X} (M : Model (BaseRing.{u} m))
    (I : IntegralSemisimpleModel.Model D)
    (e : (changeBase (algebraMap Integers.{u} (BaseRing.{u} m))).mapGrp.obj I.group ≅ M.group)
    (F : FibreIdentification φ M D weight) :=
  MarkedIntegralFibre φ M I (algebraMap Integers.{u} (BaseRing.{u} m)) e F

/-- The same arithmetic base, group, flag and line give the prescribed
pinned flag over the rationals and at every prime left in the base. -/
structure PinnedModel (D : BasedRootDatum.{u}) (weight : D.X) where
  m : ℕ
  nonzero : m ≠ 0
  model : Model (BaseRing.{u} m)
  integralGroup : IntegralSemisimpleModel.Model D
  fromIntegers : (changeBase (algebraMap Integers.{u} (BaseRing.{u} m))).mapGrp.obj
    integralGroup.group ≅ model.group
  lineBundle : model.IsLineBundle
  lineEquivariant : model.HasEquivariantLine
  fieldFibre : ∀ (k : Type u) [Field k] (φ : BaseRing.{u} m →+* k),
    ∃ F : FibreIdentification φ model D weight,
      Nonempty (IntegralPinning (m := m) φ model integralGroup fromIntegers F)

namespace PinnedModel

variable {D : BasedRootDatum.{u}} {weight : D.X} (M : PinnedModel D weight)

/-- The comparison along the canonical rational map of the selected base. -/
theorem generic : ∃ F : FibreIdentification (rationalMap M.nonzero) M.model D weight,
    Nonempty (IntegralPinning (m := M.m) (rationalMap M.nonzero) M.model M.integralGroup
      M.fromIntegers F) :=
  M.fieldFibre RationalField.{u} (rationalMap M.nonzero)

/-- The comparison along reduction at each prime that survives in the base. -/
theorem special (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ M.m) :
    ∃ F : FibreIdentification (primeMap hp) M.model D weight,
      Nonempty (IntegralPinning (m := M.m) (primeMap hp) M.model M.integralGroup
        M.fromIntegers F) :=
  M.fieldFibre (PrimeField.{u} p) (primeMap hp)

end PinnedModel

/-- One integral model works over the rational field and every non-inverted prime,
for each weight of the full lattice of a simply connected semisimple datum. -/
def Statement : Prop :=
  ∀ (D : BasedRootDatum.{u}), RootData.rationalRootAnnihilator D.datum = ⊥ →
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    ∀ weight : D.X, Nonempty (PinnedModel D weight)

end

end LinearAlgebraicGroups.Specs.IntegralFlagGeometry
