import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentDiagramComparison
import Mathlib.CategoryTheory.Whiskering
-- The mapping of triangles below adapts Mathlib's mapTriangle. Copyright (c) 2023 Joël Riou. All rights reserved. Apache-2.0. See THIRD_PARTY_NOTICES.md.
open CategoryTheory CategoryTheory.Pretriangulated

universe u v
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace Specs.DerivedFormalization.Affine.CotangentTransitivity

open _root_.DerivedFormalization.Affine
open CotangentDiagramComparison ResolvedCotangentSequence
open CotangentComplex (Model oneObject localizedModel moduleClass)
open Tensor (ModuleTensor dgCat)
open Specs.DerivedFormalization.DG
open Derived (HomotopyCategoryLaws quotient)
open DerivedKProjective (derivedCategoryInstance)
open LocalizedBimoduleExactness (classOfMap)
open DerivedBimoduleAdjunction (ConeLocalization)
open ShiftCone (cone)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]

/-- The three strict terms and their arrows, at any common final coefficient algebra. -/
abbrev leftAt {X : Chain.{u,v} k} (T : ModuleTensor.{u,v} k) (R : Resolution X)
    {E : NonpositiveCDGA.{u,v} k} (e : X.C ⟶ E) :=
  (extend T (R.Q.augmentation ≫ e)).obj (resolutionLeft T R)

abbrev middleAt {X : Chain.{u,v} k} (T : ModuleTensor.{u,v} k) (R : Resolution X)
    {E : NonpositiveCDGA.{u,v} k} (e : X.C ⟶ E) :=
  (extend T (R.Q.augmentation ≫ e)).obj R.absolute.module

abbrev rightAt {X : Chain.{u,v} k} (T : ModuleTensor.{u,v} k) (R : Resolution X)
    {E : NonpositiveCDGA.{u,v} k} (e : X.C ⟶ E) :=
  (extend T (R.Q.augmentation ≫ e)).obj R.Q.differentials.module

/-- The terminal algebra acts on every term of the resolved sequence. -/
structure ResolvedChain (T : ModuleTensor.{u,v} k) (X : Chain.{u,v} k) where
  resolution : Resolution X
  sequence : Sequence T resolution
  split (E : CommDGAlgebra.{u,v} k) (e : resolution.Q.algebra.toCommDGAlgebra ⟶ E) :
    FlatFiltration.GradedSplit ((T.baseChange e).map sequence.incl) ((T.baseChange e).map sequence.proj)
  absoluteSemifree : Semifree.IsSemifree X.A (resolution.P.base ≫ resolution.Q.base)
  coproduct : T.AlgebraCoproduct (underlying resolution.Q.base) (underlying resolution.P.augmentation)
  coproductFormulas : coproduct.Formulas
  relativeResolution :
    PushoutResolution X.second resolution.Q.augmentation coproduct coproductFormulas
  relativeDifferentials : Differentials (pushoutInr coproduct coproductFormulas)
  identifications : TermIdentifications relativeResolution relativeDifferentials
  baseProjective : KProjective.isKProjective (resolution.P.module T)
  baseFlat : T.KFlat (resolution.P.module T)
  leftGood : GoodTerm T (leftTerm T resolution.P resolution.Q)
  middleGood : GoodTerm T (middleTerm T resolution.P resolution.Q resolution.absolute)
  rightGood : GoodTerm T (rightTerm T resolution.P resolution.Q)

abbrev ResolvedChain.absoluteModel {T : ModuleTensor.{u,v} k} {X : Chain.{u,v} k}
    (R : ResolvedChain T X) : Model (X.first ≫ X.second) :=
  compositeModel R.resolution.P R.resolution.Q R.resolution.absolute R.absoluteSemifree

abbrev ResolvedChain.relativeModel {T : ModuleTensor.{u,v} k} {X : Chain.{u,v} k}
    (R : ResolvedChain T X) : Model X.second :=
  R.relativeResolution.model R.relativeDifferentials

/-- Every pair of successive semifree resolutions admits this refinement. -/
def ResolvedChainsExist : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k),
    TensorFormulas T → T.Comparisons → T.AlgebraCoproducts →
    ∀ {X : Chain.{u,v} k} (R : Resolution X),
      ∃ Z : ResolvedChain T X, Z.resolution = R

/-- The native sequence uses the augmentation followed by the identity. -/
theorem projectiveAtIdentity {T : ModuleTensor.{u,v} k} {X : Chain.{u,v} k}
    (R : ResolvedChain T X) :
    KProjective.isKProjective (leftAt T R.resolution (𝟙 X.C)) ∧
    KProjective.isKProjective (middleAt T R.resolution (𝟙 X.C)) ∧
    KProjective.isKProjective (rightAt T R.resolution (𝟙 X.C)) := by
  constructor
  · change KProjective.isKProjective ((extend T (R.resolution.Q.augmentation ≫ 𝟙 X.C)).obj _)
    rw [Category.comp_id]
    exact R.leftGood.2.1
  constructor
  · change KProjective.isKProjective ((extend T (R.resolution.Q.augmentation ≫ 𝟙 X.C)).obj _)
    rw [Category.comp_id]
    exact R.middleGood.2.1
  · change KProjective.isKProjective ((extend T (R.resolution.Q.augmentation ≫ 𝟙 X.C)).obj _)
    rw [Category.comp_id]
    exact R.rightGood.2.1

section Localized

variable {T : ModuleTensor.{u,v} k} {X Y Z : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
variable {h : HomotopyCategoryLaws (oneObject E)}

/-- A chosen realization of the signed boundary in the common localization.
The third term of the cone is identified by its coordinate projection onto the quotient. -/
structure SequenceTriangle (K : ConeLocalization (oneObject E) h)
    {R : Resolution X} (F : Sequence T R) (e : X.C ⟶ E) where
  quotientMap : cone (inclusionAt F e) ⟶ rightAt T R e
  quotientFormula : IsConeQuotient (projectionAt F e) quotientMap
  quotientIso :
    letI := Derived.homotopyCategory (oneObject E) h
    letI := derivedCategoryInstance (oneObject E) h
    (quotient (oneObject E) h).obj (cone (inclusionAt F e)) ≅
      (quotient (oneObject E) h).obj (rightAt T R e)
  quotientIso_hom :
    letI := Derived.homotopyCategory (oneObject E) h
    letI := derivedCategoryInstance (oneObject E) h
    quotientIso.hom = (quotient (oneObject E) h).map (classOfMap h quotientMap)
  distinguished :
    letI := derivedCategoryInstance (oneObject E) h
    letI := K.shiftD
    letI := K.addD
    letI := K.zeroD
    letI := K.addShiftD
    letI := K.trianglesD
    localizedSequenceTriangle h K
      (inclusionAt F e) (projectionAt F e) quotientIso ∈ distTriang (Derived.derivedCategory (oneObject E) h)

abbrev SequenceTriangle.triangle {K : ConeLocalization (oneObject E) h}
    {R : Resolution X} {F : Sequence T R} {e : X.C ⟶ E}
    (U : SequenceTriangle K F e) :=
  localizedSequenceTriangle h K
    (inclusionAt F e) (projectionAt F e) U.quotientIso

variable (K : ConeLocalization (oneObject E) h)

/-- The comparison uses the differentiated lifts on all three terms,
including the square with the connecting arrow. -/
structure Naturality (T : ModuleTensor.{u,v} k) where
  strict : CotangentDiagramComparison.ComparisonSystem T E
  triangle (X : Chain.{u,v} k) (R : ResolvedChain T X) (e : X.C ⟶ E) :
    SequenceTriangle K R.sequence e
  map {X Y : Chain.{u,v} k} (f : ChainMap X Y) (R : ResolvedChain T X) (S : ResolvedChain T Y)
      (e : X.C ⟶ E) (d : Y.C ⟶ E) (he : e = f.c ≫ d) :
    letI := derivedCategoryInstance (oneObject E) h
    letI := K.shiftD
    (triangle X R e).triangle ⟶ (triangle Y S d).triangle
  components {X Y : Chain.{u,v} k} {f : ChainMap X Y}
      (R : ResolvedChain T X) (S : ResolvedChain T Y)
      (e : X.C ⟶ E) (d : Y.C ⟶ E) (he : e = f.c ≫ d) (l : Lift f R.resolution S.resolution) :
    letI := Derived.homotopyCategory (oneObject E) h
    letI := derivedCategoryInstance (oneObject E) h
    letI := K.shiftD
    let Q := quotient (oneObject E) h
    let m := strict.map l R.sequence S.sequence e d he
    let n := map f R S e d he
    n.hom₁ = Q.map (classOfMap h m.left) ∧ n.hom₂ = Q.map (classOfMap h m.middle) ∧
      n.hom₃ = Q.map (classOfMap h m.right)
  identity (X : Chain.{u,v} k) (R : ResolvedChain T X) (e : X.C ⟶ E) :
    letI := derivedCategoryInstance (oneObject E) h
    letI := K.shiftD
    map (ChainMap.id X) R R e e (Category.id_comp e).symm = 𝟙 _
  composition {X Y Z : Chain.{u,v} k} (f : ChainMap X Y) (g : ChainMap Y Z)
      (R : ResolvedChain T X) (S : ResolvedChain T Y) (V : ResolvedChain T Z)
      (e : X.C ⟶ E) (d : Y.C ⟶ E) (c : Z.C ⟶ E)
      (hf : e = f.c ≫ d) (hg : d = g.c ≫ c) :
    letI := derivedCategoryInstance (oneObject E) h
    letI := K.shiftD
    map (f.comp g) R V e c (by rw [hf, hg]; exact (Category.assoc _ _ _).symm) =
      map f R S e d hf ≫ map g S V d c hg
  changeResolution (X : Chain.{u,v} k) (R S : ResolvedChain T X) (e : X.C ⟶ E) :
    letI := derivedCategoryInstance (oneObject E) h
    letI := K.shiftD
    IsIso (map (ChainMap.id X) R S e e (Category.id_comp e).symm)

/-- All chains can be compared inside the same one-object localization at the common
coefficient bound. Here the coefficient universe is arbitrary and Unit is small in it. -/
def NaturalSequenceTriangles : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k),
    TensorFormulas T → T.Comparisons →
    ∀ (E : NonpositiveCDGA.{u,v} k) (h : HomotopyCategoryLaws (oneObject E))
      (K : ConeLocalization (oneObject E) h), Nonempty (Naturality K T)

/-- Shift by one in the indicated cone localization. -/
abbrev translation {E : NonpositiveCDGA.{u,v} k} {h : HomotopyCategoryLaws (oneObject E)}
    (K : ConeLocalization (oneObject E) h) :
    letI := derivedCategoryInstance (oneObject E) h
    Derived.derivedCategory (oneObject E) h ⥤ Derived.derivedCategory (oneObject E) h :=
  letI := derivedCategoryInstance (oneObject E) h
  letI := K.shiftD
  shiftFunctor _ (1 : ℤ)

abbrev SequenceTriangle.boundary {K : ConeLocalization (oneObject E) h}
    {R : Resolution X} {F : Sequence T R} {e : X.C ⟶ E}
    (U : SequenceTriangle K F e) :
    letI := Derived.homotopyCategory (oneObject E) h
    letI := derivedCategoryInstance (oneObject E) h
    let Q := quotient (oneObject E) h
    Q.obj (rightAt T R e) ⟶ (translation K).obj (Q.obj (leftAt T R e)) :=
  letI := Derived.homotopyCategory (oneObject E) h
  letI := derivedCategoryInstance (oneObject E) h
  letI := K.shiftD
  U.triangle.mor₃

/-- The cone localization used by an exact scalar extension and the fixed common
localization give the same boundary under their comparison of translations. -/
def BoundaryComparison : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {T : ModuleTensor.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
    (h : HomotopyCategoryLaws (oneObject E))
    (K K' : ConeLocalization (oneObject E) h),
    letI := Derived.homotopyCategory (oneObject E) h
    letI := derivedCategoryInstance (oneObject E) h
    let Q := quotient (oneObject E) h
    ∃ s : translation K ≅ translation K',
      (∀ M : E.Module, (K.onShift M 1).hom ≫ s.hom.app (Q.obj M) = (K'.onShift M 1).hom) ∧
      ∀ {X : Chain.{u,v} k} {R : ResolvedChain T X} {e : X.C ⟶ E}
        (U : SequenceTriangle K R.sequence e) (V : SequenceTriangle K' R.sequence e),
        U.boundary ≫ s.hom.app (Q.obj (leftAt T R.resolution e)) = V.boundary

end Localized

section Identifications

open DerivedTensor (ScalarExtension)

variable {T : ModuleTensor.{u,v} k} {X : Chain.{u,v} k}
variable {hB : HomotopyCategoryLaws (oneObject X.B)} {hC : HomotopyCategoryLaws (oneObject X.C)}

local notation "D₀" => Derived.derivedCategory
local notation "L₀" => localizedModel

/-- The resolved triangle on the cotangent models, with the inclusion and quotient
transported by their identifications on differential symbols. -/
def IdentifiesCotangentTriangle
    (K : ConeLocalization (oneObject X.C) hC)
    (E : ScalarExtension T (underlying X.second) hB hC)
    (R : ResolvedChain T X) (U : SequenceTriangle K R.sequence (𝟙 X.C)) : Prop :=
    letI := Derived.homotopyCategory (oneObject X.C) hC
    letI := derivedCategoryInstance (oneObject X.B) hB
    letI := derivedCategoryInstance (oneObject X.C) hC
    letI := K.shiftD
    letI := K.addD
    letI := K.zeroD
    letI := K.addShiftD
    letI := K.trianglesD
    let Q := quotient (oneObject X.C) hC
    let F := R.sequence
    let I := R.identifications
    let a := E.onProjective (R.resolution.P.module T) R.baseProjective
    ∃ (δ : L₀ hC R.relativeModel T ⟶
          (shiftFunctor (D₀ (oneObject X.C) hC) (1 : ℤ)).obj
            (E.functor.obj (L₀ hB R.resolution.P T))),
      let V := Triangle.mk (a.hom ≫ Q.map (moduleClass hC (I.inclusion F)))
        (Q.map (moduleClass hC (I.projection F))) δ
      V ∈ distTriang (D₀ (oneObject X.C) hC) ∧
      ∃ i : U.triangle ≅ V,
        i.inv.hom₁ =
          a.hom ≫ Q.map (moduleClass hC I.left.inv) ≫
            eqToHom (congrArg Q.obj (congrArg (fun e : R.resolution.Q.algebra ⟶ X.C =>
              (extend T e).obj (resolutionLeft T R.resolution)) (Category.comp_id _).symm)) ∧
        i.inv.hom₂ = eqToHom (congrArg Q.obj
          (congrArg (fun e : R.resolution.Q.algebra ⟶ X.C =>
            (extend T e).obj R.resolution.absolute.module) (Category.comp_id _).symm)) ∧
        i.hom.hom₃ = eqToHom (congrArg Q.obj
          (congrArg (fun e : R.resolution.Q.algebra ⟶ X.C =>
            (extend T e).obj R.resolution.Q.differentials.module) (Category.comp_id _))) ≫
          Q.map (moduleClass hC I.right.hom)

def IdentifiedTriangles : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {T : ModuleTensor.{u,v} k} {X : Chain.{u,v} k}
    (hB : HomotopyCategoryLaws (oneObject X.B)) (hC : HomotopyCategoryLaws (oneObject X.C))
    (K : ConeLocalization (oneObject X.C) hC)
    (E : ScalarExtension T (underlying X.second) hB hC)
    (R : ResolvedChain T X) (U : SequenceTriangle K R.sequence (𝟙 X.C)),
    IdentifiesCotangentTriangle K E R U

end Identifications

section Extension

open DerivedTensor (ScalarExtension)
open BimoduleAdjunction (ordinaryTensor)

/-- The ordinary tensor of the augmented sequence is identified with the sequence
computed directly at the new final coefficients by the balanced tensor associator. -/
abbrev extendedSequenceIso {T : ModuleTensor.{u,v} k} {X : Chain.{u,v} k}
    {R : ResolvedChain T X} {D : NonpositiveCDGA.{u,v} k} (w : X.C ⟶ D)
    {hC : HomotopyCategoryLaws (oneObject X.C)} {hD : HomotopyCategoryLaws (oneObject D)}
    (E : ScalarExtension T (underlying w) hC hD)
    (a : ExtensionAssociator T R.resolution.Q.augmentation (𝟙 X.C) w) :
    extend T (R.resolution.Q.augmentation ≫ 𝟙 X.C) ⋙ ordinaryTensor E.models.tensor ≅
      extend T (R.resolution.Q.augmentation ≫ w) :=
  Functor.isoWhiskerLeft _ (eqToIso E.strict) ≪≫ a.iso ≪≫
    eqToIso (congrArg (fun z : X.C ⟶ D => extend T (R.resolution.Q.augmentation ≫ z))
      (Category.id_comp w))

/-- The actual derived image triangle agrees with the directly extended resolved
triangle, on the three specified term comparisons and on the boundary. Its
comparison with a new chain is induced by every lift of that chain map. -/
def ExtendedTriangles : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {T : ModuleTensor.{u,v} k},
    TensorFormulas T → T.Comparisons →
    ∀ {X : Chain.{u,v} k} {D : NonpositiveCDGA.{u,v} k} (w : X.C ⟶ D)
      (hC : HomotopyCategoryLaws (oneObject X.C)) (hD : HomotopyCategoryLaws (oneObject D))
      (E : ScalarExtension T (underlying w) hC hD)
      (R : ResolvedChain T X),
    letI := Derived.homotopyCategory (oneObject D) hD
    letI := derivedCategoryInstance (oneObject X.C) hC
    letI := derivedCategoryInstance (oneObject D) hD
    let Q := quotient (oneObject D) hD
    ∃ (KC : ConeLocalization (oneObject X.C) hC) (KD : ConeLocalization (oneObject D) hD),
      letI := KC.shiftD
      letI := KD.shiftD
      ∃ (s : E.functor.CommShift ℤ),
        letI := s
        letI := KD.addD
        letI := KD.zeroD
        letI := KD.addShiftD
        letI := KD.trianglesD
        ∀ (NC : Naturality KC T) (ND : Naturality KD T),
        ∃ (a : ExtensionAssociator T R.resolution.Q.augmentation (𝟙 X.C) w)
          (j : E.functor.mapTriangle.obj (NC.triangle X R (𝟙 X.C)).triangle ≅
                (ND.triangle X R w).triangle),
          let b := (extendedSequenceIso w E a).hom
          E.functor.mapTriangle.obj (NC.triangle X R (𝟙 X.C)).triangle ∈
            distTriang (Derived.derivedCategory (oneObject D) hD) ∧
          j.hom.hom₁ = (E.data.onProjective _ (projectiveAtIdentity R).1).hom ≫
            Q.map (classOfMap hD (b.app (resolutionLeft T R.resolution))) ∧
          j.hom.hom₂ = (E.data.onProjective _ (projectiveAtIdentity R).2.1).hom ≫
            Q.map (classOfMap hD (b.app R.resolution.absolute.module)) ∧
          j.hom.hom₃ = (E.data.onProjective _ (projectiveAtIdentity R).2.2).hom ≫
            Q.map (classOfMap hD (b.app R.resolution.Q.differentials.module)) ∧
          ∀ {Y : Chain.{u,v} k} (f : ChainMap X Y) (S : ResolvedChain T Y)
            (d : Y.C ⟶ D) (he : w = f.c ≫ d) (l : Lift f R.resolution S.resolution),
            let m := ND.strict.map l R.sequence S.sequence w d he
            let n := j.hom ≫ ND.map f R S w d he
            n.hom₁ = j.hom.hom₁ ≫ Q.map (classOfMap hD m.left) ∧
            n.hom₂ = j.hom.hom₂ ≫ Q.map (classOfMap hD m.middle) ∧
            n.hom₃ = j.hom.hom₃ ≫ Q.map (classOfMap hD m.right) ∧
            ∀ {U : Triangle (Derived.derivedCategory (oneObject X.C) hC)}
              {V : Triangle (Derived.derivedCategory (oneObject D) hD)}
              (i : (NC.triangle X R (𝟙 X.C)).triangle ≅ U)
              (i' : (ND.triangle Y S d).triangle ≅ V),
              ∃ g : E.functor.mapTriangle.obj U ⟶ V,
                g.hom₁ = E.functor.map i.inv.hom₁ ≫ j.hom.hom₁ ≫
                  Q.map (classOfMap hD m.left) ≫ i'.hom.hom₁ ∧
                g.hom₂ = E.functor.map i.inv.hom₂ ≫ j.hom.hom₂ ≫
                  Q.map (classOfMap hD m.middle) ≫ i'.hom.hom₂ ∧
                g.hom₃ = E.functor.map i.inv.hom₃ ≫ j.hom.hom₃ ≫
                  Q.map (classOfMap hD m.right) ≫ i'.hom.hom₃

end Extension

open DerivedTensor (ScalarExtension)

/-- Transitivity at a common adequate coefficient level, with one choice of
scalar extensions and resolution comparisons for all chains at that level. -/
def Transitivity : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k],
    ∃ (T : ModuleTensor.{u,v} k)
      (h : ∀ A : NonpositiveCDGA.{u,v} k, HomotopyCategoryLaws (oneObject A))
      (K : ∀ A : NonpositiveCDGA.{u,v} k, ConeLocalization (oneObject A) (h A))
      (E : ∀ {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B),
        ScalarExtension T (underlying f) (h A) (h B))
      (N : ∀ A : NonpositiveCDGA.{u,v} k, Naturality (K A) T),
      (∀ {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B),
        Nonempty (CotangentComplex.ComparisonSystem T f (h B))) ∧
      ∀ X : Chain.{u,v} k, ∃ R : ResolvedChain T X,
        IdentifiesCotangentTriangle (K X.C) (E X.second) R ((N X.C).triangle X R (𝟙 X.C))

section Coefficients

open CategoryTheory
open CotangentComplex (cdgaLift LiftedModel)
open DerivedTensor (ExtensionTransport liftAlgebra liftInput)
open DerivedCoefficientLift (Descent)

universe t

/-- A chain represented using the degreewise linear transport to the common bound. -/
abbrev liftChain (X : Chain.{u,v} k) : Chain.{u,max v t} k where
  A := (cdgaLift.{u,v,max v t} k).obj X.A
  B := (cdgaLift.{u,v,max v t} k).obj X.B
  C := (cdgaLift.{u,v,max v t} k).obj X.C
  first := (cdgaLift.{u,v,max v t} k).map X.first
  second := (cdgaLift.{u,v,max v t} k).map X.second

def liftChainMap {X Y : Chain.{u,v} k} (f : ChainMap X Y) :
    ChainMap (liftChain.{u,v,t} X) (liftChain.{u,v,t} Y) where
  a := (cdgaLift.{u,v,max v t} k).map f.a
  b := (cdgaLift.{u,v,max v t} k).map f.b
  c := (cdgaLift.{u,v,max v t} k).map f.c
  first_comm := by
    change (cdgaLift.{u,v,max v t} k).map X.first ≫ (cdgaLift.{u,v,max v t} k).map f.b =
      (cdgaLift.{u,v,max v t} k).map f.a ≫ (cdgaLift.{u,v,max v t} k).map Y.first
    rw [← Functor.map_comp, f.first_comm, Functor.map_comp]
  second_comm := by
    change (cdgaLift.{u,v,max v t} k).map X.second ≫ (cdgaLift.{u,v,max v t} k).map f.c =
      (cdgaLift.{u,v,max v t} k).map f.b ≫ (cdgaLift.{u,v,max v t} k).map Y.second
    rw [← Functor.map_comp, f.second_comm, Functor.map_comp]

/-- Transport the successive resolutions and their three differential models. -/
structure LiftedResolution {T : ModuleTensor.{u,v} k} (T' : ModuleTensor.{u,max v t} k)
    {X : Chain.{u,v} k} (R : ResolvedChain T X) where
  base : LiftedModel.{u,v,max v t} T T' R.resolution.P
  step : LiftedModel.{u,v,max v t} T T' R.resolution.Q
  absolute : LiftedModel.{u,v,max v t} T T' R.absoluteModel

/-- Regard a differential model as relative to an equal coefficient map. -/
abbrev rebaseDifferentials {A B : NonpositiveCDGA.{u,v} k} {f g : A ⟶ B}
    (h : f = g) (O : Differentials f) : Differentials g :=
  h ▸ O

abbrev LiftedResolution.resolution {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    {X : Chain.{u,v} k} {R : ResolvedChain T X} (U : LiftedResolution.{u,v,t} T' R) :
    Resolution (liftChain.{u,v,t} X) where
  P := U.base.model
  Q :=
    { algebra := (cdgaLift.{u,v,max v t} k).obj R.resolution.Q.algebra
      base := (cdgaLift.{u,v,max v t} k).map R.resolution.Q.base
      augmentation := (cdgaLift.{u,v,max v t} k).map R.resolution.Q.augmentation
      triangle := by
        change (cdgaLift.{u,v,max v t} k).map R.resolution.Q.base ≫
          (cdgaLift.{u,v,max v t} k).map R.resolution.Q.augmentation =
          (cdgaLift.{u,v,max v t} k).map R.resolution.P.augmentation ≫
            (cdgaLift.{u,v,max v t} k).map X.second
        rw [← Functor.map_comp, R.resolution.Q.triangle, Functor.map_comp]
      semifree := U.step.semifree
      surjective := U.step.surjective
      quasiIso := U.step.quasiIso
      differentials := U.step.differentials }
  absolute := rebaseDifferentials
    ((cdgaLift.{u,v,max v t} k).map_comp R.resolution.P.base R.resolution.Q.base)
    U.absolute.differentials

/-- The choice of a lift may be transported before forming the triangle comparison. -/
def LiftedResolution.lift {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    {X Y : Chain.{u,v} k} {R : ResolvedChain T X} {S : ResolvedChain T Y}
    {f : ChainMap X Y} (U : LiftedResolution.{u,v,t} T' R) (V : LiftedResolution.{u,v,t} T' S)
    (l : Lift f R.resolution S.resolution) :
    Lift (liftChainMap.{u,v,t} f) U.resolution V.resolution where
  p := (cdgaLift.{u,v,max v t} k).map l.p
  q := (cdgaLift.{u,v,max v t} k).map l.q
  p_base := by
    change (cdgaLift.{u,v,max v t} k).map R.resolution.P.base ≫ (cdgaLift.{u,v,max v t} k).map l.p =
      (cdgaLift.{u,v,max v t} k).map f.a ≫ (cdgaLift.{u,v,max v t} k).map S.resolution.P.base
    rw [← Functor.map_comp, l.p_base, Functor.map_comp]
  p_aug := by
    change (cdgaLift.{u,v,max v t} k).map l.p ≫ (cdgaLift.{u,v,max v t} k).map S.resolution.P.augmentation =
      (cdgaLift.{u,v,max v t} k).map R.resolution.P.augmentation ≫ (cdgaLift.{u,v,max v t} k).map f.b
    rw [← Functor.map_comp, l.p_aug, Functor.map_comp]
  q_base := by
    change (cdgaLift.{u,v,max v t} k).map R.resolution.Q.base ≫ (cdgaLift.{u,v,max v t} k).map l.q =
      (cdgaLift.{u,v,max v t} k).map l.p ≫ (cdgaLift.{u,v,max v t} k).map S.resolution.Q.base
    rw [← Functor.map_comp, l.q_base, Functor.map_comp]
  q_aug := by
    change (cdgaLift.{u,v,max v t} k).map l.q ≫ (cdgaLift.{u,v,max v t} k).map S.resolution.Q.augmentation =
      (cdgaLift.{u,v,max v t} k).map R.resolution.Q.augmentation ≫ (cdgaLift.{u,v,max v t} k).map f.c
    rw [← Functor.map_comp, l.q_aug, Functor.map_comp]

open Tensor (term)

/-- The strict comparisons with the scalar-extended lifted differentials.
Their coordinate rules fix the horizontal maps in the sequence comparison. -/
structure LiftedSequence {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    {X : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
    (R : ResolvedChain T X) (S : ResolvedChain T' (liftChain.{u,v,t} X)) (e : X.C ⟶ E) where
  left : (liftInput.{u,v,t} E.toCommDGAlgebra).obj (leftAt T R.resolution e) ≅
    leftAt T' S.resolution ((cdgaLift.{u,v,max v t} k).map e)
  middle : (liftInput.{u,v,t} E.toCommDGAlgebra).obj (middleAt T R.resolution e) ≅
    middleAt T' S.resolution ((cdgaLift.{u,v,max v t} k).map e)
  right : (liftInput.{u,v,t} E.toCommDGAlgebra).obj (rightAt T R.resolution e) ≅
    rightAt T' S.resolution ((cdgaLift.{u,v,max v t} k).map e)
  incl_comm : (liftInput.{u,v,t} E.toCommDGAlgebra).map (inclusionAt R.sequence e) ≫ middle.hom =
      left.hom ≫ inclusionAt S.sequence ((cdgaLift.{u,v,max v t} k).map e)
  proj_comm : (liftInput.{u,v,t} E.toCommDGAlgebra).map (projectionAt R.sequence e) ≫ right.hom =
      middle.hom ≫ projectionAt S.sequence ((cdgaLift.{u,v,max v t} k).map e)

/-- The lifted maps are the differentiated lifts of the same algebra comparisons. -/
def LiftedSequenceNaturality {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    {X Y : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
    {R : ResolvedChain T X} {S : ResolvedChain T Y}
    {R' : ResolvedChain T' (liftChain.{u,v,t} X)}
    {S' : ResolvedChain T' (liftChain.{u,v,t} Y)}
    {e : X.C ⟶ E} {d : Y.C ⟶ E}
    (a : LiftedSequence R R' e) (b : LiftedSequence S S' d)
    (m : MapAt R.sequence S.sequence e d)
    (m' : MapAt R'.sequence S'.sequence
      ((cdgaLift.{u,v,max v t} k).map e) ((cdgaLift.{u,v,max v t} k).map d)) : Prop :=
  let J := liftInput.{u,v,t} E.toCommDGAlgebra
  J.map m.left ≫ b.left.hom = a.left.hom ≫ m'.left ∧
  J.map m.middle ≫ b.middle.hom = a.middle.hom ≫ m'.middle ∧
  J.map m.right ≫ b.right.hom = a.right.hom ≫ m'.right

open ShiftCone (shift)

/-- Mapping a triangle only uses commutation with shift by one. -/
def mapTriangleWithShift {D D' : Type*} [Category* D] [Category* D']
    [HasShift D ℤ] [HasShift D' ℤ] (F : D ⥤ D')
    (s : shiftFunctor D (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor D' (1 : ℤ)) :
    Triangle D ⥤ Triangle D' where
  obj V := Triangle.mk (F.map V.mor₁) (F.map V.mor₂)
    (F.map V.mor₃ ≫ s.hom.app V.obj₁)
  map f :=
    { hom₁ := F.map f.hom₁
      hom₂ := F.map f.hom₂
      hom₃ := F.map f.hom₃
      comm₁ := by dsimp; simp only [← F.map_comp, f.comm₁]
      comm₂ := by dsimp; simp only [← F.map_comp, f.comm₂]
      comm₃ := by
        dsimp [Functor.comp]
        simp only [Category.assoc, ← NatTrans.naturality, ← F.map_comp_assoc, f.comm₃] }
  map_id V := by ext <;> exact F.map_id _
  map_comp f g := by ext <;> exact F.map_comp _ _

section LiftShift

variable {E : NonpositiveCDGA.{u,v} k}
variable {h : HomotopyCategoryLaws (oneObject E)}
variable {h' : HomotopyCategoryLaws (oneObject ((cdgaLift.{u,v,max v t} k).obj E))}
variable (K : ConeLocalization (oneObject E) h)
variable (K' : ConeLocalization (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h')
variable (d : Descent h h' (liftInput.{u,v,t} E.toCommDGAlgebra))

/-- The comparison of derived shifts is normalized on representatives by the
degreewise coefficient comparison with the signed strict shift. -/
structure LiftedShift where
  strict (M : E.Module) :
    (liftInput.{u,v,t} E.toCommDGAlgebra).obj (shift M 1) ≅
      shift ((liftInput.{u,v,t} E.toCommDGAlgebra).obj M) 1
  coordinates (M : E.Module) (n : ℤ)
      (x : term ((liftInput.{u,v,t} E.toCommDGAlgebra).obj (shift M 1)) n) :
    (((strict M).hom.app ()).f n x).down = x.down
  iso :
    letI := derivedCategoryInstance (oneObject E) h
    letI := derivedCategoryInstance (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
    translation K ⋙ d.D ≅ d.D ⋙ translation K'
  normalized (M : E.Module) :
    let E' := (cdgaLift.{u,v,max v t} k).obj E
    letI := Derived.homotopyCategory (oneObject E) h
    letI := Derived.homotopyCategory (oneObject E') h'
    letI := derivedCategoryInstance (oneObject E) h
    letI := derivedCategoryInstance (oneObject E') h'
    let Q := quotient (oneObject E) h
    let Q' := quotient (oneObject E') h'
    d.D.map (K.onShift M 1).hom ≫ iso.hom.app (Q.obj M) ≫
        (translation K').map (d.representedIso M).hom =
      (d.representedIso (shift M 1)).hom ≫ Q'.map (classOfMap h' (strict M).hom) ≫
        (K'.onShift ((liftInput.{u,v,t} E.toCommDGAlgebra).obj M) 1).hom

abbrev LiftedShift.triangles (s : LiftedShift K K' d) :=
  letI := derivedCategoryInstance (oneObject E) h
  letI := derivedCategoryInstance (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
  letI := K.shiftD
  letI := K'.shiftD
  mapTriangleWithShift d.D s.iso

end LiftShift

/-- The strict term comparisons carry each unit tensor of a differential
symbol to the unit tensor of the corresponding lifted symbol. -/
def LiftedSequence.PreservesSymbols {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    {X : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
    {R : ResolvedChain T X} {R' : ResolvedChain T' (liftChain.{u,v,t} X)}
    {e : X.C ⟶ E} (a : LiftedSequence R R' e)
    (U : LiftedResolution.{u,v,t} T' R) : Prop :=
  let e' := (cdgaLift.{u,v,max v t} k).map e
  (∀ n x, HEq ((a.left.hom.app ()).f n (ULift.up (leftSymbol T R.resolution e n x)))
    (leftSymbol T' U.resolution e' n (ULift.up x))) ∧
  (∀ n x, HEq ((a.middle.hom.app ()).f n (ULift.up (middleSymbol T R.resolution e n x)))
    (middleSymbol T' U.resolution e' n (ULift.up x))) ∧
  (∀ n x, HEq ((a.right.hom.app ()).f n (ULift.up (rightSymbol T R.resolution e n x)))
    (rightSymbol T' U.resolution e' n (ULift.up x)))

section LiftTriangle

variable {E : NonpositiveCDGA.{u,v} k}
variable {h : HomotopyCategoryLaws (oneObject E)}
variable {h' : HomotopyCategoryLaws (oneObject ((cdgaLift.{u,v,max v t} k).obj E))}
variable {K : ConeLocalization (oneObject E) h}
variable {K' : ConeLocalization (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'}
variable {d : Descent h h' (liftInput.{u,v,t} E.toCommDGAlgebra)}

abbrev representedCoefficientMap {M : E.Module}
    {M' : ((cdgaLift.{u,v,max v t} k).obj E).Module}
    (a : (liftInput.{u,v,t} E.toCommDGAlgebra).obj M ≅ M') :=
  let E' := (cdgaLift.{u,v,max v t} k).obj E
  letI := Derived.homotopyCategory (oneObject E) h
  letI := Derived.homotopyCategory (oneObject E') h'
  letI := derivedCategoryInstance (oneObject E) h
  letI := derivedCategoryInstance (oneObject E') h'
  let Q' := quotient (oneObject E') h'
  (d.representedIso M).hom ≫ Q'.map (classOfMap h' a.hom)

/-- The derived comparison intertwines all three arrows. Its components are
the localized strict comparisons, via the fixed localization square. -/
structure LiftedTriangle {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    {X : Chain.{u,v} k}
    {R : ResolvedChain T X} {R' : ResolvedChain T' (liftChain.{u,v,t} X)}
    {e : X.C ⟶ E} (a : LiftedSequence R R' e)
    (s : LiftedShift K K' d) (U : SequenceTriangle K R.sequence e)
    (V : SequenceTriangle K' R'.sequence ((cdgaLift.{u,v,max v t} k).map e)) where
  iso :
    let E' := (cdgaLift.{u,v,max v t} k).obj E
    letI := derivedCategoryInstance (oneObject E) h
    letI := derivedCategoryInstance (oneObject E') h'
    letI := K.shiftD
    letI := K'.shiftD
    s.triangles.obj U.triangle ≅ V.triangle
  components :
    let E' := (cdgaLift.{u,v,max v t} k).obj E
    letI := derivedCategoryInstance (oneObject E) h
    letI := derivedCategoryInstance (oneObject E') h'
    letI := K.shiftD
    letI := K'.shiftD
    iso.hom.hom₁ = representedCoefficientMap (d := d) a.left ∧
    iso.hom.hom₂ = representedCoefficientMap (d := d) a.middle ∧
    iso.hom.hom₃ = representedCoefficientMap (d := d) a.right

end LiftTriangle

/-- The three A08 recoveries at the common bound use the same localization
square as both scalar extensions. -/
def CommonBoundTerms {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    {h : ∀ A : CommDGAlgebra.{u,v} k, HomotopyCategoryLaws (dgCat A)}
    {h' : ∀ A : CommDGAlgebra.{u,max v t} k, HomotopyCategoryLaws (dgCat A)}
    (d : ∀ A : CommDGAlgebra.{u,v} k,
      Descent (h A) (h' (liftAlgebra.{u,v,t} A)) (liftInput.{u,v,t} A))
    {X : Chain.{u,v} k}
    (G : ScalarExtension T (underlying X.second) (h X.B.toCommDGAlgebra) (h X.C.toCommDGAlgebra))
    (G' : ScalarExtension T' (underlying (liftChain.{u,v,t} X).second)
      (h' (liftChain.{u,v,t} X).B.toCommDGAlgebra) (h' (liftChain.{u,v,t} X).C.toCommDGAlgebra))
    (R : ResolvedChain T X) (S : ResolvedChain T' (liftChain.{u,v,t} X)) : Prop :=
  let Y := liftChain.{u,v,t} X
  let hB := h X.B.toCommDGAlgebra
  let hC := h X.C.toCommDGAlgebra
  let hB' := h' Y.B.toCommDGAlgebra
  let hC' := h' Y.C.toCommDGAlgebra
  letI := derivedCategoryInstance (oneObject X.B) hB
  letI := derivedCategoryInstance (oneObject X.C) hC
  letI := derivedCategoryInstance (oneObject Y.B) hB'
  letI := derivedCategoryInstance (oneObject Y.C) hC'
  let J := (d X.C.toCommDGAlgebra).D
  Nonempty (J.obj (G.functor.obj (localizedModel hB R.resolution.P T)) ≅
    G'.functor.obj (localizedModel hB' S.resolution.P T')) ∧
  Nonempty (J.obj (localizedModel hC R.absoluteModel T) ≅ localizedModel hC' S.absoluteModel T') ∧
  Nonempty (J.obj (localizedModel hC R.relativeModel T) ≅ localizedModel hC' S.relativeModel T')

/-- The equality of the final augmentations is transported along the same
coefficient functor as the finite diagram. -/
theorem liftFinalMap {X Y : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
    (f : ChainMap X Y) {e : X.C ⟶ E} {c : Y.C ⟶ E} (he : e = f.c ≫ c) :
    (cdgaLift.{u,v,max v t} k).map e =
      (liftChainMap.{u,v,t} f).c ≫ (cdgaLift.{u,v,max v t} k).map c := by
  rw [he]
  exact (cdgaLift.{u,v,max v t} k).map_comp f.c c

/-- Simultaneous transport of the resolved triangles for all chains into the
localization of the lifted final coefficient algebra. -/
structure CommonBoundComparisons {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    {h : ∀ A : CommDGAlgebra.{u,v} k, HomotopyCategoryLaws (dgCat A)}
    {h' : ∀ A : CommDGAlgebra.{u,max v t} k, HomotopyCategoryLaws (dgCat A)}
    (d : ∀ A : CommDGAlgebra.{u,v} k,
      Descent (h A) (h' (liftAlgebra.{u,v,t} A)) (liftInput.{u,v,t} A))
    (K : ∀ E : NonpositiveCDGA.{u,v} k, ConeLocalization (oneObject E) (h E.toCommDGAlgebra))
    (K' : ∀ E : NonpositiveCDGA.{u,max v t} k, ConeLocalization (oneObject E) (h' E.toCommDGAlgebra))
    (N : ∀ E, Naturality (K E) T) (N' : ∀ E, Naturality (K' E) T') where
  shiftComparison (E : NonpositiveCDGA.{u,v} k) :
    LiftedShift (K E) (K' ((cdgaLift.{u,v,max v t} k).obj E)) (d E.toCommDGAlgebra)
  liftResolution {X : Chain.{u,v} k} (R : ResolvedChain T X) : LiftedResolution.{u,v,t} T' R
  resolved {X : Chain.{u,v} k} (R : ResolvedChain T X) : ResolvedChain T' (liftChain.{u,v,t} X)
  resolution_eq {X : Chain.{u,v} k} (R : ResolvedChain T X) :
    (resolved R).resolution = (liftResolution R).resolution
  sequence {X : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
      (R : ResolvedChain T X) (e : X.C ⟶ E) :
    LiftedSequence R (resolved R) e
  symbols {X : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
      (R : ResolvedChain T X) (e : X.C ⟶ E) :
    (sequence R e).PreservesSymbols (liftResolution R)
  triangle {X : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
      (R : ResolvedChain T X) (e : X.C ⟶ E) :
    LiftedTriangle (sequence R e) (shiftComparison E) ((N E).triangle X R e)
      ((N' ((cdgaLift.{u,v,max v t} k).obj E)).triangle _ (resolved R)
        ((cdgaLift.{u,v,max v t} k).map e))
  naturality {X Y : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
      (f : ChainMap X Y) (R : ResolvedChain T X) (S : ResolvedChain T Y)
      (e : X.C ⟶ E) (c : Y.C ⟶ E) (he : e = f.c ≫ c)
      (l : Lift f R.resolution S.resolution) :
    let E' := (cdgaLift.{u,v,max v t} k).obj E
    let e' := (cdgaLift.{u,v,max v t} k).map e
    let c' := (cdgaLift.{u,v,max v t} k).map c
    letI := derivedCategoryInstance (oneObject E) (h E.toCommDGAlgebra)
    letI := derivedCategoryInstance (oneObject E') (h' E'.toCommDGAlgebra)
    letI := (K E).shiftD
    letI := (K' E').shiftD
    let l' := (resolution_eq R).symm ▸ (resolution_eq S).symm ▸
      (liftResolution R).lift (liftResolution S) l
    let m := (N E).strict.map l R.sequence S.sequence e c he
    let m' := (N' E').strict.map l' (resolved R).sequence (resolved S).sequence e' c' (liftFinalMap f he)
    LiftedSequenceNaturality (sequence R e) (sequence S c) m m' ∧
    (shiftComparison E).triangles.map ((N E).map f R S e c he) ≫ (triangle S c).iso.hom =
      (triangle R e).iso.hom ≫
        (N' E').map (liftChainMap.{u,v,t} f) (resolved R) (resolved S) e' c' (liftFinalMap f he)

/-- Transport the triangle on the cotangent models by conjugating the
comparison of the represented sequences with their model identifications. -/
def CommonBoundComparisons.identified
    {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    {h : ∀ A : CommDGAlgebra.{u,v} k, HomotopyCategoryLaws (dgCat A)}
    {h' : ∀ A : CommDGAlgebra.{u,max v t} k, HomotopyCategoryLaws (dgCat A)}
    {d : ∀ A : CommDGAlgebra.{u,v} k,
      Descent (h A) (h' (liftAlgebra.{u,v,t} A)) (liftInput.{u,v,t} A)}
    {K : ∀ E : NonpositiveCDGA.{u,v} k, ConeLocalization (oneObject E) (h E.toCommDGAlgebra)}
    {K' : ∀ E : NonpositiveCDGA.{u,max v t} k, ConeLocalization (oneObject E) (h' E.toCommDGAlgebra)}
    {N : ∀ E, Naturality (K E) T} {N' : ∀ E, Naturality (K' E) T'}
    (b : CommonBoundComparisons d K K' N N')
    {X : Chain.{u,v} k} (R : ResolvedChain T X) : Prop :=
  let F := cdgaLift.{u,v,max v t} k
  let C' := F.obj X.C
  letI := derivedCategoryInstance (oneObject X.C) (h X.C.toCommDGAlgebra)
  letI := derivedCategoryInstance (oneObject C') (h' C'.toCommDGAlgebra)
  letI := (K X.C).shiftD
  letI := (K' C').shiftD
  let J := (b.shiftComparison X.C).triangles
  let r (e : C' ⟶ C') := ((N' C').triangle _ (b.resolved R) e).triangle
  let a := eqToIso (congrArg r (F.map_id X.C))
  ∀ {U : Triangle (Derived.derivedCategory (oneObject X.C) (h X.C.toCommDGAlgebra))}
    {V : Triangle (Derived.derivedCategory (oneObject C') (h' C'.toCommDGAlgebra))}
    (i : ((N X.C).triangle X R (𝟙 X.C)).triangle ≅ U) (i' : r (𝟙 C') ≅ V),
    ∃ j : J.obj U ≅ V,
      j.hom = J.map i.inv ≫ (b.triangle R (𝟙 X.C)).iso.hom ≫ a.hom ≫ i'.hom

/-- Apply the construction at an arbitrary larger common level. The models at
that level represent the transported cotangent terms of any original resolutions.
The common-bound triangle and its comparisons are those of the same construction
applied to all chains and chain maps at that level. -/
def CommonBoundTransitivity : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k],
    ∃ (T : ModuleTensor.{u,v} k) (T' : ModuleTensor.{u,max v t} k)
      (h : ∀ A : CommDGAlgebra.{u,v} k, HomotopyCategoryLaws (dgCat A))
      (h' : ∀ A : CommDGAlgebra.{u,max v t} k, HomotopyCategoryLaws (dgCat A))
      (F : ∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B), ScalarExtension T f (h A) (h B))
      (F' : ∀ {A B : CommDGAlgebra.{u,max v t} k} (f : A ⟶ B), ScalarExtension T' f (h' A) (h' B))
      (d : ∀ A : CommDGAlgebra.{u,v} k,
        Descent (h A) (h' (liftAlgebra.{u,v,t} A)) (liftInput.{u,v,t} A))
      (K₀ : ∀ A : NonpositiveCDGA.{u,v} k, ConeLocalization (oneObject A) (h A.toCommDGAlgebra))
      (N₀ : ∀ A : NonpositiveCDGA.{u,v} k, Naturality (K₀ A) T)
      (K : ∀ A : NonpositiveCDGA.{u,max v t} k, ConeLocalization (oneObject A) (h' A.toCommDGAlgebra))
      (N : ∀ A : NonpositiveCDGA.{u,max v t} k, Naturality (K A) T')
      (b : CommonBoundComparisons d K₀ K N₀ N),
      (∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B),
        ExtensionTransport (h A) (h B) (h' (liftAlgebra.{u,v,t} A)) (h' (liftAlgebra.{u,v,t} B))
          (F f) (F' (DerivedTensor.liftAlgebraMap.{u,v,t} f)) (d A) (d B)) ∧
      ∀ X : Chain.{u,v} k,
        let Y := liftChain.{u,v,t} X
        Nonempty (ResolvedChain T X) ∧
        ∀ R : ResolvedChain T X,
          let S := b.resolved R
          IdentifiesCotangentTriangle (K₀ X.C) (F (underlying X.second)) R
            ((N₀ X.C).triangle X R (𝟙 X.C)) ∧
          IdentifiesCotangentTriangle (K Y.C) (F' (underlying Y.second)) S
            ((N Y.C).triangle Y S (𝟙 Y.C)) ∧
          b.identified R ∧
          ∀ R' : ResolvedChain T X,
            CommonBoundTerms.{u,v,t} d (F (underlying X.second)) (F' (underlying Y.second)) R' S

end Coefficients

end
end Specs.DerivedFormalization.Affine.CotangentTransitivity
