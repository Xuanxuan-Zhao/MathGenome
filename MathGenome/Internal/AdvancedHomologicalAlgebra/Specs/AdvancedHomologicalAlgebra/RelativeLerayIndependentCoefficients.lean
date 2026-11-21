import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.RelativeLeray
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.LerayIndependentCoefficients

/-! Relative Leray for maps with independent site, section-ring, and coefficient
universes. The diagram is carried back to the original site and ring of the
target. At index `k`, the diagram uses page `k + 2` and coordinates `(p, p + q)`. -/

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
set_option linter.style.haveILetI false
set_option quotPrecheck false
set_option maxHeartbeats 1000000

universe a m u v w r s t

namespace AdvancedHomologicalAlgebra.RelativeLerayIndependentCoefficients

open SheafUniverseTransport HigherDirectImagesOriginalTheory OriginalDerivedSectionsTheory
open GrothendieckSpectralSequence GrothendieckEdges HypercohomologyDerivedNaturality
open LerayIndependentCoefficients
  (changeCoefficients changeGradedIso stalkCoordinates degreeZeroComplex originalDegreeZeroIso)
open FiniteFiltrationConvergence
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients

attribute [local instance] HasDerivedCategory.standard

section Row

variable {B₀ C₀ : Type*} [Category* B₀] [Category* C₀] [Abelian B₀] [Abelian C₀]

/-- The cokernel of the transition between two consecutive filtration steps. -/
def gradedEval (p n : ℤ) : RowDiagram C₀ ⥤ C₀ where
  obj U := cokernel (U.down p n)
  map h := cokernel.map _ _ (h.step (p + 1) n) (h.step p n) (h.down_comm p n).symm
  map_id U := by
    apply (cancel_epi (cokernel.π (U.down p n))).1
    change cokernel.π (U.down p n) ≫ cokernel.map (U.down p n) (U.down p n)
      (𝟙 _) (𝟙 _) (by simp) = _
    simp only [cokernel.map, cokernel.π_desc, Category.id_comp, Category.comp_id]
  map_comp {U V W} h j := by
    apply (cancel_epi (cokernel.π (U.down p n))).1
    simp only [cokernel.map, Category.assoc, cokernel.π_desc, cokernel.π_desc_assoc] <;>
      exact Category.assoc _ _ _

/-- Carry the representative-normalized limit comparison out of the actual
Cartan–Eilenberg row model using its simultaneous diagram isomorphism. -/
def rowGradedIso [EnoughInjectives B₀] (H : B₀ ⥤ C₀) [H.Additive] (U : DerivedRow H)
    (W : DerivedCategory.Plus B₀) (k : ℕ) (p n : ℤ)
    (e : LimitIso (modelData H U W).filtration (modelData H U W).pages ((k : ℤ) + 2) p n) :
    (U.derived.obj W).page k p n ≅ cokernel ((U.derived.obj W).down p n) :=
  (pageEval k p n).mapIso (modelIso H U W) ≪≫ e.iso ≪≫
    ((gradedEval p n).mapIso (modelIso H U W)).symm

end Row

variable {X : TopCat.{u}} {Y : TopCat.{v}} {Z : TopCat.{w}}
  {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} {T : Z.Sheaf RingCat.{t}}
  (f : RingedMap R S) (g : RingedMap S T)

/-- Composition on the original inverse-image opens and original section rings. -/
def composite : RingedMap R T where
  continuousMap := g.continuousMap.comp f.continuousMap
  scalars V := (f.scalars ((inverseOpens g.continuousMap).op.obj V)).comp (g.scalars V)
  naturality {V W} i := by
    ext c
    change R.obj.map ((inverseOpens f.continuousMap).op.map
      ((inverseOpens g.continuousMap).op.map i)) (f.scalars _ (g.scalars V c)) =
      f.scalars _ (g.scalars W (T.obj.map i c))
    have hf := DFunLike.congr_fun
      (f.naturality ((inverseOpens g.continuousMap).op.map i)) (g.scalars V c)
    have hg := DFunLike.congr_fun (g.naturality i) c
    exact hf.trans (congrArg (f.scalars ((inverseOpens g.continuousMap).op.obj W)) hg)

/-- The underived comparison is the identity linear map on each original open. -/
def underivedComposition : directImageValue.{m} f ⋙ directImageValue.{m} g ≅
    directImageValue.{m} (composite f g) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget T).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        let P := ((directImageValue.{m} f ⋙ directImageValue.{m} g).obj M).val.obj V
        let Q := ((directImageValue.{m} (composite f g)).obj M).val.obj V
        let e : (P : Type m) ≃ₗ[T.obj.obj V] (Q : Type m) :=
          { toAddEquiv := AddEquiv.refl _, map_smul' := fun _ _ ↦ rfl }
        e.toModuleIso)
        (fun {_ _} _ ↦ by ext x; rfl)))
    (by intros; ext V x; rfl)

/-- The composition comparison evaluates to the identity on sections, before
any change of coefficient universe. The scalar actions already agree by
composition of the two original ring maps. -/
theorem underivedComposition_sections (M : SheafOfModules.{m} R) (V : Opens Z)
    (x : M.val.obj (op (invOpen f (invOpen g V)))) :
    ((underivedComposition.{m} f g).hom.app M).val.app (op V) x = x := rfl

set_option hygiene false in
local notation "A" => AmbientSheaves.{max a m v w s t} R
set_option hygiene false in
local notation "B" => AmbientSheaves.{max a m u w r t} S
set_option hygiene false in
local notation "C" => AmbientSheaves.{max a m u v r s} T
set_option hygiene false in
local notation "F" => ambientDirectImage.{max a m w t} f
set_option hygiene false in
local notation "G" => ambientDirectImage.{max a m u r} g
set_option hygiene false in
local notation "D" => ambientDirectImage.{max a m v s} (composite f g)
set_option hygiene false in
local notation "R'" => liftedRing.{max a m v w s t} R
set_option hygiene false in
local notation "S'" => liftedRing.{max a m u w r t} S
set_option hygiene false in
local notation "T'" => liftedRing.{max a m u v r s} T
set_option hygiene false in
local notation "A'" => SheafTheory.Modules R'
set_option hygiene false in
local notation "B'" => SheafTheory.Modules S'
set_option hygiene false in
local notation "C'" => SheafTheory.Modules T'
set_option hygiene false in
local notation "F'" => transportedDirectImage.{max a m w t} f
set_option hygiene false in
local notation "G'" => transportedDirectImage.{max a m u r} g
set_option hygiene false in
local notation "D'" => transportedDirectImage.{max a m v s} (composite f g)
set_option hygiene false in
local notation "JX" => transport.{max a m v w s t} R
set_option hygiene false in
local notation "JY" => transport.{max a m u w r t} S
set_option hygiene false in
local notation "JZ" => transport.{max a m u v r s} T
set_option hygiene false in
local notation "f'" => transportedMap.{max a m w t} f
set_option hygiene false in
local notation "g'" => transportedMap.{max a m u r} g
set_option hygiene false in
local notation "φ'" => transportedScalars.{max a m w t} f
set_option hygiene false in
local notation "ψ'" => transportedScalars.{max a m u r} g
set_option hygiene false in
local notation "Lifts" => liftSheafCoefficients.{max a u v w r s t,u,r,m} R

variable
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a m u v w r s t}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a m u v w r s t}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max a m u v w r s t}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max a m u v w r s t}]
  [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{max a m u v w r s t}]
  [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{max a m u v w r s t}]
  [EnoughInjectives A] [EnoughInjectives B]
  [(JX).IsEquivalence] [(JY).IsEquivalence] [(JZ).IsEquivalence]

/-- The same underived comparison on the common ambient category. -/
abbrev originalUnderived := underivedComposition.{max a m u v w r s t} f g

/-- The comparison of the derived images of the original composite. -/
def originalDerivedComposition : (F ⋙ G).rightDerivedFunctorPlus ≅ (D).rightDerivedFunctorPlus where
  hom := (originalUnderived.{a,m} f g).hom.rightDerivedFunctorPlus
  inv := (originalUnderived.{a,m} f g).inv.rightDerivedFunctorPlus
  hom_inv_id := by rw [← NatTrans.rightDerivedFunctorPlus_comp, Iso.hom_inv_id,
    NatTrans.rightDerivedFunctorPlus_id]
  inv_hom_id := by rw [← NatTrans.rightDerivedFunctorPlus_comp, Iso.inv_hom_id,
    NatTrans.rightDerivedFunctorPlus_id]

/-- HA-R12 after identifying the original underived composite. -/
def originalCompositionMap : (D).rightDerivedFunctorPlus ⟶
    (F).rightDerivedFunctorPlus ⋙ (G).rightDerivedFunctorPlus :=
  (originalDerivedComposition.{a,m} f g).inv ≫
    Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F G

abbrev firstSquare (f : RingedMap R S) (_ : RingedMap S T) := pushforwardTransportExpected.{max a m w t,u,v,r,s} f
abbrev secondSquare (_ : RingedMap R S) (g : RingedMap S T) := pushforwardTransportExpected.{max a m u r,v,w,s,t} g
abbrev compositeSquare := pushforwardTransportExpected.{max a m v s,u,w,r,t} (composite f g)

abbrev RaisedLeray := RelativeLeray.Data R' S' T' f' g' φ' ψ'

/-- Simultaneous change of sites on the actual derived pushforwards. The
transport of the composite agrees with the two given maps on the original
sections before localization. -/
structure SiteComparison where
  source : ExactDescent JX
  middle : ExactDescent JY
  target : ExactDescent JZ
  first : UnitTransport F F' JX JY (firstSquare.{a,m} f g) source middle
    (F).rightDerivedFunctorPlusUnit (F').rightDerivedFunctorPlusUnit
  second : UnitTransport G G' JY JZ (secondSquare.{a,m} f g) middle target
    (G).rightDerivedFunctorPlusUnit (G').rightDerivedFunctorPlusUnit
  composed : UnitTransport (F ⋙ G) (F' ⋙ G') JX JZ
    (composeFunctorSquares (firstSquare.{a,m} f g) (secondSquare.{a,m} f g)) source target
    (F ⋙ G).rightDerivedFunctorPlusUnit (F' ⋙ G').rightDerivedFunctorPlusUnit
  underived : isoWhiskerRight (originalUnderived.{a,m} f g) JZ ≪≫
      compositeSquare.{a,m} f g =
    composeFunctorSquares (firstSquare.{a,m} f g) (secondSquare.{a,m} f g) ≪≫
      isoWhiskerLeft JX (RelativeLeray.underivedCompositionIso R' S' T' f' g' φ' ψ')
  derived : ∀ K : DerivedCategory.Plus A,
    target.functor.map ((Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F G).app K) ≫
        (composeFunctorSquares first.iso second.iso).hom.app K =
      composed.iso.hom.app K ≫
        (Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F' G').app
          (source.functor.obj K)

/-- Transport the derived composite using the very same underived comparison
at both sites. -/
def SiteComparison.compositeIso (d : SiteComparison.{a,m} f g) :
    (D).rightDerivedFunctorPlus ⋙ d.target.functor ≅ d.source.functor ⋙ (D').rightDerivedFunctorPlus :=
  isoWhiskerRight (originalDerivedComposition.{a,m} f g).symm d.target.functor ≪≫
    d.composed.iso ≪≫ isoWhiskerLeft d.source.functor
      (RelativeLeray.derivedPushforwardIso R' S' T' f' g' φ' ψ')

variable (L : RaisedLeray.{a,m} f g) (d : SiteComparison.{a,m} f g)

local notation "Lower" => (JZ).asEquivalence.inverse
local instance lowerAdditive {M N : Type*} [Category* M] [Category* N]
    [Preadditive M] [Preadditive N] (J : M ⥤ N) [J.IsEquivalence] [J.Additive] :
    J.asEquivalence.inverse.Additive := by
  letI : J.asEquivalence.functor.Additive := inferInstanceAs (J.Additive)
  exact Equivalence.inverse_additive _

local notation "QX" => DerivedCategory.Plus.singleFunctor A 0
local notation "QX'" => DerivedCategory.Plus.singleFunctor A' 0
local notation "HZ" => DerivedCategory.Plus.homologyFunctor C
local notation "HZ'" => DerivedCategory.Plus.homologyFunctor C'
set_option hygiene false in
local notation "Raised" => GrothendieckSpectralSequence.sequence F' G' L.package.row

/-- Lower an isomorphism of functors through the target-site equivalence. -/
def lowerIso {M N P : Type*} [Category* M] [Category* N] [Category* P]
    {J : N ⥤ P} [J.IsEquivalence] {U : M ⥤ N} {V : M ⥤ P}
    (e : U ⋙ J ≅ V) : V ⋙ J.asEquivalence.inverse ≅ U :=
  isoWhiskerRight e.symm _ ≪≫ associator .. ≪≫
    isoWhiskerLeft U J.asEquivalence.unitIso.symm ≪≫ rightUnitor U

/-- The same spectral sequence with values in modules over the original ring
sheaf on Z, functorial in the original bounded-below derived object. -/
def derivedSequence : DerivedCategory.Plus A ⥤ RowDiagram C :=
  d.source.functor ⋙ Raised ⋙ changeCoefficients Lower

/-- Placement of any original coefficient complex, including very small
carriers for which no derived category instance is needed. -/
def complexPlacement (_ : RingedMap R S) (_ : RingedMap S T) : CochainComplex.Plus (SheafOfModules.{m} R) ⥤ DerivedCategory.Plus A :=
  (Lifts).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q

abbrev complexSequence :=
  complexPlacement.{a,m} f g ⋙ derivedSequence.{a,m} f g L d

abbrev sheafPlacement (_ : RingedMap R S) (_ : RingedMap S T) : SheafOfModules.{m} R ⥤ DerivedCategory.Plus A := Lifts ⋙ QX

abbrev raisedSheafInput (_ : RingedMap R S) (_ : RingedMap S T) : SheafOfModules.{m} R ⥤ A' := Lifts ⋙ JX

def sheafInputComparison :
    raisedSheafInput.{a,m} f g ⋙ QX' ≅ sheafPlacement.{a,m} f g ⋙ d.source.functor :=
  isoWhiskerLeft Lifts (stalkCoordinates JX d.source)

/-- The sheaf sequence is HA-G05's specialization of the same diagram. -/
def sheafSequence : SheafOfModules.{m} R ⥤ RowDiagram C :=
  raisedSheafInput.{a,m} f g ⋙ objectSequence F' G' L.package ⋙ changeCoefficients Lower

def sheafSequenceComparison :
    sheafSequence.{a,m} f g L ≅ sheafPlacement.{a,m} f g ⋙ derivedSequence.{a,m} f g L d :=
  isoWhiskerRight (sheafInputComparison.{a,m} f g d) (Raised ⋙ changeCoefficients Lower)

/-- The specialization is obtained from the actual degree-zero complex before
raising the coefficient carriers. -/
def degreeZeroSequenceIso :
    letI : HasZeroObject (SheafOfModules.{m} R) := hasZeroObject_of_hasTerminal_object
    degreeZeroComplex (SheafOfModules.{m} R) ⋙ complexSequence.{a,m} f g L d ≅
      sheafSequence.{a,m} f g L := by
  letI : HasZeroObject (SheafOfModules.{m} R) := hasZeroObject_of_hasTerminal_object
  exact (associator ..).symm ≪≫
    isoWhiskerRight (originalDegreeZeroIso.{max a w t,m,u,v,r,s} (R := R))
      (derivedSequence.{a,m} f g L d) ≪≫
    (sheafSequenceComparison.{a,m} f g L d).symm

abbrev derivedSecondIso (p : ℕ) (q : ℤ) :
    derivedSequence.{a,m} f g L d ⋙ pageEval 0 p ((p : ℤ) + q) ≅ secondValue F G p q :=
  isoWhiskerRight (isoWhiskerLeft d.source.functor (L.secondIso p q)) Lower ≪≫
    lowerIso (composeFunctorSquares d.first.iso
      (composeFunctorSquares (d.middle.cohomology q).symm
        (composeFunctorSquares (stalkCoordinates JY d.middle).symm
          (composeFunctorSquares d.second.iso (d.target.cohomology p).symm))))

abbrev targetValue (n : ℤ) := (D).rightDerivedFunctorPlus ⋙ HZ n

def targetCoordinates (n : ℤ) :
    d.source.functor ⋙ ((D').rightDerivedFunctorPlus ⋙ HZ' n) ⋙ Lower ≅ targetValue.{a,m} f g n :=
  lowerIso (composeFunctorSquares (d.compositeIso f g) (d.target.cohomology n).symm)

def targetIso (n : ℤ) :
    derivedSequence.{a,m} f g L d ⋙ targetEval n ≅ targetValue.{a,m} f g n :=
  isoWhiskerRight (isoWhiskerLeft d.source.functor (L.targetIso n)) Lower ≪≫
    targetCoordinates.{a,m} f g d n

/-- The abutment in the original iterated-derived coordinates, before using
the canonical composition isomorphism. -/
def iteratedTargetIso (n : ℤ) :
    derivedSequence.{a,m} f g L d ⋙ targetEval n ≅ iteratedValue F G n :=
  isoWhiskerRight (isoWhiskerLeft d.source.functor (L.package.iteratedIso n)) Lower ≪≫
    lowerIso (composeFunctorSquares (composeFunctorSquares d.first.iso d.second.iso)
      (d.target.cohomology n).symm)

abbrev sheafSecondValue (p q : ℕ) := Lifts ⋙ rightValue F q ⋙ rightValue G p
set_option hygiene false in
local notation "LiftY" => liftSheafCoefficients.{max a u v w r s t,v,s,m} S

abbrev rowValue (n : ℕ) := directImageValue.{m} f ⋙ LiftY ⋙ rightValue G n

/-- Comparison for the composition of a sheaf embedding with a classical
higher direct image. -/
def higherCoordinate (n : ℕ) :
    rightValue F n ⋙ JY ≅ JX ⋙ rightValue F' n :=
  composeFunctorSquares (stalkCoordinates JX d.source).symm
    (composeFunctorSquares d.first.iso (d.middle.cohomology n).symm)

def outerHigherCoordinate (n : ℕ) :
    rightValue G n ⋙ JZ ≅ JY ⋙ rightValue G' n :=
  composeFunctorSquares (stalkCoordinates JY d.middle).symm
    (composeFunctorSquares d.second.iso (d.target.cohomology n).symm)

/-- The degree-zero specialization of the derived second-page identification,
on the HA-G05 object sequence. -/
def sheafSecondIso (p q : ℕ) :
    sheafSequence.{a,m} f g L ⋙ pageEval 0 p ((p : ℤ) + q) ≅
      sheafSecondValue.{a,m} f g p q :=
  isoWhiskerRight (sheafSequenceComparison.{a,m} f g L d)
    (pageEval 0 p ((p : ℤ) + q)) ≪≫
  isoWhiskerLeft (sheafPlacement.{a,m} f g) (derivedSecondIso.{a,m} f g L d p q)

def rowCoordinate (n : ℕ) :
    raisedSheafInput.{a,m} f g ⋙ F' ⋙ rightValue G' n ⋙ Lower ≅ rowValue.{a,m} f g n :=
  isoWhiskerLeft Lifts
    (lowerIso (composeFunctorSquares (firstSquare.{a,m} f g) (outerHigherCoordinate.{a,m} f g d n))) ≪≫
    (associator ..).symm ≪≫ isoWhiskerRight (coefficientLiftComparisonExpected.{max a u v w r s t,m,u,v,r,s} f).symm
      (rightValue G n) ≪≫ associator ..

def columnCoordinate (n : ℕ) :
    raisedSheafInput.{a,m} f g ⋙ rightValue F' n ⋙ G' ⋙ Lower ≅
      Lifts ⋙ rightValue F n ⋙ G :=
  isoWhiskerLeft Lifts
    (lowerIso (composeFunctorSquares (higherCoordinate.{a,m} f g d n) (secondSquare.{a,m} f g)))

/-- The relative abutment comparison on the original coefficient sheaf. -/
def sheafTargetCoordinate (n : ℕ) :
    raisedSheafInput.{a,m} f g ⋙ rightValue D' n ⋙ Lower ≅ Lifts ⋙ rightValue D n :=
  isoWhiskerLeft Lifts (lowerIso
    (composeFunctorSquares (stalkCoordinates JX d.source).symm
      (composeFunctorSquares (d.compositeIso f g) (d.target.cohomology n).symm)))

def sheafTargetIso (n : ℕ) :
    sheafSequence.{a,m} f g L ⋙ targetEval (n : ℤ) ≅ Lifts ⋙ rightValue D n :=
  isoWhiskerRight (isoWhiskerLeft (raisedSheafInput.{a,m} f g) (L.sheafTargetIso n)) Lower ≪≫
    sheafTargetCoordinate.{a,m} f g d n

def rowPage (n : ℕ) :
    sheafSequence.{a,m} f g L ⋙ pageEval 0 n n ≅ rowValue.{a,m} f g n :=
  isoWhiskerRight (isoWhiskerLeft (raisedSheafInput.{a,m} f g) (L.edges.rowPage n)) Lower ≪≫
    rowCoordinate.{a,m} f g d n

def columnPage (n : ℕ) :
    sheafSequence.{a,m} f g L ⋙ pageEval 0 0 n ≅ Lifts ⋙ rightValue F n ⋙ G :=
  isoWhiskerRight (isoWhiskerLeft (raisedSheafInput.{a,m} f g) (L.edges.columnPage n)) Lower ≪≫
    columnCoordinate.{a,m} f g d n

def rowEdge (n : ℕ) : rowValue.{a,m} f g n ⟶ Lifts ⋙ rightValue D n :=
  (rowCoordinate.{a,m} f g d n).inv ≫
    whiskerRight (whiskerLeft (raisedSheafInput.{a,m} f g) (L.rowEdge n)) Lower ≫
    (sheafTargetCoordinate.{a,m} f g d n).hom

def columnEdge (n : ℕ) : Lifts ⋙ rightValue D n ⟶ Lifts ⋙ rightValue F n ⋙ G :=
  (sheafTargetCoordinate.{a,m} f g d n).inv ≫
    whiskerRight (whiskerLeft (raisedSheafInput.{a,m} f g) (L.columnEdge n)) Lower ≫
    (columnCoordinate.{a,m} f g d n).hom

abbrev diagram (K : DerivedCategory.Plus A) :=
  (derivedSequence.{a,m} f g L d).obj K

private theorem diagramInclusionMono (K : DerivedCategory.Plus A) (p n : ℤ) :
    Mono ((diagram.{a,m} f g L d K).inclusion p n) := by
  letI := L.package.inclusion_mono (d.source.functor.obj K) p n
  exact inferInstanceAs (Mono ((Lower).map
    (((Raised).obj (d.source.functor.obj K)).inclusion p n)))

def filtration (K : DerivedCategory.Plus A) (p n : ℤ) :
    Subobject ((targetValue.{a,m} f g n).obj K) := by
  letI := diagramInclusionMono.{a,m} f g L d K p n
  exact Subobject.mk ((diagram.{a,m} f g L d K).inclusion p n ≫
    (targetIso.{a,m} f g L d n).hom.app K)

set_option hygiene false in
local notation "Diag" => diagram.{a,m} f g L d
set_option hygiene false in
local notation "Fil" => filtration.{a,m} f g L d

/-- Present the filtration subobject in the actual composite cohomology by
the corresponding step of the lowered diagram. -/
def filtrationStepIso (K : DerivedCategory.Plus A) (p n : ℤ) :
    (Diag K).step p n ≅ (Fil K p n : C) := by
  letI := diagramInclusionMono.{a,m} f g L d K p n
  exact (Subobject.underlyingIso
    ((Diag K).inclusion p n ≫ (targetIso.{a,m} f g L d n).hom.app K)).symm

@[reassoc]
theorem filtrationStepIso_arrow (K : DerivedCategory.Plus A) (p n : ℤ) :
    (filtrationStepIso.{a,m} f g L d K p n).hom ≫ (Fil K p n).arrow =
      (Diag K).inclusion p n ≫ (targetIso.{a,m} f g L d n).hom.app K := by
  letI := diagramInclusionMono.{a,m} f g L d K p n
  exact Subobject.underlyingIso_arrow _

/-- The map on a filtration step, in its subobject presentation. -/
def filtrationStepMap {K K' : DerivedCategory.Plus A} (h : K ⟶ K') (p n : ℤ) :
    (Fil K p n : C) ⟶ (Fil K' p n : C) :=
  (filtrationStepIso.{a,m} f g L d K p n).inv ≫
    ((derivedSequence.{a,m} f g L d).map h).step p n ≫
    (filtrationStepIso.{a,m} f g L d K' p n).hom

@[reassoc]
theorem filtrationStepMap_arrow {K K' : DerivedCategory.Plus A} (h : K ⟶ K') (p n : ℤ) :
    filtrationStepMap.{a,m} f g L d h p n ≫ (Fil K' p n).arrow =
      (Fil K p n).arrow ≫ (targetValue.{a,m} f g n).map h := by
  let U := derivedSequence.{a,m} f g L d
  apply (cancel_epi (filtrationStepIso.{a,m} f g L d K p n).hom).1
  simp only [filtrationStepMap, Category.assoc, Iso.hom_inv_id_assoc,
    filtrationStepIso_arrow, filtrationStepIso_arrow_assoc]
  rw [← Category.assoc ((U.map h).step p n), (U.map h).inclusion_comm, Category.assoc]
  exact congrArg ((Diag K).inclusion p n ≫ ·)
    ((targetIso.{a,m} f g L d n).hom.naturality h)

/-- The quotient map induced by a morphism on the actual filtered abutment. -/
def filtrationQuotientMap {K K' : DerivedCategory.Plus A} (h : K ⟶ K') (p n : ℤ)
    (hk : Fil K (p + 1) n ≤ Fil K p n) (hk' : Fil K' (p + 1) n ≤ Fil K' p n) :
    cokernel (Subobject.ofLE _ _ hk) ⟶ cokernel (Subobject.ofLE _ _ hk') :=
  cokernel.map _ _ (filtrationStepMap.{a,m} f g L d h (p + 1) n)
    (filtrationStepMap.{a,m} f g L d h p n) (by
      apply Subobject.eq_of_comp_arrow_eq
      simp only [Category.assoc, filtrationStepMap_arrow, filtrationStepMap_arrow_assoc,
        Subobject.ofLE_arrow, Subobject.ofLE_arrow_assoc])

/-- Identify the diagram cokernel with the quotient of the two subobjects
of the original derived target. -/
def filtrationQuotientIso (K : DerivedCategory.Plus A) (p n : ℤ)
    (h : Fil K (p + 1) n ≤ Fil K p n) :
    cokernel ((Diag K).down p n) ≅ cokernel (Subobject.ofLE _ _ h) :=
  cokernel.mapIso _ _ (filtrationStepIso.{a,m} f g L d K (p + 1) n)
    (filtrationStepIso.{a,m} f g L d K p n) (by
      apply Subobject.eq_of_comp_arrow_eq
      simp only [Category.assoc, Subobject.ofLE_arrow, filtrationStepIso_arrow,
        filtrationStepIso_arrow_assoc]
      rw [← Category.assoc ((Diag K).down p n)]
      congr 1
      change (Lower).map _ ≫ (Lower).map _ = (Lower).map _
      rw [← Functor.map_comp, L.package.down_inclusion])

/-- The input of the actual row sequence on the raised middle site. -/
abbrev rowInput (K : DerivedCategory.Plus A) :=
  (F').rightDerivedFunctorPlus.obj (d.source.functor.obj K)

abbrev relativeRowModel (K : DerivedCategory.Plus A) :=
  modelData G' L.package.row (rowInput.{a,m} f g d K)

/-- A late-page comparison on the actual row model, normalized on closed
representatives via `LimitIso.representative_formula`. -/
abbrev RowLimit (K : DerivedCategory.Plus A) (k : ℕ) (p n : ℤ) :=
  LimitIso (relativeRowModel.{a,m} f g L d K).filtration
    (relativeRowModel.{a,m} f g L d K).pages ((k : ℤ) + 2) p n

/-- The limiting comparison in the original target sheaf category. -/
def gradedComparison (K : DerivedCategory.Plus A) (k : ℕ) (p n : ℤ)
    (h : Fil K (p + 1) n ≤ Fil K p n) (e : RowLimit.{a,m} f g L d K k p n) :
    (Diag K).page k p n ≅ cokernel (Subobject.ofLE _ _ h) :=
  changeGradedIso Lower ((Raised).obj (d.source.functor.obj K)) k p n
    (rowGradedIso G' L.package.row (rowInput.{a,m} f g d K) k p n e) ≪≫
  filtrationQuotientIso.{a,m} f g L d K p n h

structure Comparison : Prop where
  composition_isIso : IsIso (originalCompositionMap.{a,m} f g)
  composition_transport : ∀ K : DerivedCategory.Plus A,
    d.target.functor.map ((originalCompositionMap.{a,m} f g).app K) ≫
        (composeFunctorSquares d.first.iso d.second.iso).hom.app K =
      (d.compositeIso f g).hom.app K ≫
        (RelativeLeray.compositionMap R' S' T' f' g' φ' ψ').app (d.source.functor.obj K)
  target_canonical : ∀ n : ℤ, letI := composition_isIso
    targetIso.{a,m} f g L d n = iteratedTargetIso.{a,m} f g L d n ≪≫
      isoWhiskerRight (asIso (originalCompositionMap.{a,m} f g)).symm (HZ n)
  sheaf_target : ∀ n : ℕ,
    sheafTargetIso.{a,m} f g L d n =
      isoWhiskerRight (sheafSequenceComparison.{a,m} f g L d) (targetEval (n : ℤ)) ≪≫
      isoWhiskerLeft (sheafPlacement.{a,m} f g) (targetIso.{a,m} f g L d n)
  negative_columns : ∀ (K : DerivedCategory.Plus A) (k : ℕ) (p n : ℤ),
    p < 0 → IsZero ((diagram.{a,m} f g L d K).page k p n)
  decreasing : ∀ (K : DerivedCategory.Plus A) (p n : ℤ),
    filtration.{a,m} f g L d K (p + 1) n ≤ filtration.{a,m} f g L d K p n
  finite : ∀ (K : DerivedCategory.Plus A) (n : ℤ),
    letI : OrderBot (Subobject ((targetValue.{a,m} f g n).obj K)) := Subobject.orderBot
    ∃ lo hi : ℤ, (∀ p, p ≤ lo → filtration.{a,m} f g L d K p n = ⊤) ∧
      (∀ p, hi ≤ p → filtration.{a,m} f g L d K p n = ⊥)
  filtered_natural : ∀ {K K' : DerivedCategory.Plus A} (h : K ⟶ K') (p n : ℤ),
    (filtration.{a,m} f g L d K' p n).Factors
      ((filtration.{a,m} f g L d K p n).arrow ≫ (targetValue.{a,m} f g n).map h)
  graded : ∀ (K : DerivedCategory.Plus A) (n : ℤ), ∃ N : ℕ,
    ∀ k : ℕ, N ≤ k → ∀ p : ℤ, (diagram.{a,m} f g L d K).differential k p n = 0 ∧
      Nonempty (RowLimit.{a,m} f g L d K k p n)
  graded_representatives : ∀ (K : DerivedCategory.Plus A) (k : ℕ) (p n : ℤ)
      (e : RowLimit.{a,m} f g L d K k p n),
    let M := relativeRowModel.{a,m} f g L d K
    let i := modelIso G' L.package.row (rowInput.{a,m} f g d K)
    (Lower).map (closedToPage M.filtration M.pages ((k : ℤ) + 2) p n) ≫
        (Lower).map (i.inv.page k p n) ≫
        (gradedComparison.{a,m} f g L d K k p n (decreasing K p n) e).hom =
      (Lower).map (closedClass M.filtration p n) ≫ (Lower).map (i.inv.step p n) ≫
        (filtrationStepIso.{a,m} f g L d K p n).hom ≫
        cokernel.π (Subobject.ofLE _ _ (decreasing K p n))
  graded_natural : ∀ {K K' : DerivedCategory.Plus A} (h : K ⟶ K') (n : ℤ),
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ (p : ℤ)
      (e : RowLimit.{a,m} f g L d K k p n) (e' : RowLimit.{a,m} f g L d K' k p n),
      ((derivedSequence.{a,m} f g L d).map h).page k p n ≫
          (gradedComparison.{a,m} f g L d K' k p n (decreasing K' p n) e').hom =
        (gradedComparison.{a,m} f g L d K k p n (decreasing K p n) e).hom ≫
          filtrationQuotientMap.{a,m} f g L d h p n (decreasing K p n) (decreasing K' p n)
  sheaf_quadrant : ∀ (M : SheafOfModules.{m} R) (k : ℕ) (p n : ℤ),
    p < 0 ∨ n < p → IsZero (((sheafSequence.{a,m} f g L).obj M).page k p n)
  row_comparison : ∀ (M : SheafOfModules.{m} R) (n : ℕ),
    (rowPage.{a,m} f g L d n).hom.app M ≫ (rowEdge.{a,m} f g L d n).app M =
      (Lower).map ((L.edges.filtered ((raisedSheafInput.{a,m} f g).obj M)).row n) ≫
        (sheafTargetIso.{a,m} f g L d n).hom.app M
  column_comparison : ∀ (M : SheafOfModules.{m} R) (n : ℕ),
    (sheafTargetIso.{a,m} f g L d n).hom.app M ≫ (columnEdge.{a,m} f g L d n).app M =
      (Lower).map ((L.edges.filtered ((raisedSheafInput.{a,m} f g).obj M)).column n) ≫
        (columnPage.{a,m} f g L d n).hom.app M

end AdvancedHomologicalAlgebra.RelativeLerayIndependentCoefficients

namespace Specs.AdvancedHomologicalAlgebra.RelativeLerayIndependentCoefficients

open _root_.AdvancedHomologicalAlgebra.RelativeLerayIndependentCoefficients
open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport
open _root_.AdvancedHomologicalAlgebra.HigherDirectImagesOriginalTheory
open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open _root_.Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison

attribute [local instance] HasDerivedCategory.standard

/-- Relative Leray and its sheaf edges, on three original ringed spaces with
independent carriers and for arbitrary original bounded-below complexes. -/
def relativeLerayType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {Z : TopCat.{w}}
    {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} {T : Z.Sheaf RingCat.{t}}
    (f : RingedMap R S) (g : RingedMap S T),
    letI := sectionHasSheafify.{max a m v w r s t,u} X
    letI := sectionWEqualsLocallyBijective.{max a m v w r s t,u} X
    letI := sectionHasSheafify.{max a m u w r s t,v} Y
    letI := sectionWEqualsLocallyBijective.{max a m u w r s t,v} Y
    letI := sectionHasSheafify.{max a m u v r s t,w} Z
    letI := sectionWEqualsLocallyBijective.{max a m u v r s t,w} Z
    ∃ (hX : EnoughInjectives (AmbientSheaves.{max a m v w s t} R))
      (hY : EnoughInjectives (AmbientSheaves.{max a m u w r t} S))
      (eX : (transport.{max a m v w s t} R).IsEquivalence)
      (eY : (transport.{max a m u w r t} S).IsEquivalence)
      (eZ : (transport.{max a m u v r s} T).IsEquivalence),
      letI := hX
      letI := hY
      letI := eX
      letI := eY
      letI := eZ
      (∀ (I : AmbientSheaves.{max a m v w s t} R), Injective I →
        rightAcyclicValue (ambientDirectImage.{max a m u r} g)
          ((ambientDirectImage.{max a m w t} f).obj I)) ∧
      ∃ (L : RaisedLeray.{a,m} f g) (d : SiteComparison.{a,m} f g),
        Comparison.{a,m} f g L d

end Specs.AdvancedHomologicalAlgebra.RelativeLerayIndependentCoefficients
