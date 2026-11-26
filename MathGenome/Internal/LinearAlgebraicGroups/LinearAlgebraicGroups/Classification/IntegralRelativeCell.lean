import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRelativeCell
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.TensorProduct.MvPolynomial

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Classification.IntegralRelativeCell

open _root_.LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open Specs.IntegralRelativeCell Specs.IntegralCentralQuotient
open Specs.Pinning (BasedRootDatum)
open Specs.OrderedRootProducts (Enumerates)

noncomputable section

section CellGeometry

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}}

/-- Change from pair coordinates to quotient and denominator coordinates. -/
private def divisionIso (G : Grp (Over S)) : G.X ⊗ G.X ≅ G.X ⊗ G.X where
  hom := lift (fst G.X G.X * (snd G.X G.X)⁻¹) (snd G.X G.X)
  inv := lift (fst G.X G.X * snd G.X G.X) (snd G.X G.X)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.comp_mul]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.comp_mul, GrpObj.comp_inv]

private theorem overProduct_isPullback (X Y : Over S) :
    IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
  Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct X Y)

private theorem whiskerRight_open {X Y : Over S} (f : X ⟶ Y) (Z : Over S)
    [IsOpenImmersion f.left] : IsOpenImmersion (f ▷ Z).left := by
  have h : IsPullback (fst X Z).left (f ▷ Z).left f.left (fst Y Z).left := by
    apply IsPullback.of_bot _ _ (overProduct_isPullback Y Z)
    · simpa only [← Over.comp_left, whiskerRight_snd, Over.w] using overProduct_isPullback X Z
    · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  exact MorphismProperty.of_isPullback h inferInstance

private theorem whiskerLeft_open {X Y : Over S} (f : X ⟶ Y) (Z : Over S)
    [IsOpenImmersion f.left] : IsOpenImmersion (Z ◁ f).left := by
  have h : IsPullback (snd Z X).left (Z ◁ f).left f.left (snd Z Y).left := by
    apply IsPullback.of_bot _ _ (overProduct_isPullback Z Y).flip
    · simpa only [← Over.comp_left, whiskerLeft_fst, Over.w] using (overProduct_isPullback Z X).flip
    · rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  exact MorphismProperty.of_isPullback h inferInstance

/-- The two-cell difference map is smooth whenever the cell is open in a
smooth group. This part of the cover argument is valid over an arbitrary base. -/
private theorem cellDivision_smooth (G : Grp (Over S)) {W : Over S} (i : W ⟶ G.X)
    [Smooth G.X.hom] [IsOpenImmersion i.left] : Smooth (cellDivision G i).left := by
  letI : IsOpenImmersion (i ▷ W).left := whiskerRight_open i W
  letI : IsOpenImmersion (G.X ◁ i).left := whiskerLeft_open i G.X
  have hi : IsOpenImmersion (i ⊗ₘ i).left := by
    rw [tensorHom_def, Over.comp_left]
    infer_instance
  have hf : Smooth (fst G.X G.X).left :=
    MorphismProperty.of_isPullback (overProduct_isPullback G.X G.X).flip inferInstance
  have he : cellDivision G i = (i ⊗ₘ i) ≫ (divisionIso G).hom ≫ fst G.X G.X := by
    rw [divisionIso, lift_fst]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, tensorHom_fst, tensorHom_snd, cellDivision]
  rw [he, Over.comp_left, Over.comp_left]
  infer_instance

private def leftTranslation (G : Grp (Over S)) (t : 𝟙_ (Over S) ⟶ G.X) : G.X ≅ G.X where
  hom := (toUnit G.X ≫ t) * 𝟙 G.X
  inv := (toUnit G.X ≫ t⁻¹) * 𝟙 G.X
  hom_inv_id := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc]
    have h : ((toUnit G.X ≫ t) * 𝟙 G.X) ≫ toUnit G.X = toUnit G.X := toUnit_unique _ _
    rw [h, GrpObj.comp_inv]
    exact inv_mul_cancel_left (toUnit G.X ≫ t) (𝟙 G.X)
  inv_hom_id := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc]
    have h : ((toUnit G.X ≫ t⁻¹) * 𝟙 G.X) ≫ toUnit G.X = toUnit G.X := toUnit_unique _ _
    rw [h, GrpObj.comp_inv]
    exact mul_inv_cancel_left (toUnit G.X ≫ t) (𝟙 G.X)

private theorem liftFieldPointToOpen {K : Type u} [Field K]
    {U V : Over (Spec (CommRingCat.of K))} (j : U ⟶ V)
    [IsOpenImmersion j.left] (p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ V)
    (hp : p.left (IsLocalRing.closedPoint K) ∈ Set.range j.left) :
    ∃ q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ U, q ≫ j = p := by
  letI : Subsingleton ((𝟙_ (Over (Spec (CommRingCat.of K)))).left : Type u) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of K) : Type u))
  have hr : Set.range p.left ⊆ Set.range j.left := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint K)]
    exact hp
  let q := IsOpenImmersion.lift j.left p.left hr
  have hq : q ≫ j.left = p.left := IsOpenImmersion.lift_fac j.left p.left hr
  refine ⟨Over.homMk q ?_, Over.OverMorphism.ext hq⟩
  rw [← Over.w j, ← Category.assoc, hq, Over.w]

/-- Two nonempty open translates in an irreducible geometric fibre meet.
Every field point belongs to the image of the difference map. -/
private theorem cellDivision_geometricPoint {K : Type u} [Field K] [IsAlgClosed K]
    (G : GroupScheme K) {W : SchemeOver K} (i : W ⟶ G.X)
    [IsOpenImmersion i.left] [IrreducibleSpace G.X.left] [LocallyOfFiniteType G.X.hom]
    [Nonempty W.left] (t : 𝟙_ (SchemeOver K) ⟶ G.X) :
    ∃ p : 𝟙_ (SchemeOver K) ⟶ W ⊗ W, p ≫ cellDivision G i = t := by
  let L := leftTranslation G t
  let j := i ≫ L.hom
  haveI : IsOpenImmersion j.left := by unfold j; rw [Over.comp_left]; infer_instance
  have hio := i.left.isOpenEmbedding.isOpenMap.isOpen_range
  have hjo := j.left.isOpenEmbedding.isOpenMap.isOpen_range
  have hid := hio.dense (Set.range_nonempty i.left)
  have hjd := hjo.dense (Set.range_nonempty j.left)
  letI : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  obtain ⟨x, hx, hclosed⟩ := nonempty_inter_closedPoints
    (hid.inter_of_isOpen_left hjd hio).nonempty (hio.inter hjo).isLocallyClosed
  let p : 𝟙_ (SchemeOver K) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom x hclosed)
      (pointOfClosedPoint_comp G.X.hom x hclosed)
  have hval : p.left (IsLocalRing.closedPoint K) = x := pointOfClosedPoint_apply _ _ _ _
  obtain ⟨a, ha⟩ := liftFieldPointToOpen i p (hval ▸ hx.1)
  obtain ⟨b, hb⟩ := liftFieldPointToOpen j p (hval ▸ hx.2)
  refine ⟨lift a b, ?_⟩
  have eq : a ≫ i = t * (b ≫ i) := by
    rw [ha, ← hb]
    change b ≫ (i ≫ ((toUnit G.X ≫ t) * 𝟙 G.X)) = _
    rw [← Category.assoc, MonObj.comp_mul, Category.comp_id, ← Category.assoc]
    have h : (b ≫ i) ≫ toUnit G.X = 𝟙 _ := toUnit_unique _ _
    rw [h, Category.id_comp]
  simp only [cellDivision, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc]
  rw [eq, mul_inv_cancel_right]

private theorem openAfterPullback {B : Scheme.{u}} (a : B ⟶ S) {W X : Over S}
    (i : W ⟶ X) [IsOpenImmersion i.left] :
    IsOpenImmersion ((Over.pullback a).map i).left := by
  let F := Over.pullback a
  have hpb : IsPullback (pullback.fst W.hom a) (F.map i).left
      i.left (pullback.fst X.hom a) := by
    apply IsPullback.of_bot _ _ (IsPullback.of_hasPullback X.hom a)
    · have hi : i.left ≫ X.hom = W.hom := i.w
      have hFi : (F.map i).left ≫ pullback.snd X.hom a = pullback.snd W.hom a :=
        (F.map i).w
      rw [hi, hFi]
      exact IsPullback.of_hasPullback W.hom a
    · exact (pullback.lift_fst _ _ _).symm
  exact MorphismProperty.of_isPullback hpb inferInstance

private theorem cellDivision_pullback {B : Scheme.{u}} (a : B ⟶ S) (G : Grp (Over S))
    {W : Over S} (i : W ⟶ G.X) :
    let F := Over.pullback a
    Functor.LaxMonoidal.μ F W W ≫ F.map (cellDivision G i) =
      cellDivision (F.mapGrp.obj G) (F.map i) := by
  dsimp only
  simp only [cellDivision, Functor.map_mul, Functor.map_inv', Functor.map_comp,
    MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    Functor.Monoidal.μ_fst, Functor.Monoidal.μ_snd]

/-- A point over an algebraically closed field factors on the two-cell
difference map whenever its base fibre is irreducible. -/
private theorem cellDivision_liftsFieldPoint {K : Type u} [Field K] [IsAlgClosed K]
    (G : Grp (Over S)) {W : Over S} (i : W ⟶ G.X)
    [IsOpenImmersion i.left] [LocallyOfFiniteType G.X.hom]
    (w : 𝟙_ (Over S) ⟶ W) (p : Spec (CommRingCat.of K) ⟶ G.X.left)
    (hfibre : IrreducibleSpace ((Over.pullback (p ≫ G.X.hom)).obj G.X).left) :
    ∃ v : Spec (CommRingCat.of K) ⟶ (W ⊗ W).left,
      v ≫ (cellDivision G i).left = p := by
  let a := p ≫ G.X.hom
  let F := Over.pullback a
  let G' : GroupScheme K := F.mapGrp.obj G
  let t : 𝟙_ (SchemeOver K) ⟶ G'.X :=
    Over.homMk (pullback.lift p (𝟙 _) (by simp [a])) (pullback.lift_snd _ _ _)
  haveI : IrreducibleSpace G'.X.left := hfibre
  haveI : LocallyOfFiniteType G'.X.hom :=
    MorphismProperty.pullback_snd G.X.hom a inferInstance
  letI : IsOpenImmersion (F.map i).left := openAfterPullback a i
  let w' := (Functor.Monoidal.εIso F).hom ≫ F.map w
  letI : Nonempty (F.obj W).left := ⟨w'.left (IsLocalRing.closedPoint K)⟩
  obtain ⟨z, hz⟩ := cellDivision_geometricPoint G' (F.map i) t
  let m := Functor.LaxMonoidal.μ F W W
  have hm : m ≫ F.map (cellDivision G i) = cellDivision G' (F.map i) :=
    cellDivision_pullback a G i
  have hz' : (z ≫ m).left ≫ (F.map (cellDivision G i)).left = t.left := by
    rw [← Over.comp_left, Category.assoc, hm, hz]
  let v := (z ≫ m).left ≫ pullback.fst (W ⊗ W).hom a
  have hv : v ≫ (cellDivision G i).left = p := by
    calc
      _ = (z ≫ m).left ≫ (F.map (cellDivision G i)).left ≫ pullback.fst G.X.hom a := by
        simp [v, F]
      _ = _ := by rw [← Category.assoc, hz']; exact pullback.lift_fst _ _ _
  exact ⟨v, hv⟩

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 700000 in
/-- A morphism covering all algebraically closed field points is surjective
on the underlying schemes. -/
private theorem surjective_of_liftsGeometricPoints {X Y : Scheme.{u}} (f : X ⟶ Y)
    (lifts : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (CommRingCat.of K) ⟶ Y),
      ∃ v : Spec (CommRingCat.of K) ⟶ X, v ≫ f = p) : Surjective f := by
  constructor
  intro y
  let k : Type u := Y.residueField y
  let K : Type u := AlgebraicClosure k
  let p : Spec (CommRingCat.of K) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ Y.fromSpecResidueField y
  obtain ⟨v, hv⟩ := lifts K p
  let pt := IsLocalRing.closedPoint K
  use v pt
  calc
    _ = (v ≫ f) pt := rfl
    _ = p pt := congrArg (fun q : Spec (CommRingCat.of K) ⟶ Y => q pt) hv
    _ = y := Y.fromSpecResidueField_apply y _

/-- Relative surjectivity follows by applying the two-open argument
on the geometric fibres. -/
private theorem cellDivision_surjective (G : Grp (Over S)) {W : Over S}
    (i : W ⟶ G.X) [IsOpenImmersion i.left] [LocallyOfFiniteType G.X.hom]
    (w : 𝟙_ (Over S) ⟶ W)
    (hfibre : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (CommRingCat.of K) ⟶ S),
      IrreducibleSpace ((Over.pullback a).obj G.X).left) :
    Surjective (cellDivision G i).left :=
  surjective_of_liftsGeometricPoints _ fun K _ _ p =>
    cellDivision_liftsFieldPoint G i w p (hfibre K (p ≫ G.X.hom))

private theorem faithfullyFlat_of_smoothAffineCover {R B C : Type u}
    [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (f : B →ₐ[R] C)
    (hs : Smooth (spectrumOfAlgHom f).left)
    (hq : Surjective (spectrumOfAlgHom f).left) :
    f.toRingHom.FaithfullyFlat := by
  let g : CommRingCat.of B ⟶ CommRingCat.of C := CommRingCat.ofHom f.toRingHom
  letI : Smooth (Spec.map g) := hs
  exact (flat_and_surjective_SpecMap_iff g).mp ⟨inferInstance, hq⟩

end CellGeometry

section AffineProducts

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

variable {R : Type u} [CommRing R]

private theorem affine_product (X Y : OverBase R)
    [IsAffine X.left] [IsAffine Y.left] : IsAffine (X ⊗ Y).left := by
  haveI : IsAffineHom X.hom := isAffineHom_of_isAffine X.hom
  haveI : IsAffineHom (snd X Y).left :=
    MorphismProperty.of_isPullback (overProduct_isPullback X Y) inferInstance
  exact isAffine_of_isAffineHom (snd X Y).left

private theorem affine_lineProduct {I : Type u} (l : List I) :
    IsAffine (lineProduct R l).left := by
  induction l with
  | nil => exact inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  | cons i l ih =>
    change IsAffine (((algSpec (CommRingCat.of R)).obj
      (op (CommAlgCat.of R (Polynomial R)))) ⊗ lineProduct R l).left
    letI : IsAffine ((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (Polynomial R)))).left :=
      inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial R))))
    exact affine_product _ _

private theorem faithfullyFlatCellCover_of_smooth_surjective
    {A : Type u} [CommRing A] [HopfAlgebra R A] {W : OverBase R}
    [IsAffine W.left] (i : W ⟶ (HopfSpectrum R A).X)
    [Smooth (cellDivision (HopfSpectrum R A) i).left]
    [Surjective (cellDivision (HopfSpectrum R A) i).left] : FaithfullyFlatCellCover i := by
  let F := algSpec (CommRingCat.of R)
  obtain ⟨C, ⟨e⟩⟩ := essImage_algSpec.mpr (affine_product W W)
  let f : A →ₐ[R] C.unop :=
    ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage
      (e.hom ≫ cellDivision (HopfSpectrum R A) i)).unop.hom
  have hf : spectrumOfAlgHom f = e.hom ≫ cellDivision (HopfSpectrum R A) i :=
    (algSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage _
  letI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  haveI : IsOpenImmersion e.hom.left := .of_isIso _
  have hs : Smooth (spectrumOfAlgHom f).left := by
    rw [hf, Over.comp_left]
    exact smooth_comp e.hom.left (cellDivision (HopfSpectrum R A) i).left
  have hq : Surjective (spectrumOfAlgHom f).left := by
    rw [hf, Over.comp_left]
    exact ⟨(cellDivision (HopfSpectrum R A) i).left.surjective.comp e.hom.left.surjective⟩
  exact ⟨C.unop, e, f, hf, faithfullyFlat_of_smoothAffineCover f hs hq⟩

private def zeroParameters {I : Type u} :
    (l : List I) → 𝟙_ (OverBase R) ⟶ lineProduct R l
  | [] => 𝟙 _
  | _ :: l =>
    lift (Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := R) (0 : R)).toRingHom))
      (by
        change Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := R) (0 : R)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R))) = 𝟙 _
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
        exact CommRingCat.hom_ext (RingHom.ext fun r => (Polynomial.aeval (R := R) (0 : R)).commutes r)))
      (zeroParameters l)

end AffineProducts

section GeometricFibres

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.CharacterDescent (Character Cocharacter compositionPairing)
open Specs.CharacterPairing (pairing powerMorphism)
open Specs.DiagonalizableGroups (groupAlgebraMap IntegerCharacters integerGenerator)
open Specs.OrderedRootProducts (product rootCellMap RootSubgroupFamily)
open Specs.Pinning (RootCoordinate)
open CocharacterDynamics (oppositeCocharacter)
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private group_irreducible_of_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]

private abbrev changeOfBase (K : Type u) [Field K] [Algebra R K] :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))

private def fibreSpecIso (K : Type u) [Field K] [Algebra R K]
    (B : Type u) [CommRing B] [Algebra R B] :
    (changeOfBase (R := R) K).obj ((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R B))) ≅
      (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K (K ⊗[R] B))) :=
  (pullbackSymmetry .. ≪≫ pullbackSpecIso' R K B).asOver (Spec (CommRingCat.of K))

private def fibreGroupIso (K : Type u) [Field K] [Algebra R K]
    (B : Type u) [CommRing B] [HopfAlgebra R B] :
    (fibreGroup K).obj (HopfSpectrum R B) ≅ HopfSpectrum K (K ⊗[R] B) := by
  let e : ((fibreGroup K).obj (HopfSpectrum R B)).X ≅ (HopfSpectrum K (K ⊗[R] B)).X :=
    fibreSpecIso (R := R) K B
  haveI : IsMonHom e.hom := by
    change IsMonHom ((pullbackSymmetry .. ≪≫ pullbackSpecIso' R K B).hom.asOver
      (Spec (CommRingCat.of K)))
    infer_instance
  exact Grp.mkIso e (IsMonHom.one_hom (f := e.hom)) (IsMonHom.mul_hom (f := e.hom))

@[reassoc]
private theorem fibreSpecIso_inv_fst (K : Type u) [Field K] [Algebra R K]
    (B : Type u) [CommRing B] [Algebra R B] :
    (fibreSpecIso (R := R) K B).inv.left ≫ pullback.fst
      ((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R B))).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom) := by
  change (pullbackSpecIso' R K B).inv ≫ (pullbackSymmetry _ _).inv ≫ pullback.fst _ _ = _
  rw [pullbackSymmetry_inv_comp_fst]
  exact pullbackSpecIso_inv_snd R K B

private theorem fibreSpecIso_natural (K : Type u) [Field K] [Algebra R K]
    {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] (f : B →ₐ[R] C) :
    (fibreSpecIso K C).inv ≫ (changeOfBase K).map (spectrumOfAlgHom f) =
      spectrumOfAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) f) ≫ (fibreSpecIso K B).inv := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, changeOfBase, Over.pullback_map_left,
      pullback.lift_fst, fibreSpecIso_inv_fst_assoc]
    erw [fibreSpecIso_inv_fst (R := R) K B]
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) f).toRingHom) ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  · exact (Over.w _).trans (Over.w _).symm

private def polynomialFibreEquiv (K : Type u) [Field K] [Algebra R K] :
    K ⊗[R] Polynomial R ≃ₐ[K] Polynomial K :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K)
      (MvPolynomial.uniqueAlgEquiv R Unit).symm).trans
    ((MvPolynomial.algebraTensorAlgEquiv R K).trans (MvPolynomial.uniqueAlgEquiv K Unit))

private theorem polynomialFibreEquiv_comp (K : Type u) [Field K] [Algebra R K]
    (x : A →ₐ[R] Polynomial R) :
    (polynomialFibreEquiv (R := R) K).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id K K) x) = extendCoordinate K x := by
  apply (AlgHom.liftEquiv R K A (Polynomial K)).symm.injective
  change (((polynomialFibreEquiv (R := R) K).toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : Polynomial R →ₐ[R] K ⊗[R] Polynomial R)).comp x = _
  unfold extendCoordinate
  rw [Equiv.symm_apply_apply]
  congr 1
  apply Polynomial.algHom_ext
  change polynomialFibreEquiv (R := R) K (1 ⊗ₜ[R] Polynomial.X) = _
  simp [polynomialFibreEquiv]

private theorem pairing_opposite {K : Type u} [Field K] {T : GroupScheme K}
    (α : Character T) (c : Cocharacter T) :
    pairing T α (oppositeCocharacter c) = -pairing T α c := by
  let n := pairing T α c
  obtain ⟨h, _⟩ := RootData.CharacterPairing.characterPairingComposition T α c
  apply ((RootData.CharacterPairing.characterPairingComposition T α (oppositeCocharacter c)).1 _).mp
  have hc : c ≫ α = powerMorphism n := (h n).mpr rfl
  rw [compositionPairing, oppositeCocharacter, Category.assoc, hc, powerMorphism, ← specGroupMap_comp]
  change specGroupMap (groupAlgebraMap K _ ≫ groupAlgebraMap K _) = powerMorphism (-n)
  rw [powerMorphism]
  congr 1
  apply CommHopfAlgCat.hom_ext
  change (MonoidAlgebra.mapDomainBialgHom K (invMonoidHom (α := IntegerCharacters))).comp
    (MonoidAlgebra.mapDomainBialgHom K _) = MonoidAlgebra.mapDomainBialgHom K _
  rw [← MonoidAlgebra.mapDomainBialgHom_comp]
  congr 1
  ext a
  simp [zpow_neg]

private theorem calibrated_orders {D : BasedRootDatum.{u}}
    {t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)}
    {K : Type u} [Field K] [Algebra R K] (F : FibreDatum D t K)
    (negative positive : List D.I)
    (hn : Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Enumerates positive {i | D.base.IsPos i}) :
    ∃ c : Cocharacter F.pair.T.group, IsRegular F.pair.T c ∧
      Enumerates (negative.map F.based.val.indexEquiv) (positiveRoots F.pair.T (oppositeCocharacter c)) ∧
      Enumerates (positive.map F.based.val.indexEquiv) (positiveRoots F.pair.T c) := by
  classical
  let P := F.pair
  let e := F.based.val.indexEquiv
  letI := F.attached.comm
  letI : Finite D.I := D.finiteRoots
  obtain ⟨c, _, hreg, _, hroots⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  let p : D.X →ₗ[ℤ] ℤ := (F.attached.datum.rootDatum.toLinearMap.flip (Additive.ofMul c)).comp
    F.based.val.weightEquiv.toLinearMap
  have hpair (i : D.I) : p (D.datum.root i) = pairing P.T.group (e i).val c := by
    change F.attached.datum.rootDatum.toLinearMap (F.based.val.weightEquiv (D.datum.root i))
      (Additive.ofMul c) = _
    rw [RootPairing.Equiv.weightEquiv_apply, RootPairing.Hom.root_weightMap_apply]
    change F.attached.datum.rootDatum.toLinearMap (F.attached.datum.rootDatum.root (e i))
      (Additive.ofMul c) = _
    rw [F.attached.datum.root_eq, F.attached.datum.pairing_eq]
  have hsimple (i : D.I) (hi : i ∈ D.base.support) : 0 < p (D.datum.root i) := by
    have ha : e i ∈ F.attached.base.support := by
      change F.based.val.indexEquiv i ∈ (F.attached.toBased.base.support : Set F.attached.toBased.I)
      exact (congrArg (fun S : Set F.attached.toBased.I => F.based.val.indexEquiv i ∈ S)
        F.based.property).mp (Set.mem_image_of_mem F.based.val.indexEquiv hi)
    have hb := ((F.attached.simple_iff (e i)).mp ha).1
    rw [hroots] at hb
    exact (hpair i).symm ▸ hb
  have hpos (i : D.I) (hi : D.base.IsPos i) : 0 < p (D.datum.root i) := by
    refine hi.induction_on_add hsimple ?_
    intro a b d he ha hb
    rw [he, map_add]
    exact add_pos ha (hsimple b hb)
  have hp' (i : D.I) : e i ∈ positiveRoots P.T c ↔ D.base.IsPos i := by
    change 0 < pairing P.T.group (e i).val c ↔ _
    rw [← hpair]
    refine ⟨fun hi => ?_, hpos i⟩
    by_contra hn
    have hj := hpos (D.datum.reflectionPerm i i) ((RootPairing.Base.IsPos.neg_iff_not D.base i).mpr hn)
    rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self, map_neg] at hj
    omega
  have hn' (i : D.I) : e i ∈ positiveRoots P.T (oppositeCocharacter c) ↔ ¬ D.base.IsPos i := by
    change 0 < pairing P.T.group (e i).val (oppositeCocharacter c) ↔ _
    rw [pairing_opposite, ← hp']
    change 0 < -pairing P.T.group (e i).val c ↔ ¬ 0 < pairing P.T.group (e i).val c
    have h := hreg (e i)
    omega
  refine ⟨c, hreg, ⟨hn.1.map e.injective, ?_⟩, ⟨hp.1.map e.injective, ?_⟩⟩
  · intro α
    obtain ⟨i, rfl⟩ := e.surjective α
    change e i ∈ negative.map e ↔ e i ∈ positiveRoots P.T (oppositeCocharacter c)
    simpa only [List.mem_map, e.injective.eq_iff, exists_eq_right, hn', Set.mem_ofPred_eq] using hn.2 i
  · intro α
    obtain ⟨i, rfl⟩ := e.surjective α
    change e i ∈ positive.map e ↔ e i ∈ positiveRoots P.T c
    simpa only [List.mem_map, e.injective.eq_iff, exists_eq_right, hp', Set.mem_ofPred_eq] using hp.2 i

private abbrev affineLine (R : Type u) [CommRing R] : OverBase R :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (Polynomial R)))

private def lineFibreIso (K : Type u) [Field K] [Algebra R K] :
    affineLine K ≅ (changeOfBase (R := R) K).obj (affineLine R) :=
  ((algSpec (CommRingCat.of K)).mapIso
    (CommAlgCat.isoMk (polynomialFibreEquiv (R := R) K)).op) ≪≫ (fibreSpecIso K (Polynomial R)).symm

@[reassoc]
private theorem lineFibreIso_comm (K : Type u) [Field K] [Algebra R K]
    (x : A →ₐ[R] Polynomial R) :
    (lineFibreIso (R := R) K).hom ≫ (changeOfBase K).map (spectrumOfAlgHom x) =
      spectrumOfAlgHom (extendCoordinate K x) ≫ (fibreSpecIso K A).inv := by
  rw [lineFibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, fibreSpecIso_natural,
    ← Category.assoc, ← polynomialFibreEquiv_comp]
  congr 1
  exact ((algSpec (CommRingCat.of K)).map_comp _ _).symm

private def fibreProductIso {K : Type u} [Field K] (F : OverBase R ⥤ SchemeOver K)
    [PreservesFiniteProducts F] {B C : OverBase R} {B' C' : SchemeOver K}
    (e : B' ≅ F.obj B) (f : C' ≅ F.obj C) :
    B' ⊗ C' ≅ F.obj (B ⊗ C) :=
  tensorIso e f ≪≫ (asIso (CartesianMonoidalCategory.prodComparison F B C)).symm

@[reassoc]
private theorem fibreProductIso_fst {K : Type u} [Field K] (F : OverBase R ⥤ SchemeOver K)
    [PreservesFiniteProducts F] {B C : OverBase R} {B' C' : SchemeOver K}
    (e : B' ≅ F.obj B) (f : C' ≅ F.obj C) :
    (fibreProductIso F e f).hom ≫ F.map (fst B C) = fst B' C' ≫ e.hom := by
  simp [fibreProductIso]

@[reassoc]
private theorem fibreProductIso_snd {K : Type u} [Field K] (F : OverBase R ⥤ SchemeOver K)
    [PreservesFiniteProducts F] {B C : OverBase R} {B' C' : SchemeOver K}
    (e : B' ≅ F.obj B) (f : C' ≅ F.obj C) :
    (fibreProductIso F e f).hom ≫ F.map (snd B C) = snd B' C' ≫ f.hom := by
  simp [fibreProductIso]

private def orderedFibreIso {K : Type u} [Field K] [Algebra R K] {I J : Type u}
    (e : I → J) (X : J → SchemeOver K)
    (s : ∀ i, X (e i) ≅ (changeOfBase (R := R) K).obj (affineLine R)) :
    (l : List I) → product X (l.map e) ≅ (changeOfBase (R := R) K).obj (lineProduct R l)
  | [] => Functor.Monoidal.εIso (changeOfBase (R := R) K)
  | i :: l => fibreProductIso (changeOfBase (R := R) K) (s i) (orderedFibreIso e X s l)

private theorem orderedFibreIso_comm {K : Type u} [Field K] [Algebra R K] {I : Type u}
    {G : AffineAlgebraicGroup K} {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (e : I → Root T) (x : I → A →ₐ[R] Polynomial R)
    (g : (fibreGroup K).obj (HopfSpectrum R A) ⟶ G.val)
    (s : ∀ i, (U (e i)).val.group.X ≅ (changeOfBase (R := R) K).obj (affineLine R))
    (hs : ∀ i, (s i).hom ≫ (changeOfBase K).map (spectrumOfAlgHom (x i)) ≫ g.hom.hom =
      (U (e i)).val.inclusion.hom.hom) (l : List I) :
    (orderedFibreIso e (fun α => (U α).val.group.X) s l).hom ≫
      (changeOfBase K).map (Specs.IntegralCentralQuotient.rootProduct x l) ≫ g.hom.hom =
      Specs.OrderedRootProducts.rootProduct U (l.map e) := by
  induction l with
  | nil =>
    simp [orderedFibreIso, Specs.IntegralCentralQuotient.rootProduct,
      Functor.map_one, MonObj.comp_one, MonObj.one_comp]
    rfl
  | cons i l ih =>
    simp only [orderedFibreIso, Specs.IntegralCentralQuotient.rootProduct,
      Functor.map_mul, Functor.map_comp, MonObj.comp_mul, MonObj.mul_comp]
    simp only [← Category.assoc, fibreProductIso_fst, fibreProductIso_snd]
    simp only [Category.assoc, hs, ih]
    rfl

private theorem transport_cell_factors {K : Type u} [Field K] [Algebra R K]
    {G : Grp (OverBase R)} {J : GroupScheme K} (g : (fibreGroup K).obj G ⟶ J)
    {N T P : OverBase R} {N' T' P' : SchemeOver K}
    (en : N' ≅ (changeOfBase K).obj N) (et : T' ≅ (changeOfBase K).obj T)
    (ep : P' ≅ (changeOfBase K).obj P)
    (n : N ⟶ G.X) (t : T ⟶ G.X) (p : P ⟶ G.X) :
    (fibreProductIso (changeOfBase K) en (fibreProductIso (changeOfBase K) et ep)).hom ≫
      (changeOfBase K).map ((fst N (T ⊗ P) ≫ n) *
        (snd N (T ⊗ P) ≫ ((fst T P ≫ t) * (snd T P ≫ p)))) ≫ g.hom.hom =
      (fst N' (T' ⊗ P') ≫ (en.hom ≫ (changeOfBase K).map n ≫ g.hom.hom)) *
        (snd N' (T' ⊗ P') ≫
          ((fst T' P' ≫ (et.hom ≫ (changeOfBase K).map t ≫ g.hom.hom)) *
            (snd T' P' ≫ (ep.hom ≫ (changeOfBase K).map p ≫ g.hom.hom)))) := by
  simp only [Functor.map_mul, Functor.map_comp, MonObj.comp_mul, MonObj.mul_comp,
    Category.assoc, fibreProductIso_fst_assoc, fibreProductIso_snd_assoc]

private theorem fibre_open_cell {D : BasedRootDatum.{u}}
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)) (x : D.I → A →ₐ[R] Polynomial R)
    {K : Type u} [Field K] [Algebra R K] (F : FibreDatum D t K) (hF : FibreCoordinates F x)
    (negative positive : List D.I)
    (hn : Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Enumerates positive {i | D.base.IsPos i}) :
    IsOpenImmersion ((changeOfBase K).map (cellMap t x negative positive)).left := by
  classical
  obtain ⟨c, hreg, hn', hp'⟩ := calibrated_orders F negative positive hn hp
  obtain ⟨L, U, hU⟩ := hF
  let y (i : D.I) := (hU i).choose
  let P := F.pair
  let H := MonoidAlgebra R (Multiplicative D.X)
  let e := F.based.val.indexEquiv
  let Q := changeOfBase (R := R) K
  let G := HopfSpectrum R A
  let g := fibreGroupIso K A ≪≫ F.groupIso
  let k := fibreGroupIso K H ≪≫ F.torusIso
  let s (i : D.I) : (U (e i)).val.group.X ≅ Q.obj (affineLine R) :=
    ((Grp.forget (SchemeOver K)).mapIso (y i).val.symm) ≪≫ lineFibreIso K
  have hs (i : D.I) : (s i).hom ≫ Q.map (spectrumOfAlgHom (x i)) ≫ g.hom.hom.hom =
      (U (e i)).val.inclusion.hom.hom := by
    have hy : spectrumOfAlgHom (extendCoordinate K (x i)) ≫ F.groupIso.hom.hom.hom =
        (y i).val.hom.hom.hom ≫ (U (e i)).val.inclusion.hom.hom := (hU i).choose_spec
    change (y i).val.inv.hom.hom ≫
      (lineFibreIso K).hom ≫ Q.map (spectrumOfAlgHom (x i)) ≫
        g.hom.hom.hom = _
    rw [lineFibreIso_comm_assoc]
    change (y i).val.inv.hom.hom ≫ spectrumOfAlgHom (extendCoordinate K (x i)) ≫
      (fibreSpecIso K A).inv ≫ (fibreSpecIso K A).hom ≫ F.groupIso.hom.hom.hom = _
    rw [Iso.inv_hom_id_assoc, hy, ← Category.assoc]
    have hInv : (y i).val.inv.hom.hom ≫ (y i).val.hom.hom.hom = 𝟙 _ :=
      congrArg (fun a => a.hom.hom) (y i).val.inv_hom_id
    rw [hInv, Category.id_comp]
  have ht : Q.map (spectrumOfHopfHom t).hom.hom ≫ g.hom.hom.hom =
      k.hom.hom.hom ≫ P.T.inclusion.hom.hom := by
    have h : (fibreSpecIso K H).inv ≫ Q.map (spectrumOfAlgHom t.toAlgHom) =
        spectrumOfAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) t.toAlgHom) ≫
          (fibreSpecIso K A).inv := fibreSpecIso_natural K t.toAlgHom
    have hc : Q.map (spectrumOfAlgHom t.toAlgHom) ≫ (fibreSpecIso K A).hom =
        (fibreSpecIso K H).hom ≫
          spectrumOfAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) t.toAlgHom) := by
      have hh := congrArg (fun a => (fibreSpecIso K H).hom ≫ a ≫ (fibreSpecIso K A).hom) h
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using hh
    have ht := congrArg (fun a => a.hom.hom) F.torus_comm
    change spectrumOfAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) t.toAlgHom) ≫
      F.groupIso.hom.hom.hom = F.torusIso.hom.hom.hom ≫ P.T.inclusion.hom.hom at ht
    change Q.map (spectrumOfAlgHom t.toAlgHom) ≫ (fibreSpecIso K A).hom ≫ F.groupIso.hom.hom.hom =
      (fibreSpecIso K H).hom ≫ F.torusIso.hom.hom.hom ≫ P.T.inclusion.hom.hom
    rw [← Category.assoc, hc, Category.assoc, ht]
  let sn := orderedFibreIso e (fun α => (U α).val.group.X) s negative
  let sp := orderedFibreIso e (fun α => (U α).val.group.X) s positive
  let st := (Grp.forget (SchemeOver K)).mapIso k.symm
  let j := fibreProductIso Q sn (fibreProductIso Q st sp)
  have hnt : sn.hom ≫ Q.map (Specs.IntegralCentralQuotient.rootProduct x negative) ≫
      g.hom.hom.hom = Specs.OrderedRootProducts.rootProduct U (negative.map e) :=
    orderedFibreIso_comm U e x g.hom s hs negative
  have hpt : sp.hom ≫ Q.map (Specs.IntegralCentralQuotient.rootProduct x positive) ≫
      g.hom.hom.hom = Specs.OrderedRootProducts.rootProduct U (positive.map e) :=
    orderedFibreIso_comm U e x g.hom s hs positive
  have htorus : st.hom ≫ Q.map (spectrumOfHopfHom t).hom.hom ≫ g.hom.hom.hom =
      P.T.inclusion.hom.hom := by
    rw [ht, ← Category.assoc]
    have he : st.hom ≫ k.hom.hom.hom = 𝟙 _ :=
      ((Grp.forget (SchemeOver K)).mapIso k).inv_hom_id
    rw [he, Category.id_comp]
  have he : j.hom ≫ Q.map (cellMap t x negative positive) ≫ g.hom.hom.hom =
      rootCellMap P.T U (negative.map e) (positive.map e) := by
    have hw := transport_cell_factors g.hom sn st sp
      (Specs.IntegralCentralQuotient.rootProduct x negative) (spectrumOfHopfHom t).hom.hom
      (Specs.IntegralCentralQuotient.rootProduct x positive)
    rw [hnt, htorus, hpt] at hw
    exact hw
  have hlo := RootData.OrderedRootProducts.regularRootCell P.G P.reductive P.T P.split P.maximal
    c hreg U _ _ hn' hp'
  rw [← he, Over.comp_left, Over.comp_left] at hlo
  have hj : IsIso j.hom.left := (Over.forget _).map_isIso j.hom
  have hg : IsIso g.hom.hom.hom.left := (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso g.hom
  rwa [MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion)] at hlo

private theorem integral_fibre_irreducible {D : BasedRootDatum.{u}}
    {t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)}
    {K : Type u} [Field K] [IsAlgClosed K] [Algebra R K] (F : FibreDatum D t K) :
    IrreducibleSpace ((changeOfBase (R := R) K).obj (HopfSpectrum R A).X).left := by
  haveI : GeometricallyConnected F.pair.G.val.X.hom := F.pair.reductive.2.1
  haveI : ConnectedSpace F.pair.G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton F.pair.G.val.X.hom
  have h : IrreducibleSpace F.pair.G.val.X.left := group_irreducible_of_connected F.pair.G
  let e := (Grp.forget (SchemeOver K) ⋙ Over.forget _).mapIso
    (fibreGroupIso K A ≪≫ F.groupIso)
  exact e.hom.homeomorph.irreducibleSpace_iff.mpr h

end GeometricFibres


section RelativeDifferentials

open KaehlerDifferential Algebra TensorProduct
open TensorProduct.AlgebraTensorModule (cancelBaseChange)

set_option linter.style.haveILetI false

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A finite module vanishes if it vanishes after every geometric base change.
At a maximal ideal of its support, Nakayama's lemma detects a nonzero fibre. -/
private theorem finite_subsingleton_of_geometric_extensions
    {R B M : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      Subsingleton ((K ⊗[R] B) ⊗[B] M)) : Subsingleton M := by
  by_contra hs
  letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hs
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Module.annihilator B M)
    (mt Module.annihilator_eq_top_iff.mp hs)
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  let K := AlgebraicClosure (B ⧸ m)
  letI : Module B (K ⊗[R] B) := (Algebra.TensorProduct.rightAlgebra : Algebra B (K ⊗[R] B)).toModule
  have hi : Subsingleton ((K ⊗[R] B) ⊗[B] M) := h K
  let e : K ⊗[R] B →ₗ[B] K :=
    { toFun := AlgHom.liftEquiv R K B K (IsScalarTower.toAlgHom R B K)
      map_add' := map_add _
      map_smul' := fun b z => by
        simp only [RingHom.id_apply, Algebra.smul_def]
        change (AlgHom.liftEquiv R K B K
          (IsScalarTower.toAlgHom R B K)) ((1 ⊗ₜ[R] b) * z) = algebraMap B K b * _
        rw [map_mul]
        congr 1
        simp }
  have he : Function.Surjective e := by
    intro k
    refine ⟨k ⊗ₜ[R] (1 : B), ?_⟩
    change (AlgHom.liftEquiv R K B K
      (IsScalarTower.toAlgHom R B K)) (k ⊗ₜ[R] (1 : B)) = k
    simp
  have hk : Subsingleton (K ⊗[B] M) :=
    (LinearMap.rTensor_surjective M he).subsingleton
  let a := cancelBaseChange B (B ⧸ m) (B ⧸ m) K M
  haveI : Subsingleton (K ⊗[B ⧸ m] ((B ⧸ m) ⊗[B] M)) := a.injective.subsingleton
  haveI : Subsingleton ((B ⧸ m) ⊗[B] M) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right (R := B ⧸ m) (M := K)).mp inferInstance
  have hquot := (TensorProduct.quotTensorEquivQuotSMul M m).surjective.subsingleton
  have hsmt : (m • (⊤ : Submodule B M)) = ⊤ :=
    (Submodule.Quotient.subsingleton_iff).mp hquot
  obtain ⟨r, hr, hz⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    m (⊤ : Submodule B M) Module.Finite.fg_top hsmt.ge
  have hra : r ∈ Module.annihilator B M := by
    rw [Module.mem_annihilator]
    intro x
    exact hz x (Submodule.mem_top)
  have hone : (1 : B) ∈ m := by
    simpa using m.sub_mem (hle hra) hr
  exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)

private theorem bijective_of_geometric_extensions
    {R B M N : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    [AddCommGroup N] [Module B N] [Module.Finite B N] [Module.Projective B N]
    (f : M →ₗ[B] N)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      Function.Bijective (f.lTensor (K ⊗[R] B))) : Function.Bijective f := by
  let q := f.range.mkQ
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hzero : q ∘ₗ f = 0 := by ext x; simp [q]
  haveI : Subsingleton (N ⧸ f.range) := finite_subsingleton_of_geometric_extensions
    (R := R) (B := B) fun K _ _ _ => by
      have hz : (q.lTensor (K ⊗[R] B)) ∘ₗ (f.lTensor (K ⊗[R] B)) = 0 := by
        rw [← LinearMap.lTensor_comp, hzero, LinearMap.lTensor_zero]
      have hq' : q.lTensor (K ⊗[R] B) = 0 := by
        apply LinearMap.ext
        intro y
        obtain ⟨x, rfl⟩ := (h K).surjective y
        simpa using LinearMap.congr_fun hz x
      refine ⟨fun x y => ?_⟩
      obtain ⟨a, rfl⟩ := LinearMap.lTensor_surjective _ hq x
      obtain ⟨b, rfl⟩ := LinearMap.lTensor_surjective _ hq y
      rw [hq']
      rfl
  have hsurj : Function.Surjective f :=
    LinearMap.range_eq_top.mp ((Submodule.Quotient.subsingleton_iff).mp inferInstance)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hsurj
  let g := LinearMap.id - s ∘ₗ f
  have hgf : f ∘ₗ g = 0 := by
    rw [LinearMap.comp_sub, LinearMap.comp_id, ← LinearMap.comp_assoc, hs, LinearMap.id_comp, sub_self]
  let r : M →ₗ[B] f.ker := g.codRestrict f.ker fun x => LinearMap.congr_fun hgf x
  have hr : Function.Surjective r := by
    intro x
    refine ⟨x, Subtype.ext ?_⟩
    change x.val - s (f x.val) = x.val
    rw [LinearMap.mem_ker.mp x.property, map_zero, sub_zero]
  letI : Module.Finite B f.ker := Module.Finite.of_surjective r hr
  haveI : Subsingleton f.ker := finite_subsingleton_of_geometric_extensions
    (R := R) (B := B) fun K _ _ _ => by
      have hz : (f.lTensor (K ⊗[R] B)) ∘ₗ (g.lTensor (K ⊗[R] B)) = 0 := by
        rw [← LinearMap.lTensor_comp, hgf, LinearMap.lTensor_zero]
      have hh : g.lTensor (K ⊗[R] B) = 0 := by
        apply LinearMap.ext
        intro x
        apply (h K).injective
        simpa using LinearMap.congr_fun hz x
      have hl : (r.lTensor (K ⊗[R] B)) ∘ₗ (f.ker.subtype.lTensor (K ⊗[R] B)) =
          LinearMap.id := by
        rw [← LinearMap.lTensor_comp, show r ∘ₗ f.ker.subtype = LinearMap.id from
          LinearMap.ext fun x => Subtype.ext (by
            change x.val - s (f x.val) = x.val
            rw [LinearMap.mem_ker.mp x.property, map_zero, sub_zero]), LinearMap.lTensor_id]
      have hi : Function.Injective (f.ker.subtype.lTensor (K ⊗[R] B)) :=
        Function.HasLeftInverse.injective ⟨_, fun x => LinearMap.congr_fun hl x⟩
      have hr' : (f.ker.subtype.lTensor (K ⊗[R] B)) ∘ₗ (r.lTensor (K ⊗[R] B)) = 0 := by
        rw [← LinearMap.lTensor_comp, show f.ker.subtype ∘ₗ r = g from rfl, hh]
      have hr0 : r.lTensor (K ⊗[R] B) = 0 := by
        apply LinearMap.ext
        intro x
        apply hi
        simpa using LinearMap.congr_fun hr' x
      refine ⟨fun x y => ?_⟩
      obtain ⟨a, rfl⟩ := LinearMap.lTensor_surjective _ hr x
      obtain ⟨b, rfl⟩ := LinearMap.lTensor_surjective _ hr y
      rw [hr0]
      rfl
  exact ⟨LinearMap.ker_eq_bot.mp (Submodule.subsingleton_iff_eq_bot.mp inferInstance), hsurj⟩

/-- For a formally smooth source, the Jacobi–Zariski sequence makes the
relative cotangent homology vanish when the map of base differentials is invertible. -/
private theorem formallyEtale_of_differentials {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [FormallySmooth R B] (h : Function.Bijective (mapBaseChange R A B)) :
    FormallyEtale A B := by
  have hΩ : Subsingleton Ω[B⁄A] := by
    have hzero (x : Ω[B⁄R]) : KaehlerDifferential.map R A B B x = 0 := by
      obtain ⟨y, rfl⟩ := h.surjective x
      exact (exact_mapBaseChange_map R A B _).mpr ⟨y, rfl⟩
    exact ⟨fun x y => by
      obtain ⟨a, rfl⟩ := KaehlerDifferential.map_surjective R A B x
      obtain ⟨b, rfl⟩ := KaehlerDifferential.map_surjective R A B y
      rw [hzero, hzero]⟩
  have hh : Subsingleton (H1Cotangent A B) := by
    suffices hzero : ∀ x : H1Cotangent A B, x = 0 from ⟨fun x y => (hzero x).trans (hzero y).symm⟩
    intro x
    have hx : H1Cotangent.δ R A B x = 0 := h.injective (by
      rw [map_zero]
      exact (H1Cotangent.exact_δ_mapBaseChange R A B _).mpr ⟨x, rfl⟩)
    obtain ⟨y, rfl⟩ := (H1Cotangent.exact_map_δ R A B x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨hΩ, hh⟩

/-- After geometric scalar extension the map of differentials is identified
with the one for the scalar-extended rings, hence is invertible for an étale fibre. -/
private theorem geometric_differential_comparison
    {R A B K : Type u} [CommRing R] [CommRing A] [CommRing B] [Field K]
    [Algebra R K] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hf : letI : Algebra (K ⊗[R] A) (K ⊗[R] B) :=
      (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra
      FormallyEtale (K ⊗[R] A) (K ⊗[R] B)) :
    Function.Bijective ((mapBaseChange R A B).lTensor (K ⊗[R] B)) := by
  let AK := K ⊗[R] A
  let BK := K ⊗[R] B
  let g : AK →ₐ[K] BK := Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R A B)
  letI : Algebra AK BK := g.toRingHom.toAlgebra
  letI : Algebra A BK := ((algebraMap B BK).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B BK := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A AK BK := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change (1 : K) ⊗ₜ[R] algebraMap A B a = g (1 ⊗ₜ[R] a)
    rfl)
  haveI : IsScalarTower K AK BK := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun k => (g.commutes k).symm)
  haveI : IsScalarTower R A BK := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R B BK, IsScalarTower.algebraMap_eq R A B]
    rfl)
  letI : FormallyEtale AK BK := hf
  let e₁ : BK ⊗[B] (B ⊗[A] Ω[A⁄R]) ≃ₗ[BK] BK ⊗[AK] Ω[AK⁄K] :=
    (cancelBaseChange A B BK BK Ω[A⁄R]).trans
      ((cancelBaseChange A AK BK BK Ω[A⁄R]).symm.trans
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl BK BK)
          (tensorKaehlerEquiv R K A AK)))
  let e₂ := tensorKaehlerEquiv R K B BK
  let e₃ := tensorKaehlerEquivOfFormallyEtale K AK BK
  let d₁ := e₂.toLinearMap ∘ₗ (mapBaseChange R A B).baseChange BK
  let d₂ := e₃.toLinearMap ∘ₗ e₁.toLinearMap
  let j : Ω[A⁄R] →ₗ[A] BK ⊗[B] (B ⊗[A] Ω[A⁄R]) :=
    ((TensorProduct.mk B BK _ 1).restrictScalars A) ∘ₗ (TensorProduct.mk A B _ 1)
  have hj : (d₁.restrictScalars A) ∘ₗ j = (d₂.restrictScalars A) ∘ₗ j := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro a
    change e₂ ((mapBaseChange R A B).baseChange BK (1 ⊗ₜ[B] (1 ⊗ₜ[A] D R A a))) =
      e₃ (e₁ (1 ⊗ₜ[B] (1 ⊗ₜ[A] D R A a)))
    simp only [LinearMap.baseChange_tmul, mapBaseChange_tmul, one_smul, map_D, e₂,
      tensorKaehlerEquiv_tmul_D, e₁, LinearEquiv.trans_apply, AlgebraTensorModule.cancelBaseChange_tmul,
      AlgebraTensorModule.cancelBaseChange_symm_tmul, TensorProduct.AlgebraTensorModule.congr_tmul,
      LinearEquiv.refl_apply, e₃, tensorKaehlerEquivOfFormallyEtale_apply]
    rfl
  have he : d₁ = d₂ := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro z w
    refine TensorProduct.inductionOn (motive := fun w =>
      d₁ (z ⊗ₜ[B] w) = d₂ (z ⊗ₜ[B] w)) w (fun b w => ?_) (fun x y hx hy => ?_)
    · have heq : z ⊗ₜ[B] (b ⊗ₜ[A] w) =
          (b • z) • ((1 : BK) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] w)) := by
        rw [show b ⊗ₜ[A] w = b • ((1 : B) ⊗ₜ[A] w) by
          simpa only [smul_eq_mul, mul_one] using (TensorProduct.smul_tmul' b (1 : B) w).symm,
          TensorProduct.tmul_smul]
        exact TensorProduct.tmul_eq_smul_one_tmul (b • z) ((1 : B) ⊗ₜ[A] w)
      rw [heq, map_smul, map_smul]
      exact congrArg ((b • z) • ·) (LinearMap.congr_fun hj w)
    · simp only [TensorProduct.tmul_add, map_add, hx, hy]
  have he' : (e₂ ∘ (mapBaseChange R A B).lTensor BK) = e₃ ∘ e₁ :=
    funext fun y => LinearMap.congr_fun he y
  exact (e₂.bijective.of_comp_iff' _).mp (he' ▸ e₃.bijective.comp e₁.bijective)

private theorem lift_unit_of_square_zero {B : Type u} [CommRing B] (I : Ideal B) (hI : I ^ 2 = ⊥)
    (u : (B ⧸ I)ˣ) : ∃ v : Bˣ, Units.map (Ideal.Quotient.mk I).toMonoidHom v = u := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ I)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ I)
  have hxy : x * y - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hx, hy]
    simp
  have hn : IsNilpotent (x * y - 1) := ⟨2, by
    have h := Ideal.pow_mem_pow hxy 2
    rwa [hI, Ideal.mem_bot] at h⟩
  have hu : IsUnit (x * y) := by
    simpa using hn.isUnit_add_one
  have hx' : IsUnit x := isUnit_of_mul_isUnit_left hu
  refine ⟨hx'.unit, Units.ext ?_⟩
  change Ideal.Quotient.mk I (↑hx'.unit : B) = ↑u
  rw [IsUnit.unit_spec, hx]

private theorem formallySmooth_monoidAlgebra {R X : Type u} [CommRing R] [AddCommGroup X]
    [Module.Free ℤ X] : Algebra.FormallySmooth R (MonoidAlgebra R (Multiplicative X)) := by
  let b := Module.Free.chooseBasis ℤ X
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI f
  let q := Ideal.Quotient.mkₐ R I
  let w : Multiplicative X →* (B ⧸ I)ˣ :=
    IsUnit.liftRight (f.toMonoidHom.comp (MonoidAlgebra.of R (Multiplicative X)))
      (fun x => (Group.isUnit x).map (f.toMonoidHom.comp (MonoidAlgebra.of R (Multiplicative X))))
  have hu (i : Module.Free.ChooseBasisIndex ℤ X) :=
    lift_unit_of_square_zero I hI (w (Multiplicative.ofAdd (b i)))
  let a : X →ₗ[ℤ] Additive Bˣ :=
    b.constr ℤ (fun i => Additive.ofMul (hu i).choose)
  let v : Multiplicative X →* Bˣ := a.toAddMonoidHom.toMultiplicative
  have hv : (Units.map (Ideal.Quotient.mk I).toMonoidHom).comp v = w := by
    have hw : ((Units.map (Ideal.Quotient.mk I).toMonoidHom).comp v).toAdditive.toIntLinearMap =
        w.toAdditive.toIntLinearMap := by
      apply b.ext
      intro i
      change Additive.ofMul ((Units.map (Ideal.Quotient.mk I).toMonoidHom) (v (Multiplicative.ofAdd (b i)))) =
        Additive.ofMul (w (Multiplicative.ofAdd (b i)))
      change Additive.ofMul ((Units.map (Ideal.Quotient.mk I).toMonoidHom) (Additive.toMul (a (b i)))) = _
      rw [Module.Basis.constr_basis]
      exact congrArg Additive.ofMul (hu i).choose_spec
    apply MonoidHom.ext
    intro x
    exact congrArg Additive.toMul (LinearMap.congr_fun hw (Multiplicative.toAdd x))
  refine ⟨MonoidAlgebra.lift R B _ ((Units.coeHom B).comp v), ?_⟩
  apply MonoidAlgebra.algHom_ext
  · intro x
    change q ((MonoidAlgebra.lift R B _ ((Units.coeHom B).comp v)) (MonoidAlgebra.of R _ x)) = _
    rw [MonoidAlgebra.lift_of]
    exact congrArg Units.val (DFunLike.congr_fun hv x)
  · exact Subsingleton.elim _ _


end RelativeDifferentials

section RelativeOpen

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem injective_on_geometric_points {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (CommRingCat.of K) ⟶ S),
      IsOpenImmersion ((Over.pullback a).map f).left)
    {K : Type u} [Field K] [IsAlgClosed K]
    {p q : Spec (CommRingCat.of K) ⟶ X.left} (he : p ≫ f.left = q ≫ f.left) :
    p = q := by
  let a := p ≫ X.hom
  let F := Over.pullback a
  have hq : q ≫ X.hom = a := by
    rw [← Over.w f, ← Category.assoc, ← he, Category.assoc, Over.w]
  let p' : Spec (CommRingCat.of K) ⟶ (F.obj X).left :=
    pullback.lift p (𝟙 _) (by simp [a])
  let q' : Spec (CommRingCat.of K) ⟶ (F.obj X).left :=
    pullback.lift q (𝟙 _) (by simpa using hq)
  letI : IsOpenImmersion (F.map f).left := h K a
  have he' : p' ≫ (F.map f).left = q' ≫ (F.map f).left := by
    apply pullback.hom_ext
    · simpa [p', q', F] using he
    · simp [p', q', F]
  have h' := (cancel_mono (F.map f).left).mp he'
  simpa [p', q'] using congrArg (fun z => z ≫ pullback.fst X.hom a) h'

private theorem universallyInjective_of_geometricFibres {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (CommRingCat.of K) ⟶ S),
      IsOpenImmersion ((Over.pullback a).map f).left) : UniversallyInjective f.left := by
  apply (UniversallyInjective.iff_diagonal f.left).mpr
  apply surjective_of_liftsGeometricPoints
  intro K _ _ p
  have hh : p ≫ pullback.fst f.left f.left = p ≫ pullback.snd f.left f.left :=
    injective_on_geometric_points f h (by rw [Category.assoc, Category.assoc, pullback.condition])
  refine ⟨p ≫ pullback.fst _ _, ?_⟩
  apply pullback.hom_ext
  · simp
  · simpa using hh

private theorem ringEtale_of_geometricFibres {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Smooth R A] [Algebra.Smooth R B] (f : A →ₐ[R] B)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      IsOpenImmersion (spectrumOfAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) f)).left) :
    f.toRingHom.Etale := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => (f.commutes r).symm)
  have hdiff : Function.Bijective (KaehlerDifferential.mapBaseChange R A B) := by
    apply bijective_of_geometric_extensions (R := R)
    intro K _ _ _
    apply geometric_differential_comparison
    haveI : IsOpenImmersion (spectrumOfAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) f)).left := h K
    have he : (Algebra.TensorProduct.map (AlgHom.id K K) f).toRingHom.Etale :=
      (HasRingHomProperty.Spec_iff (P := @Etale)
        (φ := CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) f).toRingHom)).mp
        (inferInstanceAs (Etale
          (spectrumOfAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) f)).left))
    exact he.toAlgebra.formallyEtale
  exact ⟨formallyEtale_of_differentials hdiff,
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A B⟩

private theorem etale_of_affine_geometricFibres {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] {W : OverBase R} [IsAffine W.left]
    [Smooth W.hom] [Algebra.Smooth R A]
    (i : W ⟶ (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A)))
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      IsOpenImmersion ((changeOfBase K).map i).left) : Etale i.left := by
  obtain ⟨C, ⟨e⟩⟩ := essImage_algSpec.mpr (show IsAffine W.left from inferInstance)
  let f := ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage (e.hom ≫ i)).unop.hom
  have he : spectrumOfAlgHom f = e.hom ≫ i := algSpec.fullyFaithful.map_preimage _
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R C.unop))) := by
    rw [← algSpec_obj_hom C, ← Over.w e.hom]
    infer_instance
  haveI : Algebra.Smooth R C.unop := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)
  have hf (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] :
      IsOpenImmersion (spectrumOfAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) f)).left := by
    haveI : IsOpenImmersion ((changeOfBase K).map i).left := h K
    have hcomm := congrArg Over.Hom.left (fibreSpecIso_natural K f)
    simp only [Over.comp_left, he, Functor.map_comp] at hcomm
    haveI : IsIso ((fibreSpecIso (R := R) K C.unop).inv.left) := (Over.forget _).map_isIso (fibreSpecIso (R := R) K C.unop).inv
    haveI : IsIso ((fibreSpecIso (R := R) K A).inv.left) := (Over.forget _).map_isIso (fibreSpecIso (R := R) K A).inv
    haveI : IsIso ((changeOfBase (R := R) K).map e.hom).left :=
      ((changeOfBase (R := R) K) ⋙ Over.forget _).map_isIso e.hom
    apply (MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion) _
      (fibreSpecIso (R := R) K A).inv.left).mp
    rw [← hcomm]
    haveI : IsOpenImmersion (fibreSpecIso (R := R) K C.unop).inv.left := .of_isIso _
    haveI : IsOpenImmersion ((changeOfBase (R := R) K).map e.hom).left := .of_isIso _
    infer_instance
  have hEtale : Etale (spectrumOfAlgHom f).left :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (ringEtale_of_geometricFibres f hf)
  rw [he, Over.comp_left, MorphismProperty.cancel_left_of_respectsIso (P := @Etale)] at hEtale
  exact hEtale

private theorem open_of_etale_and_geometricFibres {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [Etale f.left]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (CommRingCat.of K) ⟶ S),
      IsOpenImmersion ((Over.pullback a).map f).left) : IsOpenImmersion f.left := by
  letI : UniversallyInjective f.left := universallyInjective_of_geometricFibres f h
  haveI : Surjective (pullback.diagonal f.left) :=
    (UniversallyInjective.iff_diagonal f.left).mp inferInstance
  haveI : IsIso (pullback.diagonal f.left) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  letI : Mono f.left := (pullback.isIso_diagonal_iff f.left).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono f.left

private theorem smooth_product {S : Scheme.{u}} (X Y : Over S)
    [Smooth X.hom] [Smooth Y.hom] : Smooth (X ⊗ Y).hom := by
  haveI : Smooth (snd X Y).left :=
    MorphismProperty.of_isPullback (overProduct_isPullback X Y) inferInstance
  rw [← Over.w (snd X Y)]
  infer_instance

private theorem smooth_lineProduct {R : Type u} [CommRing R] {I : Type u} (l : List I) :
    Smooth (lineProduct R l).hom := by
  induction l with
  | nil => change Smooth (𝟙 (Spec (CommRingCat.of R))); infer_instance
  | cons i l ih =>
    haveI : Algebra.Smooth R (Polynomial R) := ⟨inferInstance, inferInstance⟩
    haveI : Smooth (affineLine R).hom := by
      change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R))))
      exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
        (RingHom.smooth_algebraMap.mpr ‹Algebra.Smooth R (Polynomial R)›)
    exact smooth_product (affineLine R) (lineProduct R l)

end RelativeOpen

section IntegralCell

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000 in
/-- The marked ordered cell is an affine open subscheme and differences of two
cell elements give a smooth faithfully flat cover. -/
theorem integralRelativeCell : Specs.IntegralRelativeCell.Statement.{u} := by
  intro D A _ _ t x hpA hsA ht _ hf negative positive hn hp
  let R := IntegralRing.{u}
  let X := Multiplicative D.X
  let T := (HopfSpectrum R (MonoidAlgebra R X)).X
  let G := HopfSpectrum R A
  let W := lineProduct R negative ⊗ (T ⊗ lineProduct R positive)
  let i : W ⟶ G.X := cellMap t x negative positive
  haveI : Smooth G.X.hom := hsA
  haveI : Algebra.Smooth R A := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsA)
  haveI : IsNoetherianRing R := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  haveI : Algebra.FinitePresentation R A := hpA
  haveI : Algebra.FiniteType R (MonoidAlgebra R X) :=
    Algebra.FiniteType.of_surjective t.toAlgHom ht
  haveI : Algebra.FinitePresentation R (MonoidAlgebra R X) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Module.Free ℤ D.X := D.freeX
  haveI : Algebra.FormallySmooth R (MonoidAlgebra R X) := formallySmooth_monoidAlgebra
  haveI : Algebra.Smooth R (MonoidAlgebra R X) := ⟨inferInstance, inferInstance⟩
  haveI : Smooth T.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (MonoidAlgebra R X))))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr ‹Algebra.Smooth R (MonoidAlgebra R X)›)
  haveI : Smooth (lineProduct R negative).hom := smooth_lineProduct negative
  haveI : Smooth (lineProduct R positive).hom := smooth_lineProduct positive
  haveI : Smooth (T ⊗ lineProduct R positive).hom := smooth_product _ _
  haveI : Smooth W.hom := smooth_product _ _
  haveI : IsAffine T.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra R X))))
  haveI : IsAffine (lineProduct R negative).left := affine_lineProduct negative
  haveI : IsAffine (lineProduct R positive).left := affine_lineProduct positive
  haveI : IsAffine (T ⊗ lineProduct R positive).left := affine_product _ _
  haveI : IsAffine W.left := affine_product _ _
  have hf' (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] :
      IsOpenImmersion ((changeOfBase K).map i).left := by
    obtain ⟨F, hF⟩ := hf K
    exact fibre_open_cell t x F hF negative positive hn hp
  haveI : Etale i.left := etale_of_affine_geometricFibres i hf'
  have hg (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) :
      (∃ b : Algebra R K, @changeOfBase R _ K _ b = Over.pullback a) := by
    let f := (Spec.fullyFaithful.preimage a).unop
    let b : Algebra R K := f.hom.toAlgebra
    refine ⟨b, ?_⟩
    have h : Spec.map (CommRingCat.ofHom (@algebraMap R K _ _ b)) = a :=
      Spec.fullyFaithful.map_preimage a
    change Over.pullback (Spec.map (CommRingCat.ofHom (@algebraMap R K _ _ b))) = Over.pullback a
    rw [h]
  have hgf (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) :
      IsOpenImmersion ((Over.pullback a).map i).left := by
    obtain ⟨b, hb⟩ := hg K a
    rw [← hb]
    letI : Algebra R K := b
    exact hf' K
  haveI : IsOpenImmersion i.left := open_of_etale_and_geometricFibres i hgf
  haveI : Smooth (cellDivision G i).left := cellDivision_smooth G i
  let w : 𝟙_ (OverBase R) ⟶ W :=
    lift (zeroParameters negative) (lift (1 : 𝟙_ (OverBase R) ⟶ T) (zeroParameters positive))
  haveI : Surjective (cellDivision G i).left := cellDivision_surjective G i w fun K _ _ a => by
    obtain ⟨b, hb⟩ := hg K a
    rw [← hb]
    letI : Algebra R K := b
    obtain ⟨F, _⟩ := hf K
    exact integral_fibre_irreducible F
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    faithfullyFlatCellCover_of_smooth_surjective i⟩

end IntegralCell

end

end LinearAlgebraicGroups.Classification.IntegralRelativeCell
