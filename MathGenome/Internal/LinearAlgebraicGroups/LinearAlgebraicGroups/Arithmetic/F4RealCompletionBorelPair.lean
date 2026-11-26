import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.F4RealCompletionBorelPair
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.CharacteristicZeroSmoothness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Arithmetic.F4RealCompletionBorelPair

open _root_.LinearAlgebraicGroups.Specs hiding coordinateMap
open Specs.Arithmetic.F4RealCompletionBorelPair
open Specs.AdjointRepresentation (GroupPoints)
open Specs.GeometricRadicals (IsSplitTorus IsTorus IsMaximalTorus)
open Specs.GeometricBorelConjugacy (IsBorel IsSmoothConnectedSolvable)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

open private coordinateMap coordinateMap_spec specMap_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private affineBaseTerminal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private solvable_iff_sections rationalSections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private lattice_torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private isKBorel_iff_of_isAlgClosed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer

noncomputable section

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

variable {F : Type u} [Field F] {K : Type} [Field K]

private def spectrumPoints {k : Type u} [Field k] (A R : TestAlgebra k) :
    Points ((testSpec k).obj (op A)) R ≃ (A ⟶ R) where
  toFun := coordinateMap
  invFun f := (testSpec k).map f.op
  left_inv := coordinateMap_spec
  right_inv f := by
    apply Quiver.Hom.op_inj
    exact (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective (coordinateMap_spec _)

private theorem spectrumPoints_natural {k : Type u} [Field k] (A : TestAlgebra k)
    {R S : TestAlgebra k} (a : R ⟶ S) (x : Points ((testSpec k).obj (op A)) R) :
    spectrumPoints A S (mapPoints a x) = spectrumPoints A R x ≫ a := by
  apply Quiver.Hom.op_inj
  apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  change (testSpec k).map (coordinateMap (mapPoints a x)).op =
    (testSpec k).map (coordinateMap x ≫ a).op
  rw [coordinateMap_spec, op_comp, Functor.map_comp, coordinateMap_spec]

private theorem spectrum_finiteType {k : Type u} [Field k] (A : TestAlgebra k) :
    LocallyOfFiniteType ((testSpec k).obj (op A)).hom ↔ Algebra.FiniteType k A :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
    (φ := CommRingCat.ofHom (algebraMap k A))).trans RingHom.finiteType_algebraMap

private theorem affinePresentation {k : Type u} [Field k] (X : SchemeOver k)
    [IsAffine X.left] [LocallyOfFiniteType X.hom] :
    ∃ A : TestAlgebra k, Algebra.FiniteType k A ∧ Nonempty ((testSpec k).obj (op A) ≅ X) := by
  obtain ⟨A, ⟨z⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  have hf : LocallyOfFiniteType ((testSpec k).obj A).hom := by
    rw [← Over.w z.hom]
    have : IsIso z.hom.left := (Over.forget _).map_isIso z.hom
    infer_instance
  exact ⟨A.unop, (spectrum_finiteType A.unop).mp hf, ⟨z⟩⟩

private theorem closedImmersion_iff_coordinateSurjective {k : Type u} [Field k]
    {A B : TestAlgebra k} {X Y : SchemeOver k} (z : (testSpec k).obj (op A) ≅ X)
    (w : (testSpec k).obj (op B) ≅ Y) (f : X ⟶ Y) :
    Function.Surjective (coordinateMap (z.hom ≫ f ≫ w.inv)).hom ↔ IsClosedImmersion f.left := by
  let a := coordinateMap (z.hom ≫ f ≫ w.inv)
  let b := CommRingCat.ofHom a.hom.toRingHom
  have he : Spec.map b = z.hom.left ≫ f.left ≫ w.inv.left := by
    have hh := congrArg Over.Hom.left (coordinateMap_spec (z.hom ≫ f ≫ w.inv))
    rw [algSpec_map_left, Over.comp_left, Over.comp_left] at hh
    exact hh
  letI : IsIso z.hom.left := (Over.forget _).map_isIso z.hom
  letI : IsIso w.inv.left := (Over.forget _).map_isIso w.inv
  have hi : IsClosedImmersion (Spec.map b) ↔ IsClosedImmersion f.left := by
    rw [he, ← Category.assoc,
      MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)
        (z.hom.left ≫ f.left) w.inv.left,
      MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) z.hom.left f.left]
  exact ⟨fun h => hi.mp (IsClosedImmersion.spec_of_surjective b h),
    fun h => specMap_surjective b (hi.mpr h)⟩

section TestAlgebras

variable (e : F ≃+* K) (L : TestAlgebra K ⥤ TestAlgebra F)
  (r : ∀ R : TestAlgebra K, L.obj R ≃+* R)
  (hr : ∀ (R : TestAlgebra K) (x : F), r R (algebraMap F (L.obj R) x) = algebraMap K R (e x))
  (hn : ∀ {R S : TestAlgebra K} (a : R ⟶ S) (x : L.obj R),
    r S ((L.map a).hom x) = a.hom (r R x))

include hr in
private theorem scalar_symm (R : TestAlgebra K) (x : K) :
    (r R).symm (algebraMap K R x) = algebraMap F (L.obj R) (e.symm x) := by
  apply (r R).injective
  rw [RingEquiv.apply_symm_apply, hr, e.apply_symm_apply]

private def testFullyFaithful : L.FullyFaithful where
  preimage {R S} f := CommAlgCat.ofHom
    { toRingHom := ((r S).toRingHom.comp f.hom.toRingHom).comp (r R).symm.toRingHom
      commutes' := fun x => by
        change r S (f.hom ((r R).symm (algebraMap K R x))) = algebraMap K S x
        rw [scalar_symm e L r hr, f.hom.commutes, hr, e.apply_symm_apply] }
  map_preimage {R S} f := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply (r S).injective
    rw [hn]
    change r S (f.hom ((r R).symm (r R x))) = r S (f.hom x)
    rw [RingEquiv.symm_apply_apply]
  preimage_map {R S} f := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change r S ((L.map f).hom ((r R).symm x)) = f.hom x
    rw [hn, RingEquiv.apply_symm_apply]

include hr in
private theorem testEssentialImage (A : TestAlgebra F) (hA : Algebra.FiniteType F A) :
    ∃ R : TestAlgebra K, Algebra.FiniteType K R ∧ Nonempty (L.obj R ≅ A) := by
  have hF : (algebraMap F A).FiniteType := RingHom.finiteType_algebraMap.mpr hA
  have hK : ((algebraMap F A).comp e.symm.toRingHom).FiniteType :=
    hF.comp (RingHom.FiniteType.of_surjective _ e.symm.surjective)
  obtain ⟨P, b, hb⟩ := hK.exists_smallRepr
  let R := P.eval.obj
  let j : L.obj R ≃+* A := (r R).trans b
  let a : L.obj R ≃ₐ[F] A := AlgEquiv.ofRingEquiv (f := j) (fun x => by
    have h := DFunLike.congr_fun hb (e x)
    change algebraMap F A (e.symm (e x)) = b (algebraMap K R (e x)) at h
    change b (r R (algebraMap F (L.obj R) x)) = algebraMap F A x
    rw [hr, ← h, e.symm_apply_apply])
  exact ⟨R, inferInstance, ⟨CommAlgCat.isoMk a⟩⟩

include hr in
private theorem liftedPresentation (X : SchemeOver F) [IsAffine X.left] [LocallyOfFiniteType X.hom] :
    ∃ R : TestAlgebra K, Nonempty ((testSpec F).obj (op (L.obj R)) ≅ X) := by
  obtain ⟨A, hA, ⟨z⟩⟩ := affinePresentation X
  obtain ⟨R, _, ⟨j⟩⟩ := testEssentialImage e L r hr A hA
  exact ⟨R, ⟨(testSpec F).mapIso j.op.symm ≪≫ z⟩⟩

include hr in
private theorem hom_ext_of_liftedPoints {X Y : SchemeOver F} [IsAffine X.left] [LocallyOfFiniteType X.hom]
    {f g : X ⟶ Y} (h : ∀ R : TestAlgebra K, ∀ p : Points X (L.obj R), p ≫ f = p ≫ g) : f = g := by
  obtain ⟨R, ⟨z⟩⟩ := liftedPresentation e L r hr X
  exact (cancel_epi z.hom).mp (h R z.hom)

end TestAlgebras

section RestrictedYoneda

variable {L : TestAlgebra K ⥤ TestAlgebra F} (ff : L.FullyFaithful)

include ff in
private theorem lifted_point_map {X Y : SchemeOver F} {A : TestAlgebra K}
    (z : (testSpec F).obj (op (L.obj A)) ≅ X)
    (p : ∀ R : TestAlgebra K, Points X (L.obj R) → Points Y (L.obj R))
    (hp : ∀ {R S : TestAlgebra K} (a : R ⟶ S) (x : Points X (L.obj R)),
      p S (mapPoints (L.map a) x) = mapPoints (L.map a) (p R x)) :
    ∀ R (x : Points X (L.obj R)), p R x = x ≫ z.inv ≫ p A z.hom := by
  intro R x
  let a := ff.preimage (coordinateMap (x ≫ z.inv))
  have ha : (testSpec F).map (L.map a).op = x ≫ z.inv := by
    rw [ff.map_preimage, coordinateMap_spec]
  have h := hp a z.hom
  change p R ((testSpec F).map (L.map a).op ≫ z.hom) =
    (testSpec F).map (L.map a).op ≫ p A z.hom at h
  simpa only [ha, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

include ff in
private theorem matchedPresentation {X : GroupScheme F} {Y : GroupScheme K}
    {B : TestAlgebra K} (w : (testSpec K).obj (op B) ≅ Y.X)
    (p : PointComparison L X Y) (A : TestAlgebra K)
    (z : (testSpec F).obj (op (L.obj A)) ≅ X.X) :
    ∃ z' : (testSpec F).obj (op (L.obj B)) ≅ X.X, z'.hom = p.equiv B w.hom := by
  let x : Points Y.X A := (p.equiv A).symm z.hom
  let a : B ⟶ A := coordinateMap (x ≫ w.inv)
  let f : (testSpec F).obj (op (L.obj B)) ⟶ X.X := p.equiv B w.hom
  let g : X.X ⟶ (testSpec F).obj (op (L.obj B)) := z.inv ≫ (testSpec F).map (L.map a).op
  have ha : (testSpec K).map a.op ≫ w.hom = x := by
    simp only [a, coordinateMap_spec, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hgf : g ≫ f = 𝟙 X.X := by
    have h := p.natural a w.hom
    change p.equiv A ((testSpec K).map a.op ≫ w.hom) = (testSpec F).map (L.map a).op ≫ f at h
    rw [ha, show p.equiv A x = z.hom from (p.equiv A).apply_symm_apply _] at h
    simp only [g, Category.assoc, ← h, Iso.inv_hom_id]
  let b : A ⟶ B := ff.preimage (coordinateMap (f ≫ z.inv))
  have hb : (testSpec F).map (L.map b).op = f ≫ z.inv := by
    rw [ff.map_preimage, coordinateMap_spec]
  have hxb : mapPoints b x = w.hom := by
    apply (p.equiv B).injective
    rw [p.natural b x, show p.equiv A x = z.hom from (p.equiv A).apply_symm_apply _]
    change (testSpec F).map (L.map b).op ≫ z.hom = f
    simp only [hb, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hab : a ≫ b = 𝟙 B := by
    apply Quiver.Hom.op_inj
    apply (algSpec.fullyFaithful (R := CommRingCat.of K)).map_injective
    have hId : (testSpec K).map (𝟙 B).op = 𝟙 ((testSpec K).obj (op B)) :=
      (testSpec K).map_id (op B)
    rw [op_comp, Functor.map_comp, hId]
    apply (cancel_mono w.hom).mp
    rw [Category.assoc, ha]
    exact hxb.trans (Category.id_comp _).symm
  have hfg : f ≫ g = 𝟙 _ := by
    rw [show f ≫ g = (f ≫ z.inv) ≫ (testSpec F).map (L.map a).op from (Category.assoc ..).symm,
      ← hb, ← Functor.map_comp, ← op_comp, ← Functor.map_comp, hab, L.map_id]
    exact (testSpec F).map_id (op (L.obj B))
  exact ⟨⟨f, g, hfg, hgf⟩, rfl⟩

end RestrictedYoneda

private def pointHom {k : Type u} [Field k] {X Y : GroupScheme k}
    (f : X ⟶ Y) (R : TestAlgebra k) : GroupPoints X R →* GroupPoints Y R :=
  (((groupPointsFunctor k).map f).app R).hom

private theorem pointHom_natural {k : Type u} [Field k] {X Y : GroupScheme k} (f : X ⟶ Y)
    {R S : TestAlgebra k} (a : R ⟶ S) (x : GroupPoints X R) :
    pointHom f S (mapPoints a x) = mapPoints a (pointHom f R x) := by
  change ((testSpec k).map a.op ≫ x) ≫ f.hom.hom = (testSpec k).map a.op ≫ x ≫ f.hom.hom
  exact Category.assoc ..

private theorem comparison_natural_inv {L : TestAlgebra K ⥤ TestAlgebra F}
    {X : GroupScheme F} {Y : GroupScheme K} (p : PointComparison L X Y)
    {R S : TestAlgebra K} (a : R ⟶ S) (x : GroupPoints X (L.obj R)) :
    (p.equiv S).symm (mapPoints (L.map a) x) = mapPoints a ((p.equiv R).symm x) := by
  apply (p.equiv S).injective
  rw [MulEquiv.apply_symm_apply, p.natural, MulEquiv.apply_symm_apply]

private theorem compatible_comp {L : TestAlgebra K ⥤ TestAlgebra F}
    {X₁ X₂ X₃ : GroupScheme F} {Y₁ Y₂ Y₃ : GroupScheme K}
    {p₁ : PointComparison L X₁ Y₁} {p₂ : PointComparison L X₂ Y₂}
    {p₃ : PointComparison L X₃ Y₃} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}
    {i : Y₁ ⟶ Y₂} {j : Y₂ ⟶ Y₃}
    (hf : Compatible p₂ p₁ f i) (hg : Compatible p₃ p₂ g j) :
    Compatible p₃ p₁ (f ≫ g) (i ≫ j) := by
  intro R x
  change p₃.equiv R (x ≫ i.hom.hom ≫ j.hom.hom) =
    p₁.equiv R x ≫ f.hom.hom ≫ g.hom.hom
  rw [← Category.assoc, hg, hf, Category.assoc]

private theorem compatible_unique_small {L : TestAlgebra K ⥤ TestAlgebra F}
    {X X' : GroupScheme F} {Y Y' : GroupScheme K} (hY : IsAffine Y.X.left)
    {p : PointComparison L X Y} {q : PointComparison L X' Y'} {f : X ⟶ X'}
    {g₁ g₂ : Y ⟶ Y'} (h₁ : Compatible q p f g₁) (h₂ : Compatible q p f g₂) :
    g₁ = g₂ := by
  apply (groupHomEquiv Y Y' hY).injective
  ext R x
  exact (q.equiv R).injective ((h₁ R x).trans (h₂ R x).symm)

private theorem descendHom {L : TestAlgebra K ⥤ TestAlgebra F}
    {X X' : GroupScheme F} {Y Y' : GroupScheme K} (hY : IsAffine Y.X.left)
    (p : PointComparison L X Y) (q : PointComparison L X' Y') (f : X ⟶ X') :
    ∃ g : Y ⟶ Y', Compatible q p f g := by
  let α : (groupPointsFunctor K).obj Y ⟶ (groupPointsFunctor K).obj Y' :=
    { app := fun R => GrpCat.ofHom ((q.equiv R).symm.toMonoidHom.comp
        ((pointHom f (L.obj R)).comp (p.equiv R).toMonoidHom))
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro x
        change (q.equiv S).symm (pointHom f (L.obj S) (p.equiv S (mapPoints a x))) =
          mapPoints a ((q.equiv R).symm (pointHom f (L.obj R) (p.equiv R x)))
        rw [p.natural, pointHom_natural, comparison_natural_inv] }
  let g := (groupHomEquiv Y Y' hY).symm α
  have hg := (groupHomEquiv Y Y' hY).apply_symm_apply α
  change (groupPointsFunctor K).map g = α at hg
  refine ⟨g, fun R x => ?_⟩
  have hx := congrArg (fun β : (groupPointsFunctor K).obj Y ⟶ (groupPointsFunctor K).obj Y' =>
    (β.app R).hom x) hg
  change x ≫ g.hom.hom = (q.equiv R).symm (p.equiv R x ≫ f.hom.hom) at hx
  change q.equiv R (x ≫ g.hom.hom) = _
  exact (congrArg (q.equiv R) hx).trans ((q.equiv R).apply_symm_apply _)

section Morphisms

variable {e : F ≃+* K} {L : TestAlgebra K ⥤ TestAlgebra F}
  {r : ∀ R : TestAlgebra K, L.obj R ≃+* R}
  (hr : ∀ (R : TestAlgebra K) (x : F), r R (algebraMap F (L.obj R) x) = algebraMap K R (e x))
  (hn : ∀ {R S : TestAlgebra K} (a : R ⟶ S) (x : L.obj R),
    r S ((L.map a).hom x) = a.hom (r R x))

include hr in
private theorem compatible_unique_large {X X' : AffineAlgebraicGroup F}
    {Y Y' : GroupScheme K}
    {p : PointComparison L X.val Y} {q : PointComparison L X'.val Y'}
    {f₁ f₂ : X.val ⟶ X'.val} {g : Y ⟶ Y'}
    (h₁ : Compatible q p f₁ g) (h₂ : Compatible q p f₂ g) :
    f₁ = f₂ := by
  letI := X.prop.1
  letI := X.prop.2.1
  apply Grp.hom_ext
  apply hom_ext_of_liftedPoints e L r hr
  intro R x
  obtain ⟨y, rfl⟩ := (p.equiv R).surjective x
  exact (h₁ R y).symm.trans (h₂ R y)

include hr hn in
private theorem liftGroupHom (X X' : AffineAlgebraicGroup F)
    (α : L ⋙ (groupPointsFunctor F).obj X.val ⟶ L ⋙ (groupPointsFunctor F).obj X'.val) :
    ∃ f : X.val ⟶ X'.val, ∀ (R : TestAlgebra K) (x : GroupPoints X.val (L.obj R)),
      x ≫ f.hom.hom = α.app R x := by
  letI := X.prop.1
  letI := X.prop.2.1
  obtain ⟨A, ⟨z⟩⟩ := liftedPresentation e L r hr X.val.X
  let f := z.inv ≫ α.app A z.hom
  have hf (R : TestAlgebra K) (x : GroupPoints X.val (L.obj R)) :
      α.app R x = x ≫ f :=
    lifted_point_map (testFullyFaithful e L r hr hn) z (fun R x => α.app R x)
      (fun a x => DFunLike.congr_fun (congrArg GrpCat.Hom.hom (α.naturality a)) x) R x
  have hmul (R : TestAlgebra K) (x y : GroupPoints X.val (L.obj R)) :
      (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
    rw [← hf, ← hf, ← hf]
    exact (α.app R).hom.map_mul x y
  haveI : IsMonHom f := by
    constructor
    · haveI : IsAffine ((𝟙_ (SchemeOver F)).left) :=
        inferInstanceAs (IsAffine (Spec (CommRingCat.of F)))
      haveI : LocallyOfFiniteType ((𝟙_ (SchemeOver F)).hom) :=
        inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of F))))
      apply hom_ext_of_liftedPoints e L r hr
      intro R x
      rw [show x = toUnit _ from toUnit_unique _ _]
      change (1 : GroupPoints X.val (L.obj R)) ≫ f = 1
      rw [← hf]
      exact (α.app R).hom.map_one
    · haveI : IsAffine (X.val.X ⊗ X.val.X).left := by
        change IsAffine (Limits.pullback X.val.X.hom X.val.X.hom)
        infer_instance
      haveI : LocallyOfFiniteType (X.val.X ⊗ X.val.X).hom := by
        change LocallyOfFiniteType (Limits.pullback.fst X.val.X.hom X.val.X.hom ≫ X.val.X.hom)
        infer_instance
      apply hom_ext_of_liftedPoints e L r hr
      intro R p
      let x := p ≫ fst X.val.X X.val.X
      let y := p ≫ snd X.val.X X.val.X
      calc
        p ≫ μ[X.val.X] ≫ f = (x * y) ≫ f := by
          simp only [x, y, Hom.mul_def, lift_comp_fst_snd, Category.assoc]
        _ = (x ≫ f) * (y ≫ f) := hmul R x y
        _ = p ≫ (f ⊗ₘ f) ≫ μ[X'.val.X] := by
          have h : lift (x ≫ f) (y ≫ f) = p ≫ (f ⊗ₘ f) := by
            apply CartesianMonoidalCategory.hom_ext
            · simp only [x, lift_fst, Category.assoc, tensorHom_fst]
            · simp only [y, lift_snd, Category.assoc, tensorHom_snd]
          simp only [Hom.mul_def, h, Category.assoc]
  exact ⟨Grp.homMk f, fun R x => (hf R x).symm⟩

include hr hn in
private theorem liftHom {X X' : AffineAlgebraicGroup F} {Y Y' : GroupScheme K}
    (p : PointComparison L X.val Y) (q : PointComparison L X'.val Y') (g : Y ⟶ Y') :
    ∃ f : X.val ⟶ X'.val, Compatible q p f g := by
  let α : L ⋙ (groupPointsFunctor F).obj X.val ⟶ L ⋙ (groupPointsFunctor F).obj X'.val :=
    { app := fun R => GrpCat.ofHom ((q.equiv R).toMonoidHom.comp
        ((pointHom g R).comp (p.equiv R).symm.toMonoidHom))
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro x
        change q.equiv S (pointHom g S ((p.equiv S).symm (mapPoints (L.map a) x))) =
          mapPoints (L.map a) (q.equiv R (pointHom g R ((p.equiv R).symm x)))
        rw [comparison_natural_inv, pointHom_natural, q.natural] }
  obtain ⟨f, hf⟩ := liftGroupHom hr hn X X' α
  refine ⟨f, fun R x => ?_⟩
  have hx := hf R (p.equiv R x)
  change p.equiv R x ≫ f.hom.hom =
    q.equiv R ((p.equiv R).symm (p.equiv R x) ≫ g.hom.hom) at hx
  rw [MulEquiv.symm_apply_apply] at hx
  exact hx.symm

include hr hn in
private theorem comparison_spectra {X : AffineAlgebraicGroup F} {Y : AffineAlgebraicGroup K}
    (p : PointComparison L X.val Y.val) :
    ∃ (B : TestAlgebra K) (w : (testSpec K).obj (op B) ≅ Y.val.X)
      (z : (testSpec F).obj (op (L.obj B)) ≅ X.val.X), z.hom = p.equiv B w.hom := by
  letI := X.prop.1
  letI := X.prop.2.1
  letI := Y.prop.1
  letI := Y.prop.2.1
  obtain ⟨B, _, ⟨w⟩⟩ := affinePresentation Y.val.X
  obtain ⟨A, ⟨z⟩⟩ := liftedPresentation e L r hr X.val.X
  obtain ⟨z', hz'⟩ := matchedPresentation (testFullyFaithful e L r hr hn) w p A z
  exact ⟨B, w, z', hz'⟩

include hr hn in
private theorem compatible_closedImmersion {X X' : AffineAlgebraicGroup F}
    {Y Y' : AffineAlgebraicGroup K} {p : PointComparison L X.val Y.val}
    {q : PointComparison L X'.val Y'.val} {f : X.val ⟶ X'.val} {g : Y.val ⟶ Y'.val}
    (h : Compatible q p f g) :
    IsClosedImmersion f.hom.hom.left ↔ IsClosedImmersion g.hom.hom.left := by
  obtain ⟨B, w, z, hz⟩ := comparison_spectra hr hn p
  obtain ⟨B', w', z', hz'⟩ := comparison_spectra hr hn q
  let a : B' ⟶ B := coordinateMap (w.hom ≫ g.hom.hom ≫ w'.inv)
  have ha : (testSpec K).map a.op ≫ w'.hom = w.hom ≫ g.hom.hom := by
    rw [show (testSpec K).map a.op = _ from coordinateMap_spec _]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hf : (testSpec F).map (L.map a).op ≫ z'.hom = z.hom ≫ f.hom.hom := by
    rw [hz', hz]
    exact (q.natural a w'.hom).symm.trans ((congrArg (q.equiv B) ha).trans (h B w.hom))
  have hf' : coordinateMap (z.hom ≫ f.hom.hom ≫ z'.inv) = L.map a := by
    apply Quiver.Hom.op_inj
    apply (algSpec.fullyFaithful (R := CommRingCat.of F)).map_injective
    rw [coordinateMap_spec, ← Category.assoc, ← hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← closedImmersion_iff_coordinateSurjective z z',
    ← closedImmersion_iff_coordinateSurjective w w', hf']
  change Function.Surjective (L.map a).hom ↔ Function.Surjective a.hom
  have hmap : r B ∘ (L.map a).hom = a.hom ∘ r B' := funext (hn a)
  exact (Function.Surjective.of_comp_iff' (r B).bijective _).symm.trans
    (hmap ▸ Function.Surjective.of_comp_iff _ (r B').surjective)

end Morphisms

section Models

variable {k : Type u} [Field k] {X : SchemeOver k}

private def transportLaw (D : TestAlgebra k ⥤ GrpCat.{v})
    (p : ∀ R, Points X R ≃ D.obj R)
    (hn : ∀ {R S} (a : R ⟶ S) (x : Points X R), p S (mapPoints a x) = D.map a (p R x)) :
    NaturalGroupLaw X where
  group := fun R => (p R).group
  map_one := by
    intro R S a
    apply (p S).injective
    rw [hn]
    change D.map a (p R ((p R).symm 1)) = p S ((p S).symm 1)
    simp
  map_mul := by
    intro R S a x y
    apply (p S).injective
    rw [hn]
    change D.map a (p R ((p R).symm (p R x * p R y))) =
      p S ((p S).symm (p S (mapPoints a x) * p S (mapPoints a y)))
    simp only [Equiv.apply_symm_apply, hn, map_mul]

private def realizeGroup (hX : IsAffine X.left) (D : TestAlgebra k ⥤ GrpCat.{v})
    (p : ∀ R, Points X R ≃ D.obj R)
    (hn : ∀ {R S} (a : R ⟶ S) (x : Points X R), p S (mapPoints a x) = D.map a (p R x)) :
    GroupScheme k :=
  letI := (groupLawEquiv X hX).symm (transportLaw D p hn)
  Grp.mk X

private def realizePoints (hX : IsAffine X.left) (D : TestAlgebra k ⥤ GrpCat.{v})
    (p : ∀ R, Points X R ≃ D.obj R)
    (hn : ∀ {R S} (a : R ⟶ S) (x : Points X R), p S (mapPoints a x) = D.map a (p R x))
    (R : TestAlgebra k) : GroupPoints (realizeGroup hX D p hn) R ≃* D.obj R where
  toEquiv := p R
  map_mul' x y := by
    let s := (groupLawEquiv X hX).symm (transportLaw D p hn)
    have hs : inducedGroupLaw X s = transportLaw D p hn :=
      (groupLawEquiv X hX).apply_symm_apply _
    have h := congrArg (fun laws : NaturalGroupLaw X => (laws.group R).mul x y) hs
    change (x * y : GroupPoints (realizeGroup hX D p hn) R) = (p R).symm (p R x * p R y) at h
    exact (congrArg (p R) h).trans ((p R).apply_symm_apply _)

end Models

section ChangeOfField

variable {e : F ≃+* K} {L : TestAlgebra K ⥤ TestAlgebra F}
  {r : ∀ R : TestAlgebra K, L.obj R ≃+* R}
  (hr : ∀ (R : TestAlgebra K) (x : F), r R (algebraMap F (L.obj R) x) = algebraMap K R (e x))
  (hn : ∀ {R S : TestAlgebra K} (a : R ⟶ S) (x : L.obj R),
    r S ((L.map a).hom x) = a.hom (r R x))

include hr hn in
private theorem smallModel (G : AffineAlgebraicGroup F) :
    ∃ H : AffineAlgebraicGroup K, Nonempty (PointComparison L G.val H.val) := by
  letI := G.prop.1
  letI := G.prop.2.1
  obtain ⟨A, hA, ⟨z⟩⟩ := affinePresentation G.val.X
  obtain ⟨B, hB, ⟨j⟩⟩ := testEssentialImage e L r hr A hA
  let w := (testSpec F).mapIso j.op.symm ≪≫ z
  let X := (testSpec K).obj (op B)
  let D := L ⋙ (groupPointsFunctor F).obj G.val
  let ff := testFullyFaithful e L r hr hn
  let p (R : TestAlgebra K) : Points X R ≃ D.obj R :=
    (spectrumPoints B R).trans (ff.homEquiv.trans
      ((spectrumPoints (L.obj B) (L.obj R)).symm.trans
        { toFun := (· ≫ w.hom)
          invFun := (· ≫ w.inv)
          left_inv := by intro x; simp
          right_inv := by intro x; simp }))
  have hp {R S : TestAlgebra K} (a : R ⟶ S) (x : Points X R) :
      p S (mapPoints a x) = D.map a (p R x) := by
    change (testSpec F).map (L.map (spectrumPoints B S (mapPoints a x))).op ≫ w.hom =
      (testSpec F).map (L.map a).op ≫
        (testSpec F).map (L.map (spectrumPoints B R x)).op ≫ w.hom
    rw [spectrumPoints_natural, Functor.map_comp, op_comp, Functor.map_comp, Category.assoc]
  have hX : IsAffine X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))
  let H : AffineAlgebraicGroup K := ⟨realizeGroup hX D p hp, hX,
    (spectrum_finiteType B).mpr hB, by
      change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K B)))
      infer_instance⟩
  exact ⟨H, ⟨⟨realizePoints hX D p hp, hp⟩⟩⟩

private def restrictTest (e : F ≃+* K) (R : TestAlgebra F) : CommAlgCat.{u} K :=
  letI : Algebra K R := ((algebraMap F R).comp e.symm.toRingHom).toAlgebra
  CommAlgCat.of K R

private def restrictMap (e : F ≃+* K) {R S : TestAlgebra F} (a : R ⟶ S) :
    restrictTest e R →ₐ[K] restrictTest e S :=
  ⟨a.hom.toRingHom, fun x => a.hom.commutes (e.symm x)⟩

private def restrictEquiv (R : TestAlgebra K) : R ≃ₐ[K] restrictTest e (L.obj R) :=
  AlgEquiv.ofRingEquiv (f := (r R).symm) (scalar_symm e L r hr R)

private def liftedCoordinateEquiv (B : TestAlgebra K) (R : TestAlgebra F) :
    (L.obj B ⟶ R) ≃ WithConv (B →ₐ[K] restrictTest e R) where
  toFun f := toConv
    { toRingHom := f.hom.toRingHom.comp (r B).symm.toRingHom
      commutes' := fun x => by
        change f.hom ((r B).symm (algebraMap K B x)) = algebraMap F R (e.symm x)
        rw [scalar_symm e L r hr, f.hom.commutes] }
  invFun f := CommAlgCat.ofHom
    { toRingHom := f.ofConv.toRingHom.comp (r B).toRingHom
      commutes' := fun x => by
        change f.ofConv (r B (algebraMap F (L.obj B) x)) = algebraMap F R x
        rw [hr]
        exact (f.ofConv.commutes (e x)).trans (congrArg (algebraMap F R) (e.symm_apply_apply x)) }
  left_inv f := CommAlgCat.hom_ext (AlgHom.ext fun x => congrArg f.hom ((r B).symm_apply_apply x))
  right_inv f := WithConv.ofConv_injective
    (AlgHom.ext fun x => congrArg f.ofConv ((r B).apply_symm_apply x))

/-- Convolution also works when the coefficient algebra has a larger universe. -/
@[instance_reducible]
private def coordinateConvolutionGroup (C : HopfAlgebraCategory K) (R : CommAlgCat.{u} K) :
    Group (WithConv (C →ₐ[K] R)) where
  toMonoid := inferInstance
  inv f := toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom K C))
  inv_mul_cancel f := by
    let s : WithConv (C →ₐ[K] C) := toConv (HopfAlgebra.antipodeAlgHom K C)
    let i : WithConv (C →ₐ[K] C) := toConv (AlgHom.id K C)
    have hi : s * i = 1 := AlgHom.antipode_id_cancel
    have h := AlgHom.comp_convMul_distrib f.ofConv s i
    rw [hi] at h
    apply WithConv.ofConv_injective
    refine h.symm.trans ?_
    apply AlgHom.ext
    intro a
    exact f.ofConv.commutes (Coalgebra.counit a)

private def largeConvolution (e : F ≃+* K) (C : HopfAlgebraCategory K) :
    TestAlgebra F ⥤ GrpCat.{u} where
  obj R := letI := coordinateConvolutionGroup C (restrictTest e R)
    GrpCat.of (WithConv (C →ₐ[K] restrictTest e R))
  map {R S} a := by
    letI := coordinateConvolutionGroup C (restrictTest e R)
    letI := coordinateConvolutionGroup C (restrictTest e S)
    exact GrpCat.ofHom
      { toFun := fun f => toConv ((restrictMap e a).comp f.ofConv)
        map_one' := WithConv.ofConv_injective (AlgHom.ext fun x =>
          (restrictMap e a).commutes (Coalgebra.counit x))
        map_mul' := fun f g => WithConv.ofConv_injective (AlgHom.comp_convMul_distrib (restrictMap e a) f g) }
  map_id R := by
    apply GrpCat.ext
    intro f
    rfl
  map_comp a b := by
    apply GrpCat.ext
    intro f
    rfl

private def liftConvolutionPoints (C : HopfAlgebraCategory K) (R : TestAlgebra K) :
    (convolutionPoints C).obj R ≃* (largeConvolution e C).obj (L.obj R) where
  toFun f := toConv ((restrictEquiv hr R).toAlgHom.comp f.ofConv)
  invFun f := toConv ((restrictEquiv hr R).symm.toAlgHom.comp f.ofConv)
  left_inv f := WithConv.ofConv_injective (AlgHom.ext fun x =>
    (restrictEquiv hr R).symm_apply_apply (f.ofConv x))
  right_inv f := WithConv.ofConv_injective (AlgHom.ext fun x =>
    (restrictEquiv hr R).apply_symm_apply (f.ofConv x))
  map_mul' f g := WithConv.ofConv_injective
    (AlgHom.comp_convMul_distrib (restrictEquiv hr R).toAlgHom f g)

include hr hn in
private theorem liftConvolutionPoints_natural (C : HopfAlgebraCategory K) {R S : TestAlgebra K}
    (a : R ⟶ S) (x : (convolutionPoints C).obj R) :
    liftConvolutionPoints hr C S ((convolutionPoints C).map a x) =
      (largeConvolution e C).map (L.map a) (liftConvolutionPoints hr C R x) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro c
  change (r S).symm (a.hom (x.ofConv c)) = (L.map a).hom ((r R).symm (x.ofConv c))
  apply (r S).injective
  rw [RingEquiv.apply_symm_apply, hn, RingEquiv.apply_symm_apply]

include hr hn in
private theorem largeModel (H : AffineAlgebraicGroup K) :
    ∃ G : AffineAlgebraicGroup F, Nonempty (PointComparison L G.val H.val) := by
  obtain ⟨C, hC, ⟨c⟩⟩ := groupPresentation H
  let B := (forgetHopfAlgebra (k := K)).obj C
  let A := L.obj B
  let X := (testSpec F).obj (op A)
  let D := largeConvolution e C
  let p (R : TestAlgebra F) : Points X R ≃ D.obj R :=
    (spectrumPoints A R).trans (liftedCoordinateEquiv hr B R)
  have hp {R S : TestAlgebra F} (a : R ⟶ S) (x : Points X R) :
      p S (mapPoints a x) = D.map a (p R x) := by
    change liftedCoordinateEquiv hr B S (spectrumPoints A S (mapPoints a x)) = _
    rw [spectrumPoints_natural]
    rfl
  have hX : IsAffine X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hA : Algebra.FiniteType F A := by
    apply RingHom.finiteType_algebraMap.mp
    have h : algebraMap F A = (r B).symm.toRingHom.comp
        ((algebraMap K B).comp e.toRingHom) := by
      ext x : 1
      exact (congrArg (algebraMap F A) (e.symm_apply_apply x).symm).trans
        (scalar_symm e L r hr B (e x)).symm
    rw [h]
    exact ((RingHom.finiteType_algebraMap.mpr hC).comp
      (RingHom.FiniteType.of_surjective _ e.surjective)).comp_surjective (r B).symm.surjective
  let G : AffineAlgebraicGroup F := ⟨realizeGroup hX D p hp, hX,
    (spectrum_finiteType A).mpr hA, by
      change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap F A)))
      infer_instance⟩
  let c' := hopfSpecPointIso C ≪≫ (groupPointsFunctor K).mapIso c
  let q (R : TestAlgebra K) : GroupPoints H.val R ≃* GroupPoints G.val (L.obj R) :=
    ((c'.symm.app R).groupIsoToMulEquiv.trans (liftConvolutionPoints hr C R)).trans
      (realizePoints hX D p hp (L.obj R)).symm
  have hq (R : TestAlgebra K) (x : GroupPoints H.val R) :
      p (L.obj R) (q R x) = liftConvolutionPoints hr C R (c'.inv.app R x) :=
    (realizePoints hX D p hp (L.obj R)).apply_symm_apply _
  refine ⟨G, ⟨⟨q, ?_⟩⟩⟩
  intro R S a x
  apply (p (L.obj S)).injective
  change p (L.obj S) (q S (mapPoints a x)) = p (L.obj S) (mapPoints (L.map a) (q R x))
  have hc := NatTrans.naturality_apply c'.inv a x
  change c'.inv.app S (mapPoints a x) = (convolutionPoints C).map a (c'.inv.app R x) at hc
  rw [hq, hp, hq, hc]
  exact liftConvolutionPoints_natural hr hn C a (c'.inv.app R x)

end ChangeOfField

open private maximalTorus_of_geometricallyMaximal geometricallyMaximal_of_maximal_split
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

private theorem compatible_id {L : TestAlgebra K ⥤ TestAlgebra F}
    {X : GroupScheme F} {Y : GroupScheme K} (p : PointComparison L X Y) :
    Compatible p p (𝟙 X) (𝟙 Y) := by
  intro R x
  change p.equiv R (x ≫ 𝟙 Y.X) = p.equiv R x ≫ 𝟙 X.X
  simp only [Category.comp_id]

section Subgroups

variable {e : F ≃+* K} {L : TestAlgebra K ⥤ TestAlgebra F}
  {r : ∀ R : TestAlgebra K, L.obj R ≃+* R}
  (hr : ∀ (R : TestAlgebra K) (x : F), r R (algebraMap F (L.obj R) x) = algebraMap K R (e x))
  (hn : ∀ {R S : TestAlgebra K} (a : R ⟶ S) (x : L.obj R),
    r S ((L.map a).hom x) = a.hom (r R x))

include hr hn in
private theorem descendSubgroup {X : AffineAlgebraicGroup F} {Y : AffineAlgebraicGroup K}
    (p : PointComparison L X.val Y.val) (A : ClosedSubgroup X.val) :
    ∃ (B : ClosedSubgroup Y.val) (q : PointComparison L A.group B.group),
      Compatible p q A.inclusion B.inclusion := by
  let U := closedSubgroupAlgebraicGroup (G := X) A
  obtain ⟨V, ⟨q⟩⟩ := smallModel hr hn U
  obtain ⟨g, hg⟩ := descendHom V.prop.1 q p A.inclusion
  have hg' := (compatible_closedImmersion (X := U) (Y := V) hr hn hg).mp A.isClosedImmersion
  exact ⟨⟨V.val, g, hg'⟩, q, hg⟩

include hr hn in
private theorem liftSubgroup {X : AffineAlgebraicGroup F} {Y : AffineAlgebraicGroup K}
    (p : PointComparison L X.val Y.val) (B : ClosedSubgroup Y.val) :
    ∃ (A : ClosedSubgroup X.val) (q : PointComparison L A.group B.group),
      Compatible p q A.inclusion B.inclusion := by
  let V := closedSubgroupAlgebraicGroup (G := Y) B
  obtain ⟨U, ⟨q⟩⟩ := largeModel hr hn V
  obtain ⟨f, hf⟩ := liftHom (X := U) hr hn q p B.inclusion
  have hf' := (compatible_closedImmersion (X := U) (Y := V) hr hn hf).mpr B.isClosedImmersion
  exact ⟨⟨U.val, f, hf'⟩, q, hf⟩

include hr hn in
private theorem subgroup_iff {X : AffineAlgebraicGroup F} {Y : AffineAlgebraicGroup K}
    {p : PointComparison L X.val Y.val} {A A' : ClosedSubgroup X.val}
    {B B' : ClosedSubgroup Y.val} {q : PointComparison L A.group B.group}
    {q' : PointComparison L A'.group B'.group}
    (h : Compatible p q A.inclusion B.inclusion)
    (h' : Compatible p q' A'.inclusion B'.inclusion) :
    IsSubgroupOf A A' ↔ IsSubgroupOf B B' := by
  let U := closedSubgroupAlgebraicGroup (G := X) A
  let U' := closedSubgroupAlgebraicGroup (G := X) A'
  let V := closedSubgroupAlgebraicGroup (G := Y) B
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨g, hg⟩ := descendHom V.prop.1 q q' f
    have hcomp := compatible_comp hg h'
    rw [hf] at hcomp
    exact ⟨g, compatible_unique_small V.prop.1 hcomp h⟩
  · rintro ⟨g, hg⟩
    obtain ⟨f, hf⟩ := liftHom (X := U) (X' := U') hr hn q q' g
    have hcomp := compatible_comp hf h'
    rw [hg] at hcomp
    exact ⟨f, compatible_unique_large (X := U) hr hcomp h⟩

private abbrev groundTest (k : Type u) [Field k] : TestAlgebra k := CommAlgCat.of k k

include hr in
private def groundIso : groundTest F ≅ L.obj (groundTest K) :=
  CommAlgCat.isoMk (AlgEquiv.ofRingEquiv (f := e.trans (r (groundTest K)).symm)
    (fun x => scalar_symm e L r hr (groundTest K) (e x) |>.trans
      (congrArg (algebraMap F (L.obj (groundTest K))) (e.symm_apply_apply x))))

private def groundSpecIso (k : Type u) [Field k] :
    𝟙_ (SchemeOver k) ≅ (testSpec k).obj (op (groundTest k)) :=
  (isTerminalTensorUnit (C := SchemeOver k)).uniqueUpToIso (affineBaseTerminal k)

private def groundPointsToSections {k : Type u} [Field k] (G : GroupScheme k) :
    GroupPoints G (groundTest k) ≃* rationalSections G :=
  ((yonedaGrp.obj G).mapIso (groundSpecIso k).op).groupIsoToMulEquiv

include hr in
private def rationalEquiv {X : GroupScheme F} {Y : GroupScheme K} (p : PointComparison L X Y) :
    rationalSections Y ≃* rationalSections X :=
  (groundPointsToSections Y).symm.trans <|
    (p.equiv (groundTest K)).trans <|
      ((((groupPointsFunctor F).obj X).mapIso (groundIso hr)).groupIsoToMulEquiv).symm.trans
        (groundPointsToSections X)

include hr hn in
private theorem connected_iff {X : AffineAlgebraicGroup F} {Y : AffineAlgebraicGroup K}
    (p : PointComparison L X.val Y.val) :
    ConnectedSpace X.val.X.left ↔ ConnectedSpace Y.val.X.left := by
  obtain ⟨B, w, z, _⟩ := comparison_spectra hr hn p
  exact (w.inv.left.homeomorph.trans
    ((PrimeSpectrum.homeomorphOfRingEquiv (r B).symm).trans z.hom.left.homeomorph)).connectedSpace_iff.symm

include hr hn in
private theorem solvableSubgroup_iff [IsAlgClosed F] [CharZero F] [IsAlgClosed K] [CharZero K]
    {X : AffineAlgebraicGroup F} {Y : AffineAlgebraicGroup K} {A : ClosedSubgroup X.val}
    {B : ClosedSubgroup Y.val} (p : PointComparison L A.group B.group) :
    IsSmoothConnectedSolvable A ↔ IsSmoothConnectedSolvable B := by
  let U := closedSubgroupAlgebraicGroup (G := X) A
  let V := closedSubgroupAlgebraicGroup (G := Y) B
  have sU := characteristicZeroSmoothness F U
  have sV := characteristicZeroSmoothness K V
  have c := connected_iff (X := U) (Y := V) hr hn p
  let eqv := rationalEquiv hr p
  constructor
  · rintro ⟨_, hc, hs⟩
    letI : Group.IsSolvable (rationalSections A.group) := (solvable_iff_sections U sU hc).mp hs
    exact ⟨sV, c.mp hc, (solvable_iff_sections V sV (c.mp hc)).mpr
      (Group.isSolvable_of_surjective (f := eqv.symm.toMonoidHom) eqv.symm.surjective)⟩
  · rintro ⟨_, hc, hs⟩
    letI : Group.IsSolvable (rationalSections B.group) := (solvable_iff_sections V sV hc).mp hs
    exact ⟨sU, c.mpr hc, (solvable_iff_sections U sU (c.mpr hc)).mpr
      (Group.isSolvable_of_surjective (f := eqv.toMonoidHom) eqv.surjective)⟩

private abbrev power (k : Type u) [Field k] (n : ℕ) :=
  Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin n))

private def powerUnits (r : ∀ R : TestAlgebra K, L.obj R ≃+* R) (n : ℕ) (R : TestAlgebra K) :
    (ULift.{0} (Fin n) → Rˣ) ≃* (ULift.{u} (Fin n) → (L.obj R)ˣ) where
  toFun x i := Units.mapEquiv (r R).symm.toMulEquiv (x ⟨i.down⟩)
  invFun x i := Units.mapEquiv (r R).toMulEquiv (x ⟨i.down⟩)
  left_inv x := funext fun i => (Units.mapEquiv (r R).toMulEquiv).apply_symm_apply (x i)
  right_inv x := funext fun i => (Units.mapEquiv (r R).toMulEquiv).symm_apply_apply (x i)
  map_mul' x y := funext fun i => map_mul (Units.mapEquiv (r R).symm.toMulEquiv) (x ⟨i.down⟩) (y ⟨i.down⟩)

include hn in
private def powerComparison (n : ℕ) : PointComparison L (power F n).val (power K n).val := by
  let f := StandardGroups.multiplicativePowerGroupPointsIso (k := F) («ι» := ULift.{u} (Fin n))
  let g := StandardGroups.multiplicativePowerGroupPointsIso (k := K) («ι» := ULift.{0} (Fin n))
  let l (R : TestAlgebra K) := (f.app (L.obj R)).groupIsoToMulEquiv
  let m (R : TestAlgebra K) := (g.app R).groupIsoToMulEquiv
  let p (R : TestAlgebra K) := ((m R).trans (powerUnits r n R)).trans (l R).symm
  have hp (R : TestAlgebra K) (x : GroupPoints (power K n).val R) :
      l R (p R x) = powerUnits r n R (m R x) := (l R).apply_symm_apply _
  refine ⟨p, ?_⟩
  intro R S a x
  apply (l S).injective
  have hf := NatTrans.naturality_apply f.hom (L.map a) (p R x)
  have hg := NatTrans.naturality_apply g.hom a x
  change l S (mapPoints (L.map a) (p R x)) =
    fun i => Units.map (L.map a).hom.toMonoidHom (l R (p R x) i) at hf
  change m S (mapPoints a x) = fun i => Units.map a.hom.toMonoidHom (m R x i) at hg
  calc
    l S (p S (mapPoints a x)) = powerUnits r n S (m S (mapPoints a x)) := hp S _
    _ = powerUnits r n S (fun i => Units.map a.hom.toMonoidHom (m R x i)) :=
      congrArg (powerUnits r n S) hg
    _ = (fun i => Units.map (L.map a).hom.toMonoidHom (powerUnits r n R (m R x) i)) := by
      funext i
      apply Units.ext
      change (r S).symm (a.hom ((m R x ⟨i.down⟩ : Rˣ) : R)) =
        (L.map a).hom ((r R).symm ((m R x ⟨i.down⟩ : Rˣ) : R))
      apply (r S).injective
      rw [RingEquiv.apply_symm_apply, hn, RingEquiv.apply_symm_apply]
    _ = (fun i => Units.map (L.map a).hom.toMonoidHom (l R (p R x) i)) :=
      congrArg (fun z i => Units.map (L.map a).hom.toMonoidHom (z i)) (hp R x).symm
    _ = l S (mapPoints (L.map a) (p R x)) := hf.symm

include hn in
private theorem split_descends {X : AffineAlgebraicGroup F} {Y : AffineAlgebraicGroup K}
    (p : PointComparison L X.val Y.val) (h : IsSplitTorus X.val) : IsSplitTorus Y.val := by
  obtain ⟨n, ⟨z⟩⟩ := h
  let q := powerComparison hn n
  obtain ⟨g, hg⟩ := descendHom Y.prop.1 p q z.hom
  obtain ⟨j, hj⟩ := descendHom (power K n).prop.1 q p z.inv
  refine ⟨n, ⟨⟨g, j, ?_, ?_⟩⟩⟩
  · apply compatible_unique_small Y.prop.1 _ (compatible_id p)
    simpa only [z.hom_inv_id] using compatible_comp hg hj
  · apply compatible_unique_small (power K n).prop.1 _ (compatible_id q)
    simpa only [z.inv_hom_id] using compatible_comp hj hg

include hr hn in
private theorem split_lifts {X : AffineAlgebraicGroup F} {Y : AffineAlgebraicGroup K}
    (p : PointComparison L X.val Y.val) (h : IsSplitTorus Y.val) : IsSplitTorus X.val := by
  obtain ⟨n, ⟨z⟩⟩ := h
  let q := powerComparison hn n
  obtain ⟨g, hg⟩ := liftHom (X' := power F n) hr hn p q z.hom
  obtain ⟨j, hj⟩ := liftHom (X := power F n) hr hn q p z.inv
  refine ⟨n, ⟨⟨g, j, ?_, ?_⟩⟩⟩
  · apply compatible_unique_large (X := X) hr _ (compatible_id p)
    simpa only [z.hom_inv_id] using compatible_comp hg hj
  · apply compatible_unique_large (X := power F n) hr _ (compatible_id q)
    simpa only [z.inv_hom_id] using compatible_comp hj hg

end Subgroups

/-- Keep the given ambient group and transport both of its marked subgroups. -/
theorem transportSplitBorelPair : TransportSplitBorelPair.{u} := by
  intro F _ _ _ K _ _ _ e L r hr hn P H hH p
  obtain ⟨T, t, ht⟩ := descendSubgroup hr hn p P.T
  obtain ⟨B, b, hb⟩ := descendSubgroup hr hn p P.B
  let TF := closedSubgroupAlgebraicGroup (G := P.G) P.T
  let TK := closedSubgroupAlgebraicGroup (G := H) T
  have hs : IsSplitTorus T.group := split_descends (X := TF) (Y := TK) hn t P.split
  have hmax : IsMaximalTorus T := by
    refine ⟨lattice_torus_of_split hs, ?_⟩
    intro S hS hTS
    let SK := closedSubgroupAlgebraicGroup (G := H) S
    have hsK : IsSplitTorus S.group := split_of_torus ((isTorus_iff_coordinates SK).mp hS)
    obtain ⟨A, a, ha⟩ := liftSubgroup hr hn p S
    let AF := closedSubgroupAlgebraicGroup (G := P.G) A
    have hsF : IsSplitTorus A.group := split_lifts (X := AF) (Y := SK) hr hn a hsK
    have hTm := maximalTorus_of_geometricallyMaximal P.G P.T
      (lattice_torus_of_split P.split) P.maximal
    exact (subgroup_iff hr hn ha ht).mp
      (hTm.2 A (lattice_torus_of_split hsF) ((subgroup_iff hr hn ht ha).mpr hTS))
  have hB : IsBorel B := by
    have hBF := (isKBorel_iff_of_isAlgClosed P.G P.B).mp P.borel
    refine ⟨(solvableSubgroup_iff hr hn b).mp hBF.1, ?_⟩
    intro C hC hBC
    obtain ⟨A, a, ha⟩ := liftSubgroup hr hn p C
    exact (subgroup_iff hr hn ha hb).mp
      (hBF.2 A ((solvableSubgroup_iff hr hn a).mpr hC) ((subgroup_iff hr hn hb ha).mpr hBC))
  let Q : Specs.Pinning.SplitBorelPair K :=
    ⟨H, hH, T, hs, geometricallyMaximal_of_maximal_split H T hmax hs, B,
      (isKBorel_iff_of_isAlgClosed H B).mpr hB, (subgroup_iff hr hn ht hb).mp P.containsTorus⟩
  exact ⟨Q, rfl, p, t, b, ht, hb⟩

end

end LinearAlgebraicGroups.Arithmetic.F4RealCompletionBorelPair
