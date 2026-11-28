import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.GlobalFunctionsHopf
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits hiding prodComparison prodComparison_natural prodComparison_fst prodComparison_snd terminalComparison
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Opposite
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace RepTheorySurvey.Invariants.GlobalFunctions

open LinearAlgebraicGroups (SchemeOver TestAlgebra Points testSpec HopfAlgebraCategory
  AffineGroupCategory coordinateHopf coordinateHopfSpecIso affineGroupInclusion)
open LinearAlgebraicGroups.Specs (GroupScheme)

noncomputable section

set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

local notation "F" => sectionsFunctor k
local notation "S" => algSpec (CommRingCat.of k)
local notation "A" => algΓAlgSpecAdjunction (CommRingCat.of k)

@[simp] theorem pull_comp {X Y Z : SchemeOver k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull (f ≫ g) = (pull f).comp (pull g) := by
  unfold pull
  rw [Functor.map_comp]
  rfl

@[simp] theorem pull_id (X : SchemeOver k) : pull (𝟙 X) = AlgHom.id k _ := by
  unfold pull
  exact congrArg (fun h => h.unop.hom) (CategoryTheory.Functor.map_id (sectionsFunctor k) X)

theorem productFormula : Specs.ProductFormula.{u} := by
  intro k _ X Y f g
  exact Algebra.TensorProduct.lift_tmul _ _ (fun _ _ => Commute.all _ _) _ _

theorem productNaturality : Specs.ProductNaturality.{u} := by
  intro k _ X X' Y Y' f g
  exact congrArg (fun h => h.unop.hom) (prodComparison_natural (sectionsFunctor k) f g)

theorem finiteTypeTopology : Specs.FiniteTypeTopology.{u} := by
  intro k _ X hft hqc
  letI := LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact ⟨QuasiCompact.compactSpace_of_compactSpace X.hom, inferInstance⟩

theorem evaluationFormula : Specs.EvaluationFormula.{u} := by
  intro k _ X R p
  let a := algΓAlgSpecAdjunction (CommRingCat.of k)
  let s := algSpec (CommRingCat.of k)
  let e := (testSectionsIso R).symm.op
  have he : e.hom = a.counit.app (op R) := rfl
  change p ≫ a.unit.app X = s.map (e.inv ≫ (sectionsFunctor k).map p)
  rw [Functor.map_comp, ← a.unit_naturality p]
  have h := a.right_triangle_components (op R)
  change a.unit.app (s.obj (op R)) ≫ s.map (a.counit.app (op R)) = 𝟙 _ at h
  rw [← he, ← Functor.mapIso_hom] at h
  have hi : a.unit.app (s.obj (op R)) = (s.mapIso e).inv := by
    apply (cancel_mono (s.mapIso e).hom).mp
    exact h.trans (s.mapIso e).inv_hom_id.symm
  rw [hi, Functor.mapIso_inv]

private theorem isIso_unit_of_affine (X : SchemeOver k) [IsAffine X.left] :
    IsIso (unit X) := by
  letI : (S).Full := algSpec.instFull
  letI : (S).Faithful := algSpec.instFaithful
  exact ((A).isIso_unit_app_iff_mem_essImage (Y := X)).mpr (essImage_algSpec.mpr ‹_›)

theorem affinizationUniversal : Specs.AffinizationUniversal.{u} := by
  intro k _ X L hL f
  let a := algΓAlgSpecAdjunction (CommRingCat.of k)
  let s := algSpec (CommRingCat.of k)
  obtain ⟨B, ⟨e⟩⟩ := essImage_algSpec.mpr hL
  letI : s.Full := algSpec.instFull
  letI : s.Faithful := algSpec.instFaithful
  let q := (a.homEquiv X B).symm (f ≫ e.inv)
  have hq : unit X ≫ s.map q = f ≫ e.inv := by
    change a.unit.app X ≫ s.map q = f ≫ e.inv
    exact (a.homEquiv_unit X B q).symm.trans ((a.homEquiv X B).apply_symm_apply _)
  refine ⟨s.map q ≫ e.hom, ?_, ?_⟩
  · change unit X ≫ (s.map q ≫ e.hom) = f
    rw [← Category.assoc, hq, Category.assoc, e.inv_hom_id, Category.comp_id]
  · intro g hg
    apply (cancel_mono e.inv).mp
    let q' := s.preimage (g ≫ e.inv)
    have hq' : s.map q' = g ≫ e.inv := s.map_preimage _
    have h : q' = q := by
      apply (a.homEquiv X B).injective
      rw [a.homEquiv_unit, a.homEquiv_unit]
      change unit X ≫ s.map q' = unit X ≫ s.map q
      rw [hq', hq, ← Category.assoc, hg]
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    exact hq'.symm.trans (congrArg s.map h)

private theorem product_unit (X Y : SchemeOver k) :
    unit (X ⊗ Y) ≫ (S).map (prodComparison F X Y) ≫ prodComparison S ((F).obj X) ((F).obj Y) =
      unit X ⊗ₘ unit Y := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, prodComparison_fst, ← Functor.map_comp]
    exact ((A).unit_naturality (fst X Y)).trans
      (tensorHom_fst (unit X) (unit Y)).symm
  · simp only [Category.assoc, prodComparison_snd, ← Functor.map_comp]
    exact ((A).unit_naturality (snd X Y)).trans
      (tensorHom_snd (unit X) (unit Y)).symm

private theorem affine_product (X Y : SchemeOver k) [IsAffine X.left] [IsAffine Y.left] :
    Function.Bijective (tensorComparison X Y) := by
  letI := isIso_unit_of_affine X
  letI := isIso_unit_of_affine Y
  haveI : IsAffine (X ⊗ Y).left := by
    change IsAffine (pullback X.hom Y.hom)
    infer_instance
  letI := isIso_unit_of_affine (X ⊗ Y)
  haveI hp : IsIso (unit X ⊗ₘ unit Y) :=
    (tensorIso (asIso (unit X)) (asIso (unit Y))).isIso_hom
  haveI : IsIso (unit (X ⊗ Y) ≫ (S).map (prodComparison F X Y) ≫
      prodComparison S ((F).obj X) ((F).obj Y)) := by
    rw [product_unit]
    exact hp
  haveI : IsIso ((S).map (prodComparison F X Y) ≫ prodComparison S ((F).obj X) ((F).obj Y)) :=
    IsIso.of_isIso_comp_left (unit (X ⊗ Y)) _
  haveI : PreservesLimit (pair ((F).obj X) ((F).obj Y)) S :=
    AlgebraicGeometry.preservesLimitsOfSize_algSpec.preservesLimitsOfShape.preservesLimit
  haveI : IsIso ((S).map (prodComparison F X Y)) := IsIso.of_isIso_comp_right ((S).map (prodComparison F X Y))
      (prodComparison S ((F).obj X) ((F).obj Y))
  letI : (S).Full := algSpec.instFull
  letI : (S).Faithful := algSpec.instFaithful
  haveI : IsIso (prodComparison F X Y) := isIso_of_reflects_iso _ S
  exact ConcreteCategory.bijective_of_isIso (prodComparison F X Y).unop

/-- An element of the global functions algebra, viewed as a morphism to the affine line. -/
private def sectionToLine {X : SchemeOver k} (x : Sections X) :
    X ⟶ (S).obj (op (CommAlgCat.of k (Polynomial k))) :=
  ((A).homEquiv _ _) (CommAlgCat.ofHom (Polynomial.aeval x)).op

private theorem sectionToLine_bijective (X : SchemeOver k) :
    Function.Bijective (sectionToLine (X := X)) := by
  constructor
  · intro f g h
    have h' := ((A).homEquiv X (op (CommAlgCat.of k (Polynomial k)))).injective h
    exact (Polynomial.aeval_X f).symm.trans
      ((congrArg (fun q => q.unop.hom Polynomial.X) h').trans (Polynomial.aeval_X g))
  · intro f
    let q := ((A).homEquiv X (op (CommAlgCat.of k (Polynomial k)))).symm f
    refine ⟨q.unop.hom Polynomial.X, ?_⟩
    have hq : (CommAlgCat.ofHom (Polynomial.aeval (q.unop.hom Polynomial.X))).op = q := by
      apply Quiver.Hom.unop_inj
      apply CommAlgCat.hom_ext
      exact Polynomial.algHom_ext (Polynomial.aeval_X _)
    unfold sectionToLine
    rw [hq]
    exact ((A).homEquiv X (op (CommAlgCat.of k (Polynomial k)))).apply_symm_apply f

private theorem sectionToLine_pull {X Y : SchemeOver k} (f : X ⟶ Y) (x : Sections Y) :
    sectionToLine (pull f x) = f ≫ sectionToLine x := by
  unfold sectionToLine
  rw [← (A).homEquiv_naturality_left]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  change Polynomial.aeval (pull f x) Polynomial.X = pull f (Polynomial.aeval x Polynomial.X)
  rw [Polynomial.aeval_X, Polynomial.aeval_X]

variable {Y : SchemeOver k}

private abbrev chart (C : Y.left.OpenCover) (i : C.I₀) : SchemeOver k :=
  Over.mk (C.f i ≫ Y.hom)

private abbrev chartMap (C : Y.left.OpenCover) (i : C.I₀) : chart C i ⟶ Y :=
  Over.homMk (C.f i)

private abbrev overlap (C : Y.left.OpenCover) (i j : C.I₀) : SchemeOver k :=
  Over.mk (pullback.fst (C.f i) (C.f j) ≫ C.f i ≫ Y.hom)

private abbrev overlapFst (C : Y.left.OpenCover) (i j : C.I₀) :
    overlap C i j ⟶ chart C i :=
  Over.homMk (pullback.fst _ _)

private abbrev overlapSnd (C : Y.left.OpenCover) (i j : C.I₀) :
    overlap C i j ⟶ chart C j :=
  Over.homMk (pullback.snd _ _) (by simp only [Over.mk_hom, pullback.condition_assoc])

private theorem pull_cover_injective (C : Y.left.OpenCover) :
    Function.Injective (fun x : Sections Y => fun i : C.I₀ => pull (chartMap C i) x) := by
  intro f g h
  exact C.ext_elem f g (fun i => congrFun h i)

/-- Gluing sections is gluing maps to the affine line over the base. -/
private theorem glue_sections (C : Y.left.OpenCover) (x : ∀ i, Sections (chart C i))
    (hx : ∀ i j, pull (overlapFst C i j) (x i) = pull (overlapSnd C i j) (x j)) :
    ∃ t : Sections Y, ∀ i, pull (chartMap C i) t = x i := by
  let f (i : C.I₀) := sectionToLine (x i)
  have hf (i j : C.I₀) :
      pullback.fst (C.f i) (C.f j) ≫ (f i).left =
        pullback.snd (C.f i) (C.f j) ≫ (f j).left := by
    exact congrArg (fun g => g.left)
      ((sectionToLine_pull (overlapFst C i j) (x i)).symm.trans
        ((congrArg sectionToLine (hx i j)).trans (sectionToLine_pull (overlapSnd C i j) (x j))))
  let g := C.glueMorphisms (fun i => (f i).left) hf
  have hg (i : C.I₀) : C.f i ≫ g = (f i).left := C.ι_glueMorphisms _ _ i
  have hw : g ≫ ((S).obj (op (CommAlgCat.of k (Polynomial k)))).hom = Y.hom := by
    apply C.hom_ext
    intro i
    rw [← Category.assoc, hg]
    exact Over.w (f i)
  let g' : Y ⟶ (S).obj (op (CommAlgCat.of k (Polynomial k))) := Over.homMk g hw
  obtain ⟨t, ht⟩ := (sectionToLine_bijective Y).2 g'
  refine ⟨t, fun i => (sectionToLine_bijective (chart C i)).1 ?_⟩
  rw [sectionToLine_pull, ht]
  exact Over.OverMorphism.ext (hg i)

private theorem productChartPullback (X : SchemeOver k) {V W : SchemeOver k} (f : V ⟶ W) :
    IsPullback (X ◁ f).left (snd X V).left (snd X W).left f.left := by
  apply IsPullback.flip
  apply IsPullback.of_bot (v₂₁ := (fst X W).left) (v₂₂ := W.hom)
  · have h : (X ◁ f).left ≫ (fst X W).left = (fst X V).left :=
      congrArg (fun g => g.left) (whiskerLeft_fst X f)
    rw [h, Over.w f]
    exact (IsPullback.of_hasPullback X.hom V.hom).flip
  · exact (congrArg (fun g => g.left) (whiskerLeft_snd X f)).symm
  · exact (IsPullback.of_hasPullback X.hom W.hom).flip

private def productCover (X : SchemeOver k) (C : Y.left.OpenCover) : (X ⊗ Y).left.OpenCover :=
  let D : (X ⊗ Y).left.OpenCover := C.pullback₁ (snd X Y).left
  D.copy C.I₀ (fun i => (X ⊗ chart C i).left) (fun i => (X ◁ chartMap C i).left)
    (Equiv.refl _) (fun i => (productChartPullback X (chartMap C i)).isoPullback)
    (fun i => ((productChartPullback X (chartMap C i)).isoPullback_hom_fst).symm)

private theorem pull_productCover_injective (X : SchemeOver k) (C : Y.left.OpenCover) :
    Function.Injective
      (fun x : Sections (X ⊗ Y) => fun i : C.I₀ => pull (X ◁ chartMap C i) x) := by
  intro f g h
  exact (productCover X C).ext_elem f g (fun i => congrFun h i)

private def coverRestriction (C : Y.left.OpenCover) :
    Sections Y →ₗ[k] (∀ i, Sections (chart C i)) :=
  LinearMap.pi (fun i => (pull (chartMap C i)).toLinearMap)

private def coverDifference (C : Y.left.OpenCover) :
    (∀ i, Sections (chart C i)) →ₗ[k] (∀ ij : C.I₀ × C.I₀, Sections (overlap C ij.1 ij.2)) :=
  LinearMap.pi (fun ij =>
    (pull (overlapFst C ij.1 ij.2)).toLinearMap.comp (LinearMap.proj ij.1) -
    (pull (overlapSnd C ij.1 ij.2)).toLinearMap.comp (LinearMap.proj ij.2))

private theorem coverExact (C : Y.left.OpenCover) :
    Function.Exact (coverRestriction C) (coverDifference C) := by
  intro x
  constructor
  · intro h
    have hc (i j : C.I₀) : pull (overlapFst C i j) (x i) = pull (overlapSnd C i j) (x j) :=
      sub_eq_zero.mp (congrFun h (i, j))
    obtain ⟨t, ht⟩ := glue_sections C x hc
    exact ⟨t, funext ht⟩
  · rintro ⟨x, rfl⟩
    funext ij
    rcases ij with ⟨i, j⟩
    change pull (overlapFst C i j) (pull (chartMap C i) x) -
      pull (overlapSnd C i j) (pull (chartMap C j) x) = 0
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← pull_comp, ← pull_comp]
    have h : overlapFst C i j ≫ chartMap C i = overlapSnd C i j ≫ chartMap C j :=
      Over.OverMorphism.ext pullback.condition
    rw [h, sub_self]

private theorem comparison_whisker (X : SchemeOver k) {V W : SchemeOver k} (f : V ⟶ W)
    (x : Sections X ⊗[k] Sections W) :
    tensorComparison X V ((pull f).toLinearMap.lTensor (Sections X) x) =
      pull (X ◁ f) (tensorComparison X W x) := by
  have h := congrArg (fun (g : Sections X ⊗[k] Sections W →ₐ[k] Sections (X ⊗ V)) => g x)
    (productNaturality (𝟙 X) f)
  rw [id_tensorHom, pull_id] at h
  exact h.symm

private theorem restrictionTensor (X : SchemeOver k) (C : Y.left.OpenCover)
    (x : Sections X ⊗[k] Sections Y) (i : C.I₀) :
    TensorProduct.piRightHom k k (Sections X) (fun i => Sections (chart C i))
        ((coverRestriction C).lTensor (Sections X) x) i =
      (pull (chartMap C i)).toLinearMap.lTensor (Sections X) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

private theorem differenceTensor (X : SchemeOver k) (C : Y.left.OpenCover)
    (x : Sections X ⊗[k] (∀ i, Sections (chart C i))) (i j : C.I₀) :
    TensorProduct.piRightHom k k (Sections X) (fun ij : C.I₀ × C.I₀ => Sections (overlap C ij.1 ij.2))
        ((coverDifference C).lTensor (Sections X) x) (i,j) =
      (pull (overlapFst C i j)).toLinearMap.lTensor (Sections X)
        (TensorProduct.piRightHom k k (Sections X) (fun l => Sections (chart C l)) x i) -
      (pull (overlapSnd C i j)).toLinearMap.lTensor (Sections X)
        (TensorProduct.piRightHom k k (Sections X) (fun l => Sections (chart C l)) x j) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change a ⊗ₜ[k] (pull (overlapFst C i j) (b i) - pull (overlapSnd C i j) (b j)) =
      a ⊗ₜ[k] pull (overlapFst C i j) (b i) - a ⊗ₜ[k] pull (overlapSnd C i j) (b j)
    exact TensorProduct.tmul_sub _ _ _
  | add a b ha hb =>
    simp only [map_add, Pi.add_apply, ha, hb]
    abel

private theorem comparison_injective_of_cover (X : SchemeOver k) (C : Y.left.OpenCover)
    [Fintype C.I₀] (hC : ∀ i, Function.Injective (tensorComparison X (chart C i))) :
    Function.Injective (tensorComparison X Y) := by
  classical
  intro a b hab
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := Sections X) (coverRestriction C)
    (pull_cover_injective C)
  apply (TensorProduct.piRight k k (Sections X) (fun i => Sections (chart C i))).injective
  funext i
  simp only [TensorProduct.piRight_apply, restrictionTensor]
  apply hC i
  simp only [comparison_whisker, hab]

/-- Local tensor lifts agree on overlaps by injectivity there. Flatness and the
finite-product equivalences then make the family lift to a global tensor. -/
private theorem comparison_surjective_of_cover (X : SchemeOver k) (C : Y.left.OpenCover)
    [Fintype C.I₀] (hC : ∀ i, Function.Surjective (tensorComparison X (chart C i)))
    (hO : ∀ i j, Function.Injective (tensorComparison X (overlap C i j))) :
    Function.Surjective (tensorComparison X Y) := by
  classical
  intro t
  choose v hv using fun i => hC i (pull (X ◁ chartMap C i) t)
  let P := TensorProduct.piRight k k (Sections X) (fun i => Sections (chart C i))
  let Q := TensorProduct.piRight k k (Sections X)
    (fun ij : C.I₀ × C.I₀ => Sections (overlap C ij.1 ij.2))
  let z := P.symm v
  have hz (i : C.I₀) :
      TensorProduct.piRightHom k k (Sections X) (fun l => Sections (chart C l)) z i = v i :=
    congrFun (P.apply_symm_apply v) i
  have hd : (coverDifference C).lTensor (Sections X) z = 0 := by
    apply Q.injective
    funext ij
    rcases ij with ⟨i, j⟩
    change TensorProduct.piRightHom k k (Sections X)
      (fun ij : C.I₀ × C.I₀ => Sections (overlap C ij.1 ij.2))
      ((coverDifference C).lTensor (Sections X) z) (i, j) = (Q 0) (i, j)
    rw [map_zero, Pi.zero_apply, differenceTensor, hz, hz, sub_eq_zero]
    apply hO i j
    simp only [comparison_whisker, hv, ← AlgHom.comp_apply, ← pull_comp]
    congr 2
    rw [← whiskerLeft_comp, ← whiskerLeft_comp]
    exact congrArg (fun f => X ◁ f) (Over.OverMorphism.ext pullback.condition)
  obtain ⟨s, hs⟩ := (Module.Flat.lTensor_exact (Sections X) (coverExact C) z).mp hd
  apply Exists.intro s
  apply pull_productCover_injective X C
  funext i
  change pull (X ◁ chartMap C i) (tensorComparison X Y s) = pull (X ◁ chartMap C i) t
  rw [← comparison_whisker, ← restrictionTensor, hs, hz, hv]

private theorem comparison_injective_of_affines (X Y : SchemeOver k) [CompactSpace Y.left]
    (h : ∀ (V : SchemeOver k) [IsAffine V.left], Function.Injective (tensorComparison X V)) :
    Function.Injective (tensorComparison X Y) := by
  let C := Y.left.affineCover.finiteSubcover
  letI : Fintype C.I₀ := Fintype.ofFinite _
  apply comparison_injective_of_cover X C
  intro i
  haveI : IsAffine (chart C i).left := by
    change IsAffine (Y.left.affineCover.X (Y.left.affineCover.idx i.val))
    infer_instance
  exact h (chart C i)

private theorem comparison_bijective_of_affines (X Y : SchemeOver k)
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    (h : ∀ (V : SchemeOver k) [IsAffine V.left], Function.Bijective (tensorComparison X V)) :
    Function.Bijective (tensorComparison X Y) := by
  refine ⟨comparison_injective_of_affines X Y (fun V inst => (h V).1), ?_⟩
  let C := Y.left.affineCover.finiteSubcover
  letI : Fintype C.I₀ := Fintype.ofFinite _
  haveI hc (i : C.I₀) : IsAffine (chart C i).left := by
    change IsAffine (Y.left.affineCover.X (Y.left.affineCover.idx i.val))
    infer_instance
  apply comparison_surjective_of_cover X C (fun i => (h (chart C i)).2)
  intro i j
  haveI (i : C.I₀) : CompactSpace (C.X i) := inferInstanceAs (CompactSpace (chart C i).left)
  haveI : QuasiCompact (C.f i) := (quasiCompact_iff_compactSpace (C.f i)).mpr inferInstance
  haveI : CompactSpace (overlap C i j).left :=
    inferInstanceAs (CompactSpace (pullback (C.f i) (C.f j) : Scheme))
  -- Quasi-separatedness lets us check agreement on a finite affine subcover of the overlap.
  exact comparison_injective_of_affines X (overlap C i j) (fun V inst => (h V).1)

private theorem comparison_flip (X Y : SchemeOver k) (h : Function.Bijective (tensorComparison X Y)) :
    Function.Bijective (tensorComparison Y X) := by
  let e := Algebra.TensorProduct.comm k (Sections Y) (Sections X)
  let e' := (sectionsFunctor k).mapIso ((β_ Y X)).symm
  have he : tensorComparison Y X =
      e'.inv.unop.hom.comp ((tensorComparison X Y).comp e.toAlgHom) := by
    have hl (a : Sections Y) (b : Sections X) :
        tensorComparison Y X (a ⊗ₜ[k] b) =
          (pull (β_ Y X).hom) (tensorComparison X Y (b ⊗ₜ[k] a)) := by
      rw [productFormula, productFormula, map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply,
        ← pull_comp, ← pull_comp, braiding_hom_fst, braiding_hom_snd, mul_comm]
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro a b
    exact hl a b
  rw [he]
  exact ((ConcreteCategory.bijective_of_isIso e'.inv.unop).comp h).comp e.bijective

theorem productIsomorphism : Specs.ProductIsomorphism.{u} := by
  intro k _ X Y hx hxs hy hys
  apply comparison_bijective_of_affines X Y
  intro V inst
  apply comparison_flip
  exact comparison_bijective_of_affines V X (fun W inst => affine_product V W)

/-- The canonical comparison as an algebra equivalence. -/
def tensorProductIso (X Y : SchemeOver k)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] :
    Sections X ⊗[k] Sections Y ≃ₐ[k] Sections (X ⊗ Y) :=
  AlgEquiv.ofBijective (tensorComparison X Y) (productIsomorphism X Y)

private theorem isIso_productComparison (X Y : SchemeOver k)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] :
    IsIso (prodComparison F X Y) := by
  let e := tensorProductIso X Y
  exact (CommAlgCat.isoMk e).op.isIso_hom

private theorem unique_precomp {T U L : SchemeOver k} (a : T ⟶ U)
    (h : ∀ f : T ⟶ L, ∃! g : U ⟶ L, a ≫ g = f)
    {g g' : U ⟶ L} (he : a ≫ g = a ≫ g') : g = g' := by
  obtain ⟨t, _, ht⟩ := h (a ≫ g')
  exact (ht g he).trans (ht g' rfl).symm

theorem productAffinizationUniversal : Specs.ProductAffinizationUniversal.{u} := by
  intro k _ X Y L hx hxs hy hys hL f
  let s := algSpec (CommRingCat.of k)
  let ff := sectionsFunctor k
  letI := isIso_productComparison X Y
  letI : PreservesLimit (pair (ff.obj X) (ff.obj Y)) s :=
    AlgebraicGeometry.preservesLimitsOfSize_algSpec.preservesLimitsOfShape.preservesLimit
  let e : affinization (X ⊗ Y) ≅ affinization X ⊗ affinization Y :=
    s.mapIso (asIso (prodComparison ff X Y)) ≪≫ asIso (prodComparison s (ff.obj X) (ff.obj Y))
  have he : unit (X ⊗ Y) ≫ e.hom = unit X ⊗ₘ unit Y := product_unit X Y
  obtain ⟨g, hg, hu⟩ := affinizationUniversal (X ⊗ Y) L f
  refine ⟨e.inv ≫ g, ?_, ?_⟩
  · change (unit X ⊗ₘ unit Y) ≫ e.inv ≫ g = f
    rw [← he, Category.assoc, e.hom_inv_id_assoc, hg]
  · intro b hb
    have hb' : unit (X ⊗ Y) ≫ (e.hom ≫ b) = f := by
      rw [← Category.assoc, he]
      exact hb
    exact (e.eq_inv_comp).mpr (hu _ hb')

private def qcqs (k : Type u) [Field k] : ObjectProperty (SchemeOver k) :=
  fun X => CompactSpace X.left ∧ QuasiSeparatedSpace X.left

private theorem qcqs_terminal : qcqs k (𝟙_ (SchemeOver k)) := by
  change CompactSpace (Spec (CommRingCat.of k)) ∧ QuasiSeparatedSpace (Spec (CommRingCat.of k))
  exact ⟨inferInstance, inferInstance⟩

private theorem qcqs_product (X Y : SchemeOver k) (hX : qcqs k X) (hY : qcqs k Y) :
    qcqs k (X ⊗ Y) := by
  haveI := hX.1
  haveI := hX.2
  haveI := hY.1
  haveI := hY.2
  change CompactSpace (pullback X.hom Y.hom : Scheme) ∧
    QuasiSeparatedSpace (pullback X.hom Y.hom : Scheme)
  haveI : QuasiCompact X.hom := inferInstance
  haveI : QuasiSeparated X.hom := inferInstance
  exact ⟨inferInstance, quasiSeparatedSpace_of_quasiSeparated (pullback.snd X.hom Y.hom)⟩

private instance qcqsIsMonoidal : (qcqs k).IsMonoidal where
  prop_unit := qcqs_terminal
  prop_tensor := qcqs_product

private instance qcqsCartesian : CartesianMonoidalCategory (qcqs k).FullSubcategory where
  __ := ObjectProperty.fullMonoidalSubcategory (qcqs k)
  isTerminalTensorUnit := .ofUniqueHom
    (fun X => ObjectProperty.homMk (toUnit X.1))
    (fun _ _ => by apply ObjectProperty.hom_ext; apply toUnit_unique)
  fst X Y := ObjectProperty.homMk (fst X.1 Y.1)
  snd X Y := ObjectProperty.homMk (snd X.1 Y.1)
  tensorProductIsBinaryProduct X Y :=
    BinaryFan.IsLimit.mk _ (fun f g => ObjectProperty.homMk (lift f.hom g.hom))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def X Y := by apply ObjectProperty.hom_ext; exact fst_def X.1 Y.1
  snd_def X Y := by apply ObjectProperty.hom_ext; exact snd_def X.1 Y.1

private theorem isIso_terminalComparison : IsIso (terminalComparison F) := by
  letI : PreservesLimitsOfSize.{0,0} S :=
    AlgebraicGeometry.preservesLimitsOfSize_algSpec (R := CommRingCat.of k)
  letI : PreservesLimit (Functor.empty.{0} (CommAlgCat.{u} k)ᵒᵖ) S :=
    inferInstance
  let e := preservesTerminalIso S
  letI : (S).Full := algSpec.instFull
  letI : (S).Faithful := algSpec.instFaithful
  let c := asIso ((A).counit.app (𝟙_ (CommAlgCat.{u} k)ᵒᵖ))
  have h : terminalComparison F = (F).map e.inv ≫ c.hom := toUnit_unique _ _
  rw [h]
  infer_instance

private abbrev qcqsSections (k : Type u) [Field k] :=
  (qcqs k).ι ⋙ sectionsFunctor k

private theorem qcqsProdComparison (X Y : (qcqs k).FullSubcategory) :
    prodComparison (qcqsSections k) X Y = prodComparison F X.1 Y.1 := by
  apply CartesianMonoidalCategory.hom_ext
  · exact (prodComparison_fst (qcqsSections k) X Y).trans (prodComparison_fst F X.1 Y.1).symm
  · exact (prodComparison_snd (qcqsSections k) X Y).trans (prodComparison_snd F X.1 Y.1).symm

/-- Sections preserve the chosen finite products on quasi-compact, quasi-separated schemes.
The canonical monoidal structure transports the group laws to the opposite algebra category. -/
private instance qcqsSectionsMonoidal : (qcqsSections k).Monoidal := by
  let ff := qcqsSections k
  haveI (X Y : (qcqs k).FullSubcategory) : IsIso (prodComparison ff X Y) := by
    letI := X.2.1
    letI := X.2.2
    letI := Y.2.1
    letI := Y.2.2
    rw [qcqsProdComparison X Y]
    exact isIso_productComparison X.1 Y.1
  haveI : IsIso (terminalComparison ff) := isIso_terminalComparison (k := k)
  letI := preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison ff
  letI := preservesLimit_empty_of_isIso_terminalComparison ff
  letI := Limits.preservesLimitsOfShape_pempty_of_preservesTerminal ff
  letI : PreservesFiniteProducts ff := .of_preserves_binary_and_terminal _
  exact Functor.Monoidal.ofChosenFiniteProducts ff

private def qcqsGroup (G : GroupScheme k) (hG : qcqs k G.X) : Grp (qcqs k).FullSubcategory :=
  let X : (qcqs k).FullSubcategory := ⟨G.X, hG⟩
  letI : GrpObj ((qcqs k).ι.obj X) := G.grp
  letI : GrpObj X := (qcqs k).fullyFaithfulι.grpObj X
  Grp.mk X

private theorem qcqsGroup_one (G : GroupScheme k) (hG : qcqs k G.X) :
    (MonObj.one (X := (qcqsGroup G hG).X)).hom = MonObj.one (X := G.X) := by
  change 𝟙 (𝟙_ (SchemeOver k)) ≫ MonObj.one (X := G.X) = _
  exact Category.id_comp _

private theorem qcqsGroup_mul (G : GroupScheme k) (hG : qcqs k G.X) :
    (MonObj.mul (X := (qcqsGroup G hG).X)).hom = MonObj.mul (X := G.X) := by
  change 𝟙 (G.X ⊗ G.X) ≫ MonObj.mul (X := G.X) = _
  exact Category.id_comp _

private theorem qcqsGroup_inv (G : GroupScheme k) (hG : qcqs k G.X) :
    (GrpObj.inv (X := (qcqsGroup G hG).X)).hom = GrpObj.inv (X := G.X) := rfl

private def qcqsGroupIso (G : GroupScheme k) (hG : qcqs k G.X) :
    G ≅ (qcqs k).ι.mapGrp.obj (qcqsGroup G hG) :=
  Grp.mkIso (Iso.refl _)
    (by
      change MonObj.one (X := G.X) ≫ 𝟙 G.X =
        𝟙 (𝟙_ (SchemeOver k)) ≫ (MonObj.one (X := (qcqsGroup G hG).X)).hom
      rw [Category.comp_id, Category.id_comp, qcqsGroup_one])
    (by
      change MonObj.mul (X := G.X) ≫ 𝟙 G.X =
        (𝟙 G.X ⊗ₘ 𝟙 G.X) ≫ 𝟙 (G.X ⊗ G.X) ≫ (MonObj.mul (X := (qcqsGroup G hG).X)).hom
      have hm : (MonObj.mul (X := (qcqsGroup G hG).X)).hom = MonObj.mul (X := G.X) :=
        qcqsGroup_mul G hG
      exact (Category.comp_id _).trans (hm.symm.trans
        ((Category.id_comp _).symm.trans ((Category.id_comp _).symm.trans
          (congrArg (fun g : G.X ⊗ G.X ⟶ G.X ⊗ G.X => g ≫ 𝟙 _ ≫ _)
            (id_tensorHom_id G.X G.X).symm)))))

private abbrev sectionsGroup (G : GroupScheme k) (hG : qcqs k G.X) :
    Grp (CommAlgCat.{u} k)ᵒᵖ :=
  (qcqsSections k).mapGrp.obj (qcqsGroup G hG)

private def globalHopfData (G : GroupScheme k) (hG : qcqs k G.X) : Specs.GlobalHopf G where
  group := (sectionsGroup G hG).grp
  comultiplication := by
    let X := (qcqsGroup G hG).X
    let ff := qcqsSections k
    have h : prodComparison F G.X G.X ≫ MonObj.mul (X := (sectionsGroup G hG).X) =
        (F).map (MonObj.mul (X := G.X)) := by
      change prodComparison F X.1 X.1 ≫
        (Functor.LaxMonoidal.μ ff X X ≫ ff.map (MonObj.mul (X := X))) = _
      rw [← qcqsProdComparison X X, ← Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory,
        ← Category.assoc, Functor.Monoidal.δ_μ]
      change 𝟙 ((F).obj (G.X ⊗ G.X)) ≫
        (F).map (MonObj.mul (X := (qcqsGroup G hG).X)).hom = _
      rw [qcqsGroup_mul, Category.id_comp]
    exact congrArg (fun f => f.unop.hom) h
  counit := by
    let X := (qcqsGroup G hG).X
    let ff := qcqsSections k
    let R := CommAlgCat.of k k
    let p := toUnit ((S).obj (op R))
    let c := (testSectionsIso R).symm.op
    haveI : IsIso (terminalComparison ff) := isIso_terminalComparison (k := k)
    have he : Functor.LaxMonoidal.ε ff = c.inv ≫ (F).map p :=
      (cancel_mono (terminalComparison ff)).mp (toUnit_unique _ _)
    have h : MonObj.one (X := (sectionsGroup G hG).X) =
        c.inv ≫ (F).map (p ≫ MonObj.one (X := G.X)) := by
      change Functor.LaxMonoidal.ε ff ≫ ff.map (MonObj.one (X := X)) = _
      rw [he, Category.assoc, Functor.map_comp]
      change c.inv ≫ (F).map p ≫ (F).map (MonObj.one (X := (qcqsGroup G hG).X)).hom = _
      rw [qcqsGroup_one]
    exact congrArg (fun f => f.unop.hom) h
  antipode := by
    change pull ((GrpObj.inv (X := (qcqsGroup G hG).X)).hom) = _
    rw [qcqsGroup_inv]

private def globalHopfUnit (G : GroupScheme k) (hG : qcqs k G.X) :
    G ⟶ (globalHopfData G hG).spectrum := by
  let i := (qcqs k).ι
  let ff := qcqsSections k
  let s := algSpec (CommRingCat.of k)
  letI : s.Monoidal := AlgebraicGeometry.braidedAlgSpec.toMonoidal
  let Q := qcqsGroup G hG
  let n : i ⟶ ff ⋙ s := Functor.whiskerLeft i (A).unit
  let E := commHopfAlgCatEquivCogrpCommAlgCat (CommRingCat.of k)
  let e := (E.counitIso.app (op (sectionsGroup G hG))).hom.unop
  let eComp : (ff ⋙ s).mapGrp ≅ ff.mapGrp ⋙ s.mapGrp := Functor.mapGrpCompIso
  exact (qcqsGroupIso G hG).hom ≫ (Functor.mapGrpNatTrans n).app Q ≫
    eComp.hom.app Q ≫ s.mapGrp.map e

private theorem globalHopfUnit_underlying (G : GroupScheme k) (hG : qcqs k G.X) :
    (globalHopfUnit G hG).hom.hom = unit G.X := by
  change 𝟙 G.X ≫ unit G.X ≫ 𝟙 (affinization G.X) ≫ (S).map (𝟙 ((F).obj G.X)) = unit G.X
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.comp_id _

theorem hopfOperationFormulas : Specs.HopfOperationFormulas.{u} := by
  intro k _ G H
  exact ⟨H.comultiplication, H.counit, H.antipode⟩

/-- The coordinate Hopf algebra on global regular functions of a finite-type group scheme. -/
def globalHopf (G : GroupScheme k) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    Specs.GlobalHopf G :=
  globalHopfData G (finiteTypeTopology G.X)

/-- The canonical morphism from a finite-type group scheme to its affine spectrum. -/
def groupUnit (G : GroupScheme k) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    G ⟶ (globalHopf G).spectrum :=
  globalHopfUnit G (finiteTypeTopology G.X)

theorem groupUnit_underlying (G : GroupScheme k) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    (groupUnit G).hom.hom = unit G.X :=
  globalHopfUnit_underlying G _

theorem globalHopfExists : Specs.GlobalHopfExists.{u} := by
  intro k _ G hGf hGc
  let a := groupUnit G
  let H := globalHopf G
  have ha : a.hom.hom = unit G.X := groupUnit_underlying G
  refine ⟨H, a, ha, ?_⟩
  intro L hL f
  obtain ⟨g, hg, hgu⟩ := affinizationUniversal G.X L.X f.hom.hom
  have h₁ : MonObj.one (X := H.spectrum.X) ≫ g = MonObj.one (X := L.X) := by
    rw [← IsMonHom.one_hom a.hom.hom, Category.assoc, ha, hg, IsMonHom.one_hom]
  have h₂ : MonObj.mul (X := H.spectrum.X) ≫ g =
      (g ⊗ₘ g) ≫ MonObj.mul (X := L.X) := by
    letI := (finiteTypeTopology G.X).1
    letI := (finiteTypeTopology G.X).2
    apply unique_precomp (unit G.X ⊗ₘ unit G.X) (productAffinizationUniversal G.X G.X L.X)
    change (unit G.X ⊗ₘ unit G.X) ≫ (MonObj.mul (X := H.spectrum.X) ≫ g) =
      (unit G.X ⊗ₘ unit G.X) ≫ ((g ⊗ₘ g) ≫ MonObj.mul (X := L.X))
    rw [← ha, ← Category.assoc, ← IsMonHom.mul_hom a.hom.hom,
      Category.assoc, ha, hg, ← Category.assoc, tensorHom_comp_tensorHom, hg, IsMonHom.mul_hom]
  let g' : H.spectrum ⟶ L := Grp.homMk'' g h₁ h₂
  refine ⟨g', ?_, ?_⟩
  · apply (Grp.forget _).map_injective
    change a.hom.hom ≫ g = f.hom.hom
    rw [ha, hg]
  · intro b hb
    apply (Grp.forget _).map_injective
    change b.hom.hom = g
    apply hgu
    rw [← ha]
    exact congrArg (fun p : G ⟶ L => p.hom.hom) hb

private theorem evaluate_specMap {B R : TestAlgebra k} (f : B →ₐ[k] R) :
    (evaluate ((S).map (CommAlgCat.ofHom f).op)).comp (testSectionsIso B).inv.hom = f := by
  let a := algΓAlgSpecAdjunction (CommRingCat.of k)
  let cR := (testSectionsIso R).symm.op
  let cB := (testSectionsIso B).symm.op
  let g := (CommAlgCat.ofHom f).op
  have h := a.counit.naturality g
  change (F).map ((S).map g) ≫ cB.hom = cR.hom ≫ g at h
  have hh : cR.inv ≫ (F).map ((S).map g) ≫ cB.hom = g := by
    rw [h, ← Category.assoc, cR.inv_hom_id, Category.id_comp]
  exact congrArg (fun m => m.unop.hom) hh

theorem affineCompatibility : Specs.AffineCompatibility.{u} := by
  intro k _ G H a ha
  haveI : IsAffine G.val.X.left := G.property
  haveI : IsIso a.hom.hom := by
    rw [ha]
    exact isIso_unit_of_affine G.val.X
  let ae : G.val ≅ H.spectrum :=
    Grp.mkIso (asIso a.hom.hom) (IsMonHom.one_hom _) (IsMonHom.mul_hom _)
  have hae : ae.hom = a := (Grp.forget (SchemeOver k)).map_injective rfl
  haveI : IsIso a := hae ▸ ae.isIso_hom
  let c := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso G)
  let s := algSpec (CommRingCat.of k)
  let hSpec := hopfSpec (CommRingCat.of k)
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let e' : op H.hopf ≅ op (coordinateHopf G) :=
    ff.preimageIso ((asIso a).symm ≪≫ c.symm)
  let e : H.hopf ≅ coordinateHopf G := e'.unop.symm
  have he : hSpec.map e.inv.op = inv a ≫ c.inv :=
    ff.map_preimage _
  have hg : s.map (CommAlgCat.ofHom e.inv.hom.toAlgHom).op =
      (inv a).hom.hom ≫ c.inv.hom.hom := by
    exact congrArg (fun m => m.hom.hom) he
  refine ⟨e, fun R p => ?_⟩
  have h : s.map (CommAlgCat.ofHom ((evaluate p).comp e.inv.hom.toAlgHom)).op =
      p ≫ c.inv.hom.hom := by
    change s.map ((CommAlgCat.ofHom (evaluate p)).op ≫
      (CommAlgCat.ofHom e.inv.hom.toAlgHom).op) = _
    rw [Functor.map_comp, ← evaluationFormula p, hg, ← ha]
    rw [Category.assoc, ← Category.assoc a.hom.hom]
    have hi : a.hom.hom ≫ (inv a).hom.hom = 𝟙 G.val.X := by
      exact congrArg (fun m => m.hom.hom) (IsIso.hom_inv_id a)
    rw [hi, Category.id_comp]
  rw [← h]
  exact (evaluate_specMap (B := CommAlgCat.of k (coordinateHopf G)) (R := R)
    ((evaluate p).comp e.inv.hom.toAlgHom)).symm

end
end RepTheorySurvey.Invariants.GlobalFunctions
