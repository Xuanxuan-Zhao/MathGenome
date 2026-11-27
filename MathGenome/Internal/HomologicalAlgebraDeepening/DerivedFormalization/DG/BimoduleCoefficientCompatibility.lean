import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.BimoduleCoefficientCompatibility
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift
import Mathlib.CategoryTheory.Adjunction.Mates

open CategoryTheory CategoryTheory.Functor
open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.BimoduleCoefficientCompatibility
open BalancedTensor (bimodule Degree tmul left)
open BimoduleAdjunction (ordinaryTensor ordinaryHom)
open DerivedFormalization.DGBimodule (lift lift_tmul linearMap_ext tensorPair tmul_balance)
open DerivedFormalization.DG.CoefficientLift (isoOfComponents)

universe u v w z s vA t

namespace DerivedFormalization.DG.BimoduleCoefficientCompatibility
set_option autoImplicit false
set_option quotPrecheck false

noncomputable section

variable {k : Type u} [CommRing k]

section Mates

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
variable {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
variable (a : F ⊣ G) (a' : F' ⊣ G') {I : C ⥤ C'} {J : D ⥤ D'}
variable (tau : F ⋙ J ≅ I ⋙ F')

private abbrev rightMate : G ⋙ I ⟶ J ⋙ G' := mateEquiv a a' tau.inv

private theorem rightMate_counit (Y : D) :
    tau.hom.app (G.obj Y) ≫ F'.map ((rightMate a a' tau).app Y) ≫ a'.counit.app (J.obj Y) =
      J.map (a.counit.app Y) := by
  rw [mateEquiv_counit, Iso.hom_inv_id_app_assoc]

private def comparisonOfMate [IsIso (rightMate a a' tau)] :
    AdjunctionComparison a a' I J where
  tensor := tau
  hom := asIso (rightMate a a' tau)
  unit X := by
    change I.map (a.unit.app X) ≫ (rightMate a a' tau).app (F.obj X) ≫
      G'.map (tau.hom.app X) = _
    rw [← Category.assoc, unit_mateEquiv, Category.assoc, ← G'.map_comp]
    change a'.unit.app (I.obj X) ≫ G'.map (tau.inv.app X ≫ tau.hom.app X) = _
    rw [Iso.inv_hom_id_app]
    change a'.unit.app (I.obj X) ≫ G'.map (𝟙 (F'.obj (I.obj X))) = _
    rw [G'.map_id]
    exact Category.comp_id _
  counit Y := by
    rw [← mateEquiv_counit a a' tau.inv Y, ← Functor.map_comp_assoc]
    change F'.map ((asIso (rightMate a a' tau)).inv.app Y ≫
      (asIso (rightMate a a' tau)).hom.app Y) ≫ _ = _
    rw [Iso.inv_hom_id_app]
    change F'.map (𝟙 (G'.obj (J.obj Y))) ≫ a'.counit.app (J.obj Y) = _
    rw [F'.map_id, Category.id_comp]

variable (sigma : G ⋙ I ≅ J ⋙ G')

private abbrev leftMate : I ⋙ F' ⟶ F ⋙ J := (mateEquiv a a').symm sigma.hom

private def comparisonOfRightMate [IsIso (leftMate a a' sigma)] :
    AdjunctionComparison a a' I J where
  tensor := (asIso (leftMate a a' sigma)).symm
  hom := sigma
  unit X := by
    have h := unit_mateEquiv_symm a a' sigma.hom X
    change I.map (a.unit.app X) ≫ sigma.hom.app (F.obj X) =
      a'.unit.app (I.obj X) ≫ G'.map ((leftMate a a' sigma).app X) at h
    rw [← Category.assoc, h, Category.assoc, ← G'.map_comp]
    change a'.unit.app (I.obj X) ≫ G'.map ((asIso (leftMate a a' sigma)).hom.app X ≫
      (asIso (leftMate a a' sigma)).inv.app X) = _
    rw [Iso.hom_inv_id_app]
    change a'.unit.app (I.obj X) ≫ G'.map (𝟙 (F'.obj (I.obj X))) = _
    rw [G'.map_id]
    exact Category.comp_id _
  counit Y := by
    have h := mateEquiv_counit_symm a a' sigma.hom Y
    change F'.map (sigma.hom.app Y) ≫ a'.counit.app (J.obj Y) =
      (leftMate a a' sigma).app (G.obj Y) ≫ J.map (a.counit.app Y) at h
    change F'.map (sigma.inv.app Y) ≫
      (leftMate a a' sigma).app (G.obj Y) ≫ J.map (a.counit.app Y) = _
    rw [← h, ← F'.map_comp_assoc, Iso.inv_hom_id_app]
    change F'.map (𝟙 (G'.obj (J.obj Y))) ≫ a'.counit.app (J.obj Y) = _
    rw [F'.map_id, Category.id_comp]


end Mates


section Coordinates

variable {O : Type w} {a₀ : DGCategoryData.{u,v} k O} {a₁ : DGCategoryData.{u,s} k O}


private abbrev ArrowCoordinates (a₀ : DGCategoryData.{u,v} k O)
    (a₁ : DGCategoryData.{u,s} k O) :=
  ∀ a b : O, ∀ i : ℤ, (a₀.hom a b).X i ≃ₗ[k] (a₁.hom a b).X i

private structure ModuleCoordinates (e : ArrowCoordinates a₀ a₁)
    (M : RightDGModuleModel (DGCategoryModel.mk O a₀)) (N : RightDGModuleModel (DGCategoryModel.mk O a₁)) where
  term : ∀ a i, (M.complex a).X i ≃ₗ[k] (N.complex a).X i
  d (a : O) (i : ℤ) (x : (M.complex a).X i) :
    term a (i+1) ((M.complex a).d i (i+1) x) = (N.complex a).d i (i+1) (term a i x)
  act {a b : O} (i j n : ℤ) (h : i+j=n) (x : (M.complex b).X i)
      (f : (a₀.hom a b).X j) :
    term a n (M.act i j n h x f) = N.act i j n h (term b i x) (e a b j f)

private structure FunctorCoordinates (e : ArrowCoordinates a₀ a₁)
    (I : RightDGModuleModel (DGCategoryModel.mk O a₀) ⥤ RightDGModuleModel (DGCategoryModel.mk O a₁)) where
  module (M : RightDGModuleModel (DGCategoryModel.mk O a₀)) : ModuleCoordinates e M (I.obj M)
  map {M N : RightDGModuleModel (DGCategoryModel.mk O a₀)} (f : M ⟶ N) (a : O) (i : ℤ)
      (x : (M.complex a).X i) :
    (module N).term a i ((f.app a).f i x) = ((I.map f).app a).f i ((module M).term a i x)

private def ModuleCoordinates.symm {e : ArrowCoordinates a₀ a₁}
    {M : RightDGModuleModel (DGCategoryModel.mk O a₀)} {N : RightDGModuleModel (DGCategoryModel.mk O a₁)}
    (c : ModuleCoordinates e M N) :
    ModuleCoordinates (fun a b i => (e a b i).symm) N M where
  term a i := (c.term a i).symm
  d a i x := by
    apply (c.term a (i+1)).injective
    rw [LinearEquiv.apply_symm_apply, c.d, LinearEquiv.apply_symm_apply]
  act i j n h x f := by
    apply (c.term _ n).injective
    rw [LinearEquiv.apply_symm_apply, c.act, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]

private def ModuleCoordinates.iso {e : ArrowCoordinates a₀ a₁}
    {M : RightDGModuleModel (DGCategoryModel.mk O a₀)} {N : RightDGModuleModel (DGCategoryModel.mk O a₁)} {P : RightDGModuleModel (DGCategoryModel.mk O a₁)}
    (cN : ModuleCoordinates e M N) (cP : ModuleCoordinates e M P) : N ≅ P :=
  isoOfComponents (fun a i => (cN.term a i).symm.trans (cP.term a i))
    (fun a i x => by
      obtain ⟨x, rfl⟩ := (cN.term a i).surjective x
      rw [← cN.d]
      simpa using cP.d a i x)
    (by
      intro a b i j n h x f
      obtain ⟨x, rfl⟩ := (cN.term b i).surjective x
      obtain ⟨f, rfl⟩ := (e a b j).surjective f
      rw [← cN.act]
      simpa using cP.act i j n h x f)

private theorem ModuleCoordinates.iso_apply {e : ArrowCoordinates a₀ a₁}
    {M : RightDGModuleModel (DGCategoryModel.mk O a₀)} {N : RightDGModuleModel (DGCategoryModel.mk O a₁)} {P : RightDGModuleModel (DGCategoryModel.mk O a₁)}
    (cN : ModuleCoordinates e M N) (cP : ModuleCoordinates e M P)
    (a : O) (i : ℤ) (x : (M.complex a).X i) :
    (((cN.iso cP).hom.app a).f i) (cN.term a i x) = cP.term a i x :=
  congrArg (cP.term a i) ((cN.term a i).symm_apply_apply x)

private def ModuleCoordinates.trans {a₂ : DGCategoryData.{u,t} k O}
    {e : ArrowCoordinates a₀ a₁} {f : ArrowCoordinates a₁ a₂}
    {M : RightDGModuleModel (DGCategoryModel.mk O a₀)}
    {N : RightDGModuleModel (DGCategoryModel.mk O a₁)}
    {P : RightDGModuleModel (DGCategoryModel.mk O a₂)}
    (c : ModuleCoordinates e M N) (d : ModuleCoordinates f N P) :
    ModuleCoordinates (fun a b i => (e a b i).trans (f a b i)) M P where
  term a i := (c.term a i).trans (d.term a i)
  d a i x := by simp only [LinearEquiv.trans_apply, c.d, d.d]
  act i j n h x g := by simp only [LinearEquiv.trans_apply, c.act, d.act]

end Coordinates

section Conjugation

open RightDGModule (GradedHom)
open HomComplex (component)

variable {O : Type w} {b₀ : DGCategoryData.{u,v} k O} {b₁ : DGCategoryData.{u,s} k O}
variable {e : ArrowCoordinates b₀ b₁}
variable {U V : RightDGModuleModel (DGCategoryModel.mk O b₀)}
variable {U' V' : RightDGModuleModel (DGCategoryModel.mk O b₁)}
variable (cU : ModuleCoordinates e U U') (cV : ModuleCoordinates e V V') {r : ℤ}

private theorem graded_ext_values {g h : GradedHom U V r}
    (e : ∀ a i n (p : i+r=n) x, component g a i n p x = component h a i n p x) :
    g = h := by
  apply GradedHom.ext
  intro a i n p
  apply ModuleCat.hom_ext
  exact LinearMap.ext (e a i n p)

private def conjugateGraded (g : GradedHom U V r) : GradedHom U' V' r :=
  GradedHom.mk (fun a i n h => ModuleCat.ofHom ((cV.term a n).toLinearMap.comp
    ((component g a i n h).hom.comp (cU.term a i).symm.toLinearMap))) (by
    intro a b i j n ir nr hij hi hn x f
    obtain ⟨x, rfl⟩ := (cU.term b i).surjective x
    obtain ⟨f, rfl⟩ := (e a b j).surjective f
    change cV.term a nr (component g a n nr hn
      ((cU.term a n).symm (U'.act i j n hij (cU.term b i x) (e a b j f)))) =
      V'.act ir j nr _ (cV.term b ir (component g b i ir hi
        ((cU.term b i).symm (cU.term b i x)))) (e a b j f)
    rw [← cU.act, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
      GradedHom.comm_act, cV.act])

private theorem conjugateGraded_eval (g : GradedHom U V r)
    (a : O) (i n : ℤ) (h : i+r=n) (x : (U.complex a).X i) :
    component (conjugateGraded cU cV g) a i n h (cU.term a i x) =
      cV.term a n (component g a i n h x) :=
  congrArg (fun y => cV.term a n (component g a i n h y)) ((cU.term a i).symm_apply_apply x)

private theorem conjugateGraded_bijective :
    Function.Bijective (conjugateGraded cU cV (r := r)) := by
  constructor
  · intro g h E
    apply graded_ext_values
    intro a i n p x
    apply (cV.term a n).injective
    rw [← conjugateGraded_eval cU cV g, E, conjugateGraded_eval]
  · intro g
    refine ⟨conjugateGraded cU.symm cV.symm g, ?_⟩
    apply graded_ext_values
    intro a i n p x
    obtain ⟨x, rfl⟩ := (cU.term a i).surjective x
    rw [conjugateGraded_eval]
    have h := conjugateGraded_eval cU.symm cV.symm g a i n p (cU.term a i x)
    change component (conjugateGraded cU.symm cV.symm g) a i n p
      ((cU.term a i).symm (cU.term a i x)) =
      (cV.term a n).symm (component g a i n p (cU.term a i x)) at h
    rw [LinearEquiv.symm_apply_apply] at h
    rw [h, LinearEquiv.apply_symm_apply]

end Conjugation

private theorem complex_iso_inv_hom_apply {X Y : ModuleCochain.{u,v} k}
    (e : X ≅ Y) (i : ℤ) (x : Y.X i) :
    e.hom.f i (e.inv.f i x) = x := by
  have h := congrArg (fun f : Y ⟶ Y => f.f i x) e.inv_hom_id
  exact h

private theorem complex_iso_hom_inv_apply {X Y : ModuleCochain.{u,v} k}
    (e : X ≅ Y) (i : ℤ) (x : X.X i) :
    e.inv.f i (e.hom.f i x) = x := complex_iso_inv_hom_apply e.symm i x

section BalancedMap

variable {OA : Type w} {OB : Type z}
variable {a₀ : DGCategoryData.{u,v} k OA} {a₁ : DGCategoryData.{u,s} k OA}
variable {b₀ : DGCategoryData.{u,v} k OB} {b₁ : DGCategoryData.{u,s} k OB}

variable {T : BalancedTensor.Bimodule (DGCategoryModel.mk OA a₀) (DGCategoryModel.mk OB b₀)} {T' : BalancedTensor.Bimodule (DGCategoryModel.mk OA a₁) (DGCategoryModel.mk OB b₁)}
variable {eA : ArrowCoordinates a₀ a₁} {eB : ArrowCoordinates b₀ b₁}

private def balancedMap {M : RightDGModuleModel (DGCategoryModel.mk OA a₀)} {M' : RightDGModuleModel (DGCategoryModel.mk OA a₁)}
    (cM : ModuleCoordinates eA M M') (cT : ∀ a : OA, ModuleCoordinates (k := k) (a₀ := b₀) (a₁ := b₁) eB (T.obj a) (T'.obj a))
    (hT : ∀ (b : OB) {a a' : OA} (i j n : ℤ) (h : i+j=n) (f : (a₀.hom a a').X i)
      (x : ((T.obj a).complex b).X j),
      (cT a').term b n (left T b i j n h f x) =
        left T' b i j n h (eA a a' i f) ((cT a).term b j x))
    (b : OB) (n : ℤ) : Degree T M b n →ₗ[k] Degree T' M' b n :=
  lift T M (fun a i j h => (tensorPair T' M' b a i j n h).compl₁₂
    (cM.term a i).toLinearMap ((cT a).term b j).toLinearMap) (by
    intro a a' i l j h m f t
    change tmul T' M' b a (i+l) j n h (cM.term a (i+l) (M.act i l (i+l) rfl m f))
      ((cT a).term b j t) =
        tmul T' M' b a' i (l+j) n _ (cM.term a' i m) ((cT a').term b (l+j)
          (left T b l j (l+j) rfl f t))
    rw [cM.act, hT]
    exact tmul_balance T' M' b i l j (i+l) (l+j) n rfl rfl h
      (cM.term a' i m) (eA a a' l f) ((cT a).term b j t))

private theorem balancedMap_tmul {M : RightDGModuleModel (DGCategoryModel.mk OA a₀)} {M' : RightDGModuleModel (DGCategoryModel.mk OA a₁)}
    (cM : ModuleCoordinates eA M M') (cT : ∀ a : OA, ModuleCoordinates (k := k) (a₀ := b₀) (a₁ := b₁) eB (T.obj a) (T'.obj a))
    (hT : ∀ (b : OB) {a a' : OA} (i j n : ℤ) (h : i+j=n) (f : (a₀.hom a a').X i)
      (x : ((T.obj a).complex b).X j),
      (cT a').term b n (left T b i j n h f x) =
        left T' b i j n h (eA a a' i f) ((cT a).term b j x))
    (b : OB) (a : OA) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    balancedMap cM cT hT b n (tmul T M b a i j n h m t) =
      tmul T' M' b a i j n h (cM.term a i m) ((cT a).term b j t) :=
  lift_tmul T M _ _ a i j h m t

private def balancedEquiv {M : RightDGModuleModel (DGCategoryModel.mk OA a₀)} {M' : RightDGModuleModel (DGCategoryModel.mk OA a₁)}
    (cM : ModuleCoordinates eA M M') (cT : ∀ a : OA, ModuleCoordinates (k := k) (a₀ := b₀) (a₁ := b₁) eB (T.obj a) (T'.obj a))
    (hT : ∀ (b : OB) {a a' : OA} (i j n : ℤ) (h : i+j=n) (f : (a₀.hom a a').X i)
      (x : ((T.obj a).complex b).X j),
      (cT a').term b n (left T b i j n h f x) =
        left T' b i j n h (eA a a' i f) ((cT a).term b j x))
    (b : OB) (n : ℤ) : Degree T M b n ≃ₗ[k] Degree T' M' b n := by
  have hinv : ∀ (b : OB) {a a' : OA} (i j n : ℤ) (h : i+j=n) (f : (a₁.hom a a').X i)
      (x : ((T'.obj a).complex b).X j),
      (cT a').symm.term b n (left T' b i j n h f x) =
        left T b i j n h ((eA a a' i).symm f) ((cT a).symm.term b j x) := by
    intro b a a' i j n h f x
    obtain ⟨f, rfl⟩ := (eA a a' i).surjective f
    obtain ⟨x, rfl⟩ := ((cT a).term b j).surjective x
    rw [← hT b i j n h f x]
    simp [ModuleCoordinates.symm]
  let F := balancedMap cM cT hT b n
  let G := balancedMap cM.symm (fun a => (cT a).symm) hinv b n
  refine LinearEquiv.ofLinearMap F G ?_ ?_
  all_goals
    apply linearMap_ext
    intro a i j h m t
    simp [F, G, balancedMap_tmul, ModuleCoordinates.symm]

private theorem balancedEquiv_tmul {M : RightDGModuleModel (DGCategoryModel.mk OA a₀)} {M' : RightDGModuleModel (DGCategoryModel.mk OA a₁)}
    (cM : ModuleCoordinates eA M M') (cT : ∀ a : OA, ModuleCoordinates (k := k) (a₀ := b₀) (a₁ := b₁) eB (T.obj a) (T'.obj a))
    (hT : ∀ (b : OB) {a a' : OA} (i j n : ℤ) (h : i+j=n) (f : (a₀.hom a a').X i)
      (x : ((T.obj a).complex b).X j),
      (cT a').term b n (left T b i j n h f x) =
        left T' b i j n h (eA a a' i f) ((cT a).term b j x))
    (b : OB) (a : OA) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) :
    balancedEquiv cM cT hT b n (tmul T M b a i j n h m t) =
      tmul T' M' b a i j n h (cM.term a i m) ((cT a).term b j t) :=
  balancedMap_tmul cM cT hT b a i j n h m t

private theorem tensor_term_ext {M : RightDGModuleModel (DGCategoryModel.mk OA a₀)} {b : OB} {n : ℤ}
    {U V : Type*} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    (e : Degree T M b n ≃ₗ[k] U) (f g : U →ₗ[k] V)
    (h : ∀ a i j h x y,
      f (e (tmul T M b a i j n h x y)) = g (e (tmul T M b a i j n h x y))) :
    ∀ x, f x = g x := by
  have he : f.comp e.toLinearMap = g.comp e.toLinearMap := linearMap_ext T M h
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  exact DFunLike.congr_fun he x

end BalancedMap

section Tensor

variable {OA : Type w} {OB : Type z}
variable {a₀ : DGCategoryData.{u,max v w z} k OA} {a₁ : DGCategoryData.{u,max s w z} k OA}
variable {b₀ : DGCategoryData.{u,max v w z} k OB} {b₁ : DGCategoryData.{u,max s w z} k OB}

variable {T : BalancedTensor.Bimodule (DGCategoryModel.mk OA a₀) (DGCategoryModel.mk OB b₀)} {T' : BalancedTensor.Bimodule (DGCategoryModel.mk OA a₁) (DGCategoryModel.mk OB b₁)}
variable {eA : ArrowCoordinates a₀ a₁} {eB : ArrowCoordinates b₀ b₁}

variable {m : SignedModels.{u,v,w,z} T} {m' : SignedModels.{u,s,w,z} T'}
variable {I : RightDGModuleModel (DGCategoryModel.mk OA a₀) ⥤ RightDGModuleModel (DGCategoryModel.mk OA a₁)}
variable {J : RightDGModuleModel (DGCategoryModel.mk OB b₀) ⥤ RightDGModuleModel (DGCategoryModel.mk OB b₁)}
variable (cA : FunctorCoordinates eA I) (cB : FunctorCoordinates eB J)
variable (cT : ∀ a : OA, ModuleCoordinates (k := k) (a₀ := b₀) (a₁ := b₁) eB (T.obj a) (T'.obj a))
variable (hT : ∀ (b : OB) {a a' : OA} (i j n : ℤ) (h : i+j=n) (f : (a₀.hom a a').X i)
    (x : ((T.obj a).complex b).X j),
    (cT a').term b n (left T b i j n h f x) =
      left T' b i j n h (eA a a' i f) ((cT a).term b j x))

local notation "F" => (m.tensor.functor ⋙ BalancedTensor.RightModule.toOrdinary)
local notation "F'" => (m'.tensor.functor ⋙ BalancedTensor.RightModule.toOrdinary)
local notation "H" => (m.hom.functor ⋙ BalancedTensor.RightModule.toOrdinary)
local notation "H'" => (m'.hom.functor ⋙ BalancedTensor.RightModule.toOrdinary)

private def tensorTerm (M : RightDGModuleModel (DGCategoryModel.mk OA a₀)) (b : OB) (n : ℤ) :
    ((J.obj ((F).obj M)).complex b).X n ≃ₗ[k] (((F').obj (I.obj M)).complex b).X n :=
  ((cB.module ((F).obj M)).term b n).symm.trans
    ((m.tensor.degree M b n).symm.trans
      ((balancedEquiv (cA.module M) cT hT b n).trans (m'.tensor.degree (I.obj M) b n)))

private theorem tensorTerm_tmul (M : RightDGModuleModel (DGCategoryModel.mk OA a₀)) (b : OB) (a : OA)
    (i j n : ℤ) (h : i+j=n) (x : (M.complex a).X i) (y : ((T.obj a).complex b).X j) :
    tensorTerm (m := m) (m' := m') cA cB cT hT M b n
      ((cB.module ((F).obj M)).term b n (m.tensor.degree M b n (tmul T M b a i j n h x y))) =
    m'.tensor.degree (I.obj M) b n
      (tmul T' (I.obj M) b a i j n h ((cA.module M).term a i x) ((cT a).term b j y)) := by
  simp only [tensorTerm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, balancedEquiv_tmul]

private def tensorIso (M : RightDGModuleModel (DGCategoryModel.mk OA a₀)) : J.obj ((F).obj M) ≅ (F').obj (I.obj M) := by
  let e := tensorTerm (m := m) (m' := m') cA cB cT hT M
  let c := cB.module ((F).obj M)
  refine isoOfComponents e ?_ ?_
  · intro b n x
    let D := ((J.obj ((F).obj M)).complex b).d n (n+1)
    let D' := (((F').obj (I.obj M)).complex b).d n (n+1)
    refine tensor_term_ext ((m.tensor.degree M b n).trans (c.term b n))
      ((e b (n+1)).toLinearMap.comp D.hom) (D'.hom.comp (e b n).toLinearMap) ?_ x
    intro a i j h x y
    change e b (n+1) (D (c.term b n (m.tensor.degree M b n (tmul T M b a i j n h x y)))) =
      D' (e b n (c.term b n (m.tensor.degree M b n (tmul T M b a i j n h x y))))
    dsimp only [D, D', c, e]
    rw [← (cB.module ((F).obj M)).d, tensorTerm_tmul]
    change (tensorTerm (m := m) (m' := m') cA cB cT hT M b (n+1)) ((cB.module ((F).obj M)).term b (n+1)
      (((m.tensor.functor.obj M).complex b).d n (n+1)
        (m.tensor.degree M b n (tmul T M b a i j n h x y)))) =
      ((m'.tensor.functor.obj (I.obj M)).complex b).d n (n+1) _
    rw [m.tensor.d_tmul, m'.tensor.d_tmul]
    simp only [_root_.map_add, Units.smul_def, _root_.map_zsmul, tensorTerm_tmul,
      (cA.module M).d, (cT a).d]
  · intro b d n l q eDeg x f
    obtain ⟨f, rfl⟩ := (eB b d l).surjective f
    let A := ((J.obj ((F).obj M)).act n l q eDeg).flip (eB b d l f)
    let A' := (((F').obj (I.obj M)).act n l q eDeg).flip (eB b d l f)
    refine tensor_term_ext ((m.tensor.degree M d n).trans (c.term d n))
      ((e b q).toLinearMap.comp A) (A'.comp (e d n).toLinearMap) ?_ x
    intro a i j h x y
    change e b q (A (c.term d n (m.tensor.degree M d n (tmul T M d a i j n h x y)))) =
      A' (e d n (c.term d n (m.tensor.degree M d n (tmul T M d a i j n h x y))))
    dsimp only [A, A', c, e, LinearMap.flip_apply]
    rw [← (cB.module ((F).obj M)).act, tensorTerm_tmul]
    change (tensorTerm (m := m) (m' := m') cA cB cT hT M b q) ((cB.module ((F).obj M)).term b q
      ((m.tensor.functor.obj M).act n l q eDeg (m.tensor.degree M d n (tmul T M d a i j n h x y)) f)) =
      (m'.tensor.functor.obj (I.obj M)).act n l q eDeg _ (eB b d l f)
    rw [m.tensor.act_tmul, m'.tensor.act_tmul, tensorTerm_tmul, (cT a).act]

private theorem tensorIso_tmul (M : RightDGModuleModel (DGCategoryModel.mk OA a₀)) (b : OB) (a : OA)
    (i j n : ℤ) (h : i+j=n) (x : (M.complex a).X i) (y : ((T.obj a).complex b).X j) :
    (((tensorIso (m := m) (m' := m') cA cB cT hT M).hom.app b).f n)
      ((cB.module ((F).obj M)).term b n (m.tensor.degree M b n (tmul T M b a i j n h x y))) =
    m'.tensor.degree (I.obj M) b n
      (tmul T' (I.obj M) b a i j n h ((cA.module M).term a i x) ((cT a).term b j y)) :=
  tensorTerm_tmul cA cB cT hT M b a i j n h x y

private def tensorComparison : F ⋙ J ≅ I ⋙ F' :=
  NatIso.ofComponents (tensorIso (m := m) (m' := m') cA cB cT hT) (by
    intro M N f
    apply RightDGModuleModel.hom_ext
    intro b
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    let c := cB.module ((F).obj M)
    refine tensor_term_ext ((m.tensor.degree M b n).trans (c.term b n)) _ _ ?_
    intro a i j h x y
    change (((tensorIso (m := m) (m' := m') cA cB cT hT N).hom.app b).f n)
      (((J.map ((F).map f)).app b).f n (c.term b n (m.tensor.degree M b n (tmul T M b a i j n h x y)))) =
      (((F').map (I.map f)).app b).f n
        ((((tensorIso (m := m) (m' := m') cA cB cT hT M).hom.app b).f n)
          (c.term b n (m.tensor.degree M b n (tmul T M b a i j n h x y))))
    dsimp only [c]
    rw [← cB.map, tensorIso_tmul]
    change (((tensorIso (m := m) (m' := m') cA cB cT hT N).hom.app b).f n) ((cB.module ((F).obj N)).term b n
      (((m.tensor.functor.map f).app b).f n (m.tensor.degree M b n (tmul T M b a i j n h x y)))) =
      ((m'.tensor.functor.map (I.map f)).app b).f n _
    rw [m.tensor.map_tmul, m'.tensor.map_tmul, tensorIso_tmul, cA.map])


open HomComplex (gradedHom component)

private theorem strictMate_eval (N : RightDGModuleModel (DGCategoryModel.mk OB b₀))
    (a : OA) (b : OB) (r i n : ℤ) (h : i+r=n)
    (g : gradedHom (T.obj a) N r) (x : ((T.obj a).complex b).X i) :
    let tau := tensorComparison (m := m) (m' := m') cA cB cT hT
    let sigma := rightMate m.adjunction m'.adjunction tau
    component ((m'.hom.objectwise (J.obj N) a).inv.f r
      (((sigma.app N).app a).f r ((cA.module ((H).obj N)).term a r
        ((m.hom.objectwise N a).hom.f r g))))
      b i n h ((cT a).term b i x) = (cB.module N).term b n (component g b i n h x) := by
  intro tau sigma
  let y := (m.hom.objectwise N a).hom.f r g
  let z := ((sigma.app N).app a).f r ((cA.module ((H).obj N)).term a r y)
  let g' := (m'.hom.objectwise (J.obj N) a).inv.f r z
  let h' : r+i=n := by omega
  let p := m.tensor.degree ((H).obj N) b n (tmul T ((H).obj N) b a r i n h' y x)
  have eq := congrArg
    (fun f : J.obj ((F).obj ((H).obj N)) ⟶ J.obj N =>
      (f.app b).f n ((cB.module ((F).obj ((H).obj N))).term b n p))
    (rightMate_counit m.adjunction m'.adjunction tau N)
  change ((m'.adjunction.counit.app (J.obj N)).app b).f n
      ((((F').map (sigma.app N)).app b).f n
        (((tau.hom.app ((H).obj N)).app b).f n
          ((cB.module ((F).obj ((H).obj N))).term b n p))) =
    ((J.map (m.adjunction.counit.app N)).app b).f n
      ((cB.module ((F).obj ((H).obj N))).term b n p) at eq
  dsimp only [p, tau, tensorComparison, NatIso.ofComponents_hom_app] at eq
  have hmap := cB.map (m.adjunction.counit.app N) b n p
  rw [tensorIso_tmul] at eq
  have eq := eq.trans hmap.symm
  have hmap' := m'.tensor.map_tmul (sigma.app N) a b r i n h'
    ((cA.module ((H).obj N)).term a r y) ((cT a).term b i x)
  have eq := (congrArg (fun t => ((m'.adjunction.counit.app (J.obj N)).app b).f n t)
    hmap').symm.trans eq
  have hz : (m'.hom.objectwise (J.obj N) a).hom.f r g' = z :=
    complex_iso_inv_hom_apply _ _ _
  have hs := m'.laws.counit (J.obj N) a b r i n h' g' ((cT a).term b i x)
  have hs' := (congrArg (fun g => ((m'.adjunction.counit.app (J.obj N)).app b).f n
      (m'.tensor.degree ((H').obj (J.obj N)) b n
        (tmul T' ((H').obj (J.obj N)) b a r i n h' g ((cT a).term b i x)))) hz).symm.trans hs
  have hr := congrArg ((cB.module N).term b n) (m.laws.counit N a b r i n h' g x)
  exact hs'.symm.trans (eq.trans hr)

private theorem strictMate_isIso :
    IsIso (rightMate m.adjunction m'.adjunction
      (tensorComparison (m := m) (m' := m') cA cB cT hT)) := by
  let tau := tensorComparison (m := m) (m' := m') cA cB cT hT
  let sigma := rightMate m.adjunction m'.adjunction tau
  change IsIso sigma
  apply (NatTrans.isIso_iff_isIso_app sigma).mpr
  intro N
  let f := sigma.app N
  have hf (a : OA) (r : ℤ) : Function.Bijective ((f.app a).f r) := by
    let l := m.hom.objectwise N a
    let l' := m'.hom.objectwise (J.obj N) a
    let c := (cA.module ((H).obj N)).term a r
    have left_bij : Function.Bijective (fun g => c (l.hom.f r g)) :=
      c.bijective.comp ⟨fun g h e => by
        have eq := congrArg (fun x => l.inv.f r x) e
        change l.inv.f r (l.hom.f r g) = l.inv.f r (l.hom.f r h) at eq
        rw [complex_iso_hom_inv_apply l r g, complex_iso_hom_inv_apply l r h] at eq
        exact eq,
        fun y => ⟨l.inv.f r y, complex_iso_inv_hom_apply l r y⟩⟩
    have right_bij : Function.Bijective (l'.inv.f r) :=
      ⟨fun g h e => by
        have eq := congrArg (fun x => l'.hom.f r x) e
        change l'.hom.f r (l'.inv.f r g) = l'.hom.f r (l'.inv.f r h) at eq
        rw [complex_iso_inv_hom_apply l' r g, complex_iso_inv_hom_apply l' r h] at eq
        exact eq,
        fun y => ⟨l'.hom.f r y, complex_iso_hom_inv_apply l' r y⟩⟩
    have coord : ∀ g, l'.inv.f r ((f.app a).f r (c (l.hom.f r g))) =
        conjugateGraded (cT a) (cB.module N) g := by
      intro g
      apply graded_ext_values
      intro b i n h x
      obtain ⟨x, rfl⟩ := ((cT a).term b i).surjective x
      rw [conjugateGraded_eval]
      exact strictMate_eval cA cB cT hT N a b r i n h g x
    apply (left_bij.of_comp_iff _).mp
    apply (right_bij.of_comp_iff' _).mp
    change Function.Bijective (fun g => l'.inv.f r ((f.app a).f r (c (l.hom.f r g))))
    rw [funext coord]
    exact conjugateGraded_bijective (cT a) (cB.module N)
  let e : ∀ a r, _ ≃ₗ[k] _ :=
    fun a r => LinearEquiv.ofBijective ((f.app a).f r).hom (hf a r)
  let iso := isoOfComponents e
    (fun a r x => by
      have h := congrArg (fun g => g x) ((f.app a).comm r (r+1))
      exact h.symm)
    (fun {_ _} i j n h x g => f.comm_act i j n h x g)
  have he : iso.hom = f := by
    apply RightDGModuleModel.hom_ext
    intro a
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    change (e a i).toLinearMap = ((f.app a).f i).hom
    rfl
  change IsIso f
  rw [← he]
  infer_instance

include hT in
private theorem strictComparisonFromCoordinates :
    ∃ e : AdjunctionComparison m.adjunction m'.adjunction I J,
      StrictComparisonLaws.{u,v,w,z,s} (m := m) (m' := m') e (Equiv.refl _) (Equiv.refl _)
        (fun M => (cA.module M).term) (fun N => (cB.module N).term)
        (fun a => (cB.module (T.obj a)).iso (cT a)) := by
  let tau := tensorComparison (m := m) (m' := m') cA cB cT hT
  let : IsIso (rightMate m.adjunction m'.adjunction tau) := strictMate_isIso cA cB cT hT
  let e := comparisonOfMate m.adjunction m'.adjunction tau
  refine ⟨e, ?_, ?_⟩
  · intro M a b i j n h x y
    change (((tau.hom.app M).app b).f n)
      ((cB.module ((F).obj M)).term b n (m.tensor.degree M b n (tmul T M b a i j n h x y))) =
      m'.tensor.degree (I.obj M) b n
        (tmul T' (I.obj M) b a i j n h ((cA.module M).term a i x)
          ((((cB.module (T.obj a)).iso (cT a)).hom.app b).f j ((cB.module (T.obj a)).term b j y)))
    rw [ModuleCoordinates.iso_apply]
    exact tensorIso_tmul cA cB cT hT M b a i j n h x y
  · intro N a b r i n h g x
    change component ((m'.hom.objectwise (J.obj N) a).inv.f r
      ((((rightMate m.adjunction m'.adjunction tau).app N).app a).f r
        ((cA.module ((H).obj N)).term a r ((m.hom.objectwise N a).hom.f r g))))
      b i n h ((((cB.module (T.obj a)).iso (cT a)).hom.app b).f i
        ((cB.module (T.obj a)).term b i x)) = _
    rw [ModuleCoordinates.iso_apply]
    exact strictMate_eval cA cB cT hT N a b r i n h g x


end Tensor

section CoefficientRepresentations

open BimoduleAdjunction (ModuleEquiv asMixed restrictLifted)
open Specs.DerivedFormalization.DG.CoefficientLift (liftCategory)
open Specs.DerivedFormalization.DG.DerivedCoefficientLift (strictTransition)
open Specs.DerivedFormalization.DG.AmbientDerived (category transportToAmbient)

private def liftCoordinates {B : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel B} {N : RightDGModuleModel (liftCategory.{u,v,w,t} B)}
    (c : ModuleEquiv (asMixed M)
      (restrictLifted.{u,v,w,max v t,t} (asMixed N))) :
    ModuleCoordinates (a₀ := B.toData) (a₁ := (liftCategory.{u,v,w,t} B).toData)
      (fun _ _ _ => ULift.moduleEquiv.symm) M N where
  term := c.degree
  d := c.comm_d
  act i j n h x g := c.comm_act i j n h x g

private def transitionCoordinates (B : DGCategoryModel.{u,v,w} k) :
    FunctorCoordinates (a₀ := (category.{u,v,w,t} B).toData)
      (a₁ := (category.{u,v,w,max t s} B).toData)
      (fun _ _ _ => ULift.moduleEquiv.trans ULift.moduleEquiv.symm)
      (strictTransition.{u,v,w,t,s} B) where
  module _ :=
    { term := fun _ _ => ULift.moduleEquiv.symm
      d := fun _ _ _ => rfl
      act := fun _ _ _ _ _ _ => rfl }
  map _ _ _ _ := rfl

private def nativeCoordinates (B : DGCategoryModel.{u,max v w t,w} k) :
    FunctorCoordinates (a₀ := B.toData) (a₁ := (category.{u,max v w t,w,t} B).toData)
      (fun _ _ _ => ULift.moduleEquiv.symm) (transportToAmbient.{u,v,w,t} B) where
  module _ :=
    { term := fun _ _ => LinearEquiv.refl k _
      d := fun _ _ _ => rfl
      act := fun _ _ _ _ _ _ => rfl }
  map _ _ _ _ := rfl

theorem nativeStrictComparison : NativeStrictComparison.{u,v,w,z} := by
  intro k _ A B T m m'
  dsimp only
  let cA := nativeCoordinates.{u,v,w,max v w z} A
  let cB := nativeCoordinates.{u,v,z,max v w z} B
  let cT (a : A.Obj) := liftCoordinates (m'.comparison a)
  have hT : ∀ (b : B.Obj) {a a' : A.Obj} (i j n : ℤ) (h : i+j=n)
      (f : (A.hom a a').X i) (x : ((T.obj a).complex b).X j),
      (cT a').term b n (left T b i j n h f x) =
        left m'.bimodule b i j n h (ULift.up f) ((cT a).term b j x) := by
    intro b a a' i j n h f x
    exact m'.comparisonLaws.left_action b i j n h f x
  obtain ⟨e, he⟩ := strictComparisonFromCoordinates
    (m := m) (m' := m'.models) cA cB cT hT
  refine ⟨fun a => (cB.module (T.obj a)).iso (cT a), e, ?_, he⟩
  intro a b n x
  exact ModuleCoordinates.iso_apply (cB.module (T.obj a)) (cT a) b n x

theorem ambientStrictComparison : AmbientStrictComparison.{u,v,w,z,vA,t,s} := by
  intro k _ A B T m m'
  dsimp only
  let cA := transitionCoordinates.{u,vA,w,s,max v z t} A
  let cB := transitionCoordinates.{u,v,z,s,max vA w t} B
  let lo (a : A.Obj) := liftCoordinates (m.comparison a)
  let hi (a : A.Obj) := liftCoordinates (m'.comparison a)
  let cT (a : A.Obj) := (lo a).symm.trans (hi a)
  have hT : ∀ (b : B.Obj) {a a' : A.Obj} (i j n : ℤ) (h : i+j=n)
      (f : ((category.{u,vA,w,max v z t} A).hom a a').X i)
      (x : ((m.bimodule.obj a).complex b).X j),
      (cT a').term b n (left m.bimodule b i j n h f x) =
        left m'.bimodule b i j n h (ULift.up f.down) ((cT a).term b j x) := by
    intro b a a' i j n h f x
    obtain ⟨x, rfl⟩ := ((lo a).term b j).surjective x
    have hlo := m.comparisonLaws.left_action b i j n h f.down x
    have hhi := m'.comparisonLaws.left_action b i j n h f.down x
    change (hi a').term b n (((lo a').term b n).symm
      (left m.bimodule b i j n h f ((lo a).term b j x))) = _
    change (lo a').term b n (left T b i j n h f.down x) =
      left m.bimodule b i j n h f ((lo a).term b j x) at hlo
    rw [← hlo]
    change (hi a').term b n (((lo a').term b n).symm
      ((lo a').term b n (left T b i j n h f.down x))) =
      left m'.bimodule b i j n h (ULift.up f.down)
        ((hi a).term b j (((lo a).term b j).symm ((lo a).term b j x)))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact hhi
  obtain ⟨e, he⟩ := strictComparisonFromCoordinates
    (m := m.models) (m' := m'.models)
    (eA := fun _ _ _ => ULift.moduleEquiv.trans ULift.moduleEquiv.symm)
    (eB := fun _ _ _ => ULift.moduleEquiv.trans ULift.moduleEquiv.symm)
    cA cB cT (fun b {_ _} i j n h f x => hT b i j n h f x)
  refine ⟨fun a => (cB.module (m.bimodule.obj a)).iso (cT a), e, ?_, he⟩
  intro a b n x
  change (((cB.module (m.bimodule.obj a)).iso (cT a)).hom.app b).f n
      ((cB.module (m.bimodule.obj a)).term b n ((lo a).term b n x)) = (hi a).term b n x
  exact (ModuleCoordinates.iso_apply (cB.module (m.bimodule.obj a)) (cT a)
    b n ((lo a).term b n x)).trans (congrArg ((hi a).term b n) (((lo a).term b n).symm_apply_apply x))

end CoefficientRepresentations

section DerivedMates

variable {C E C' E' X Y X' Y' : Type*}
variable [Category* C] [Category* E] [Category* C'] [Category* E']
variable [Category* X] [Category* Y] [Category* X'] [Category* Y']
variable {F : C ⥤ E} {G : E ⥤ C} {F' : C' ⥤ E'} {G' : E' ⥤ C'}
variable {L : X ⥤ Y} {R : Y ⥤ X} {L' : X' ⥤ Y'} {R' : Y' ⥤ X'}
variable {I : C ⥤ C'} {J : E ⥤ E'} {ID : X ⥤ X'} {JD : Y ⥤ Y'}
variable {ad : F ⊣ G} {ad' : F' ⊣ G'} {adD : L ⊣ R} {adD' : L' ⊣ R'}
variable {U : C ⥤ X} {V : E ⥤ Y} {U' : C' ⥤ X'} {V' : E' ⥤ Y'}
variable (i : U ⋙ ID ≅ I ⋙ U') (j : V ⋙ JD ≅ J ⋙ V')
variable (r : V ⋙ R ≅ G ⋙ U) (r' : V' ⋙ R' ≅ G' ⋙ U')
variable (e : AdjunctionComparison ad ad' I J) (sigma : R ⋙ ID ≅ JD ⋙ R')

private theorem leftMate_at_rep (P : C)
    (c : L.obj (U.obj P) ≅ V.obj (F.obj P))
    (c' : L'.obj (U'.obj (I.obj P)) ≅ V'.obj (F'.obj (I.obj P)))
    (h : adD.unit.app (U.obj P) ≫ R.map c.hom ≫ r.hom.app (F.obj P) = U.map (ad.unit.app P))
    (h' : adD'.unit.app (U'.obj (I.obj P)) ≫ R'.map c'.hom ≫ r'.hom.app (F'.obj (I.obj P)) =
      U'.map (ad'.unit.app (I.obj P)))
    (hσ : ∀ N : E, sigma.hom.app (V.obj N) ≫ R'.map (j.hom.app N) ≫ r'.hom.app (J.obj N) =
      ID.map (r.hom.app N) ≫ i.hom.app (G.obj N) ≫ U'.map (e.hom.hom.app N)) :
    ((mateEquiv adD adD').symm sigma.hom).app (U.obj P) ≫
        JD.map c.hom ≫ j.hom.app (F.obj P) ≫ V'.map (e.tensor.hom.app P) =
      L'.map (i.hom.app P) ≫ c'.hom := by
  apply (adD'.homEquiv (ID.obj (U.obj P)) (V'.obj (F'.obj (I.obj P)))).injective
  apply (cancel_mono (r'.hom.app (F'.obj (I.obj P)))).mp
  have hm := unit_mateEquiv_symm adD adD' sigma.hom (U.obj P)
  change ID.map (adD.unit.app (U.obj P)) ≫ sigma.hom.app (L.obj (U.obj P)) =
    adD'.unit.app (ID.obj (U.obj P)) ≫
      R'.map (((mateEquiv adD adD').symm sigma.hom).app (U.obj P)) at hm
  have hσc := sigma.hom.naturality c.hom
  change ID.map (R.map c.hom) ≫ sigma.hom.app (V.obj (F.obj P)) =
    sigma.hom.app (L.obj (U.obj P)) ≫ R'.map (JD.map c.hom) at hσc
  have hr := r'.hom.naturality (e.tensor.hom.app P)
  change R'.map (V'.map (e.tensor.hom.app P)) ≫ r'.hom.app (F'.obj (I.obj P)) =
    r'.hom.app (J.obj (F.obj P)) ≫ U'.map (G'.map (e.tensor.hom.app P)) at hr
  have hi := i.hom.naturality (ad.unit.app P)
  change ID.map (U.map (ad.unit.app P)) ≫ i.hom.app (G.obj (F.obj P)) =
    i.hom.app P ≫ U'.map (I.map (ad.unit.app P)) at hi
  have hu := adD'.unit.naturality (i.hom.app P)
  change i.hom.app P ≫ adD'.unit.app (U'.obj (I.obj P)) =
    adD'.unit.app (ID.obj (U.obj P)) ≫ R'.map (L'.map (i.hom.app P)) at hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (adD'.unit.app (ID.obj (U.obj P))), ← hm]
  simp only [Category.assoc]
  rw [← Category.assoc (sigma.hom.app (L.obj (U.obj P))), ← hσc]
  simp only [Category.assoc]
  rw [hr, ← Category.assoc (R'.map (j.hom.app (F.obj P))), ← Category.assoc
    (sigma.hom.app (V.obj (F.obj P))), hσ]
  simp only [Category.assoc]
  rw [← ID.map_comp_assoc, ← ID.map_comp_assoc, Category.assoc, h, reassoc_of% hi]
  simp only [← U'.map_comp]
  rw [e.unit]
  rw [← Category.assoc (adD'.unit.app (ID.obj (U.obj P))), ← hu, Category.assoc, h']

private theorem resolutionUnitAt
    {C E X Y : Type*} [Category* C] [Category* E] [Category* X] [Category* Y]
    {Q : C ⥤ X} {Q' : E ⥤ Y} {Jres : X ⥤ C} (res : Jres ⊣ Q)
    {F : C ⥤ E} {H : E ⥤ C} (adj : F ⊣ H)
    {HD : Y ⥤ X} (b : Q' ⋙ HD ≅ H ⋙ Q)
    (adjD : (Jres ⋙ F) ⋙ Q' ⊣ HD)
    (h : ∀ X, adjD.unit.app X =
      res.unit.app X ≫ Q.map (adj.unit.app (Jres.obj X)) ≫ b.inv.app (F.obj (Jres.obj X)))
    (P : C) :
    adjD.unit.app (Q.obj P) ≫ HD.map (Q'.map (F.map (res.counit.app P))) ≫
      b.hom.app (F.obj P) = Q.map (adj.unit.app P) := by
  have hb := b.hom.naturality (F.map (res.counit.app P))
  change HD.map (Q'.map (F.map (res.counit.app P))) ≫ b.hom.app (F.obj P) =
    b.hom.app (F.obj (Jres.obj (Q.obj P))) ≫ Q.map (H.map (F.map (res.counit.app P))) at hb
  have hn := adj.unit.naturality (res.counit.app P)
  change res.counit.app P ≫ adj.unit.app P =
    adj.unit.app (Jres.obj (Q.obj P)) ≫ H.map (F.map (res.counit.app P)) at hn
  rw [h, Category.assoc, Category.assoc, hb, Iso.inv_hom_id_app_assoc,
    ← Q.map_comp, ← hn, Q.map_comp, ← Category.assoc, res.right_triangle_components]
  exact Category.id_comp _

end DerivedMates

section IsoAlgebra

variable {C : Type*} [Category* C] {X Y Z : C}

private theorem completeIsoSquare (lhs : X ≅ Z) (rhs : Y ≅ Z) {f : X ⟶ Y}
    (h : f = (lhs ≪≫ rhs.symm).hom) : f ≫ rhs.hom = lhs.hom := by
  rw [h]
  change (lhs.hom ≫ rhs.inv) ≫ rhs.hom = _
  rw [Category.assoc, rhs.inv_hom_id, Category.comp_id]

private theorem isIsoOfIsoSquare (lhs : X ≅ Z) (rhs : Y ≅ Z) {f : X ⟶ Y}
    (h : f ≫ rhs.hom = lhs.hom) : IsIso f := by
  have h' : f = (lhs ≪≫ rhs.symm).hom := by
    apply (cancel_mono rhs.hom).mp
    exact h.trans (completeIsoSquare lhs rhs rfl).symm
  rw [h']
  infer_instance

private theorem isIsoAtIso {C' : Type*} [Category* C'] {F G : C ⥤ C'}
    (f : F ⟶ G) (p : X ≅ Y) (h : IsIso (f.app X)) : IsIso (f.app Y) := by
  let lhs := (asIso (f.app X)) ≪≫ G.mapIso p
  let rhs := F.mapIso p
  have e : f.app Y = (rhs.symm ≪≫ lhs).hom := by
    apply (cancel_epi rhs.hom).mp
    rw [show rhs.hom ≫ (rhs.symm ≪≫ lhs).hom = lhs.hom by
      exact rhs.hom_inv_id_assoc _]
    exact f.naturality p.hom
  rw [e]
  infer_instance

private theorem inverseSquare (a : Y ≅ X) {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : a.hom ≫ f = g) : a.inv ≫ g = f := by
  rw [← h, a.inv_hom_id_assoc]

private theorem replacementSquare
    {D C' D' : Type*} [Category* D] [Category* C'] [Category* D']
    {I : C ⥤ C'} {J : D ⥤ D'} {L : C ⥤ D} {L' : C' ⥤ D'}
    (tau : L ⋙ J ≅ I ⋙ L') (p : X ≅ Y) {X' Y' : C'} (p' : X' ≅ Y')
    (iX : I.obj X ≅ X') (iY : I.obj Y ≅ Y')
    (h : I.map p.hom ≫ iY.hom = iX.hom ≫ p'.hom)
    {P : D} {P' : D'} (c : L.obj X ≅ P) (c' : L'.obj X' ≅ P') (z : J.obj P ⟶ P')
    (hX : tau.hom.app X ≫ L'.map iX.hom ≫ c'.hom = J.map c.hom ≫ z) :
    tau.hom.app Y ≫ L'.map iY.hom ≫ L'.map p'.inv ≫ c'.hom =
      J.map (L.map p.inv ≫ c.hom) ≫ z := by
  have hi : iY.hom ≫ p'.inv = I.map p.inv ≫ iX.hom := by
    apply (cancel_epi (I.map p.hom)).mp
    rw [← Category.assoc, h, Category.assoc, p'.hom_inv_id, Category.comp_id,
      ← I.map_comp_assoc, p.hom_inv_id, I.map_id, Category.id_comp]
  have ht := tau.hom.naturality p.inv
  change J.map (L.map p.inv) ≫ tau.hom.app X =
    tau.hom.app Y ≫ L'.map (I.map p.inv) at ht
  rw [← L'.map_comp_assoc, hi, L'.map_comp, Category.assoc,
    ← Category.assoc (tau.hom.app Y), ← ht]
  simp only [Category.assoc, hX, J.map_comp]

end IsoAlgebra

section Representatives

set_option allowUnsafeReducibility true in
attribute [local reducible] Derived.derivedCategory Derived.quotient

open Derived (HomotopyCategoryLaws homotopyCategory derivedCategory quotient quasiIsomorphisms)
open DerivedKProjective (derivedCategoryInstance)
open DerivedCoefficientLift (Descent)

local notation "K" => HomComplex.homotopyCategory
local instance {A : DGCategoryModel.{u,v,w} k} : Category (K A) :=
  RightDGModule.instCategoryK A

local instance {A : DGCategoryModel.{u,v,w} k} (h : HomotopyCategoryLaws A) :
    Category (derivedCategory A h) := derivedCategoryInstance A h

private theorem commute_heq {C : Type*} [Category* C] {X X' Y Y' : C}
    (eX : X = X') (eY : Y = Y') {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) :
    f ≫ eqToHom eY = eqToHom eX ≫ g := by
  cases eX
  cases eY
  obtain rfl := eq_of_heq h
  simp

variable {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,s,z} k}
variable (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B)

private abbrev toDerived (h : HomotopyCategoryLaws A) :
    RightDGModuleModel A ⥤ derivedCategory A h :=
  RightDGModule.toHomotopyCategory A ⋙ quotient A h

private def onClasses (F : RightDGModuleModel A ⥤ RightDGModuleModel B)
    (FK : K A ⥤ K B) (obj : ∀ M : RightDGModuleModel A, FK.obj M = F.obj M)
    (map : ∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
      HEq (FK.map (HomComplex.homotopyClass f)) (HomComplex.homotopyClass (F.map f))) :
    RightDGModule.toHomotopyCategory A ⋙ FK ≅ F ⋙ RightDGModule.toHomotopyCategory B :=
  NatIso.ofComponents (fun M => eqToIso (obj M)) (fun f => commute_heq (obj _) (obj _) (map f))

private def representedSquare (F : RightDGModuleModel A ⥤ RightDGModuleModel B)
    (FK : K A ⥤ K B) (FD : derivedCategory A hA ⥤ derivedCategory B hB)
    (obj : ∀ M : RightDGModuleModel A, FK.obj M = F.obj M)
    (map : ∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
      HEq (FK.map (HomComplex.homotopyClass f)) (HomComplex.homotopyClass (F.map f)))
    (square : quotient A hA ⋙ FD ≅ FK ⋙ quotient B hB) :
    toDerived hA ⋙ FD ≅ F ⋙ toDerived hB :=
  isoWhiskerLeft (RightDGModule.toHomotopyCategory A) square ≪≫
    isoWhiskerRight (onClasses F FK obj (fun f => map f)) (quotient B hB)

private theorem representedSquare_app (F : RightDGModuleModel A ⥤ RightDGModuleModel B)
    (FK : K A ⥤ K B) (FD : derivedCategory A hA ⥤ derivedCategory B hB)
    (obj : ∀ M : RightDGModuleModel A, FK.obj M = F.obj M)
    (map : ∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
      HEq (FK.map (HomComplex.homotopyClass f)) (HomComplex.homotopyClass (F.map f)))
    (square : quotient A hA ⋙ FD ≅ FK ⋙ quotient B hB) (M : RightDGModuleModel A) :
    (representedSquare hA hB F FK FD obj (fun f => map f) square).hom.app M =
      square.hom.app M ≫ eqToHom (congrArg (quotient B hB).obj (obj M)) := by
  change square.hom.app M ≫ (quotient B hB).map (eqToHom (obj M)) = _
  rw [eqToHom_map]
  rfl

private theorem liftIsoOnRepresentatives
    {E : Type*} [Category* E] {F G : derivedCategory A hA ⥤ E}
    (alpha : toDerived hA ⋙ F ≅ toDerived hA ⋙ G) :
    ∃ beta : F ≅ G, ∀ M : RightDGModuleModel A,
      beta.hom.app ((quotient A hA).obj M) = alpha.hom.app M := by
  let L := quotient A hA
  let W := quasiIsomorphisms A
  have : L.IsLocalization W := inferInstanceAs ((MorphismProperty.Q W).IsLocalization W)
  let alphaK : L ⋙ F ≅ L ⋙ G :=
    NatIso.ofComponents (fun M => alpha.app M) (by
      intro M N f
      obtain ⟨g, rfl⟩ := RightDGModule.homotopyClass_surjective f
      exact alpha.hom.naturality g)
  let P := (Functor.whiskeringLeft _ _ E).obj L
  let ff : P.FullyFaithful := Localization.fullyFaithfulWhiskeringLeft L W E
  let beta := ff.preimageIso alphaK
  refine ⟨beta, fun M => ?_⟩
  have h : P.map beta.hom = alphaK.hom := ff.map_preimage _
  exact congrArg (fun f : L ⋙ F ⟶ L ⋙ G => f.app M) h

open DerivedKProjective (kProjectiveObjects restrictedLocalization replacementIso)
open KProjective (isKProjective)
open HomComplex (homotopyClass)

section SignedRepresentatives

variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {T : bimodule A B} {m : SignedModels.{u,v,w,z} T}
variable {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
variable (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB)

private theorem onProjectiveUnit (h : d.Realizes m.adjunction)
    (P : RightDGModuleModel A) (hP : isKProjective P) :
    d.adjunction.unit.app ((toDerived hA).obj P) ≫
      d.hom.derived.map (d.onProjective P hP).hom ≫
      (d.onInput ((ordinaryTensor.{u,v,w,z} m.tensor).obj P)).hom =
    (toDerived hA).map (m.adjunction.unit.app P) := by
  rcases h with ⟨_, _, hK, _, hD, _, hc⟩
  let QA := quotient A hA
  let QB := quotient B hB
  let FP := (ordinaryTensor.{u,v,w,z} m.tensor).obj P
  let eta := d.adjunction.unit.app (QA.obj P)
  let eps := QB.map (d.tensorH.map (d.resolutionAdjunction.counit.app P))
  let f : d.tensorH.obj P ⟶ FP := eqToHom (d.tensorObj P)
  let g := eqToHom (d.hom.obj FP)
  have hb := d.hom.square.hom.naturality f
  change d.hom.derived.map (QB.map f) ≫ d.hom.square.hom.app FP =
    d.hom.square.hom.app (d.tensorH.obj P) ≫ QA.map (d.hom.homotopy.map f) at hb
  have hf := eqToHom_map QB (d.tensorObj P)
  have hg := eqToHom_map QA (d.hom.obj FP)
  have hgK : d.hom.homotopy.map f ≫ g =
      eqToHom ((congrArg d.hom.homotopy.obj (d.tensorObj P)).trans (d.hom.obj FP)) := by
    dsimp only [f, g]
    rw [eqToHom_map, eqToHom_trans]
  have hclass := commute_heq rfl
    ((congrArg d.hom.homotopy.obj (d.tensorObj P)).trans (d.hom.obj FP)) (hK P)
  have hclass' : d.homotopyAdjunction.unit.app P ≫ (d.hom.homotopy.map f ≫ g) =
      homotopyClass (m.adjunction.unit.app P) := by
    rw [hgK]
    exact hclass.trans (Category.id_comp _)
  change eta ≫ d.hom.derived.map (d.tensorSquare.hom.app ⟨P, hP⟩ ≫
      eqToHom (congrArg QB.obj (d.tensorObj P))) ≫
      d.hom.square.hom.app FP ≫ eqToHom (congrArg QA.obj (d.hom.obj FP)) = _
  erw [hc P hP, ← hf, ← hg]
  change eta ≫ d.hom.derived.map (eps ≫ QB.map f) ≫
      d.hom.square.hom.app FP ≫ QA.map g = QA.map (homotopyClass (m.adjunction.unit.app P))
  erw [d.hom.derived.map_comp_assoc, reassoc_of% hb]
  have hres := resolutionUnitAt d.resolutionAdjunction d.homotopyAdjunction d.hom.square
    d.adjunction hD P
  change eta ≫ d.hom.derived.map eps ≫ d.hom.square.hom.app (d.tensorH.obj P) = _ at hres
  erw [Category.assoc (d.hom.square.hom.app (d.tensorH.obj P)), reassoc_of% hres,
    ← QA.map_comp_assoc, ← QA.map_comp, Category.assoc, hclass']

end SignedRepresentatives

section DescentTheorem

variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {A' : DGCategoryModel.{u,max s w z,w} k} {B' : DGCategoryModel.{u,max s w z,z} k}
variable {T : bimodule A B} {T' : bimodule A' B'}
variable {m : SignedModels.{u,v,w,z} T} {m' : SignedModels.{u,s,w,z} T'}
variable {I : RightDGModuleModel A ⥤ RightDGModuleModel A'}
variable {J : RightDGModuleModel B ⥤ RightDGModuleModel B'}
variable {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
variable {hA' : HomotopyCategoryLaws A'} {hB' : HomotopyCategoryLaws B'}

private def transitionRepSquare {C : DGCategoryModel.{u,v,w} k}
    {C' : DGCategoryModel.{u,s,w} k}
    {h : HomotopyCategoryLaws C} {h' : HomotopyCategoryLaws C'}
    {F : RightDGModuleModel C ⥤ RightDGModuleModel C'} (d : Descent h h' F) :
    toDerived h ⋙ d.D ≅ F ⋙ toDerived h' :=
  NatIso.ofComponents (fun M => d.representedIso M) (by
    intro M N f
    let e := representedSquare h h' F d.H d.D d.obj (fun g => d.map g) d.square
    have hM := representedSquare_app h h' F d.H d.D d.obj (fun g => d.map g) d.square M
    have hN := representedSquare_app h h' F d.H d.D d.obj (fun g => d.map g) d.square N
    change e.hom.app M = (d.representedIso M).hom at hM
    change e.hom.app N = (d.representedIso N).hom at hN
    rw [← hM, ← hN]
    exact e.hom.naturality f)

private def homRepSquare (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB) :
    toDerived hB ⋙ d.hom.derived ≅ ordinaryHom.{u,v,w,z} m.hom ⋙ toDerived hA :=
  NatIso.ofComponents (fun N => d.onInput N) (by
    intro N N' f
    let e := representedSquare hB hA _ d.hom.homotopy d.hom.derived
      d.hom.obj (fun g => d.hom.map g) d.hom.square
    have hN := representedSquare_app hB hA _ d.hom.homotopy d.hom.derived
      d.hom.obj (fun g => d.hom.map g) d.hom.square N
    have hN' := representedSquare_app hB hA _ d.hom.homotopy d.hom.derived
      d.hom.obj (fun g => d.hom.map g) d.hom.square N'
    change e.hom.app N = (d.onInput N).hom at hN
    change e.hom.app N' = (d.onInput N').hom at hN'
    rw [← hN, ← hN']
    exact e.hom.naturality f)

theorem derivedComparison : DerivedComparison.{u,v,w,z,s} := by
  intro k _ A B A' B' T T' m m' I J hA hB hA' hB' dI dJ d d' e hI _hJ hIP hd hd'
  let U := toDerived hA
  let V := toDerived hB
  let U' := toDerived hA'
  let V' := toDerived hB'
  let i := transitionRepSquare dI
  let j := transitionRepSquare dJ
  let r := homRepSquare d
  let r' := homRepSquare d'
  let lhs := isoWhiskerRight r dI.D ≪≫
    isoWhiskerLeft (ordinaryHom.{u,v,w,z} m.hom) i ≪≫ isoWhiskerRight e.hom U'
  let rhs := isoWhiskerRight j d'.hom.derived ≪≫ isoWhiskerLeft J r'
  let comparison := lhs ≪≫ rhs.symm
  let alpha : V ⋙ (d.hom.derived ⋙ dI.D) ≅ V ⋙ (dJ.D ⋙ d'.hom.derived) :=
    NatIso.ofComponents comparison.app (fun f => comparison.hom.naturality f)
  obtain ⟨sigma, hsigma⟩ := liftIsoOnRepresentatives hB alpha
  have hσ (N : RightDGModuleModel B) :
      sigma.hom.app (V.obj N) ≫ d'.hom.derived.map (j.hom.app N) ≫ r'.hom.app (J.obj N) =
        dI.D.map (r.hom.app N) ≫ i.hom.app ((ordinaryHom.{u,v,w,z} m.hom).obj N) ≫
          U'.map (e.hom.hom.app N) :=
    completeIsoSquare (lhs.app N) (rhs.app N) (hsigma N)
  let nu := leftMate d.adjunction d'.adjunction sigma
  have hnu (P : RightDGModuleModel A) (hP : isKProjective P) :
      nu.app (U.obj P) ≫ dJ.D.map (d.onProjective P hP).hom ≫
        j.hom.app ((ordinaryTensor.{u,v,w,z} m.tensor).obj P) ≫ V'.map (e.tensor.hom.app P) =
          d'.tensor.map (i.hom.app P) ≫ (d'.onProjective (I.obj P) (hIP P hP)).hom :=
    leftMate_at_rep i j r r' e sigma P (d.onProjective P hP)
      (d'.onProjective (I.obj P) (hIP P hP))
      (onProjectiveUnit d hd P hP) (onProjectiveUnit d' hd' (I.obj P) (hIP P hP)) hσ
  have hIso (P : RightDGModuleModel A) (hP : isKProjective P) :
      IsIso (nu.app (U.obj P)) := by
    let a := dJ.D.mapIso (d.onProjective P hP) ≪≫
      j.app ((ordinaryTensor.{u,v,w,z} m.tensor).obj P) ≪≫ V'.mapIso (e.tensor.app P)
    let b := d'.tensor.mapIso (i.app P) ≪≫ d'.onProjective (I.obj P) (hIP P hP)
    exact isIsoOfIsoSquare b a (hnu P hP)
  let : IsIso nu := (NatTrans.isIso_iff_isIso_app nu).mpr (by
    intro X
    let q := restrictedLocalization A hA
    have hq : q.IsEquivalence :=
      RightDGModule.kProjectiveLocalization_isEquivalence.{u,max v z,w} A hA
    let P := q.objPreimage X
    exact isIsoAtIso nu (q.objObjPreimageIso X) (hIso P.obj P.property))
  let ed := comparisonOfRightMate d.adjunction d'.adjunction sigma
  refine ⟨ed, ?_, ?_⟩
  · exact hσ
  · intro P M p hP hp
    have hp' := hI p hp
    let p₀ := replacementIso hA p hp
    let p₁ := replacementIso hA' (I.map p) hp'
    let c := d.onProjective P hP
    let c' := d'.onProjective (I.obj P) (hIP P hP)
    have hτ : ed.tensor.hom.app (U.obj P) ≫ d'.tensor.map (i.hom.app P) ≫ c'.hom =
        dJ.D.map c.hom ≫ j.hom.app ((ordinaryTensor.{u,v,w,z} m.tensor).obj P) ≫
          V'.map (e.tensor.hom.app P) :=
      inverseSquare (ed.tensor.app (U.obj P)).symm (hnu P hP)
    exact replacementSquare ed.tensor p₀ p₁ (i.app P) (i.app M)
      (i.hom.naturality p) c c'
      (j.hom.app ((ordinaryTensor.{u,v,w,z} m.tensor).obj P) ≫ V'.map (e.tensor.hom.app P)) hτ

end DescentTheorem

end Representatives

end

end DerivedFormalization.DG.BimoduleCoefficientCompatibility
