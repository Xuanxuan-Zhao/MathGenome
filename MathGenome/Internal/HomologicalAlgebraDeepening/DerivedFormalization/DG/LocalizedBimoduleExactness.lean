import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedTriangles
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.LocalizedBimoduleExactness
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w z vA

namespace DerivedFormalization.DGBimodule

open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.LocalizedBimoduleExactness
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)
open Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance)
open Specs.DerivedFormalization.DG.BalancedTensor (bimodule tmul)
open Specs.DerivedFormalization.DG.BimoduleAdjunction
  (TensorModel InternalHomModel OrdinaryCurryFamily StrictLaws ordinaryTensor ordinaryHom)
open Specs.DerivedFormalization.DG.KProjective (isKProjective)
open RightDGModule
  (homotopyPreadditive homotopyHasZeroObject homotopyHasShift homotopyShiftAdditive
    homotopyPretriangulated homotopyIsTriangulated strictHasShift toHomotopyCategoryCommShift)

open private homotopyQuotient strictShiftZero strictShiftAdd quotientCommShift_hom
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyShift
open private specConeTriangle_eq derived_distinguished_iff_projective_cone
  quasiIsomorphisms_hasLeftCalculusOfFractions quasiIsomorphisms_isStableUnderFiniteProducts
  quasiIsomorphisms_isCompatibleWithTriangulation
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedTriangles

open private quotientShift_map_heq from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyPretriangulated

local notation "K" => HomComplex.homotopyCategory
local notation "D" => Derived.derivedCategory
local notation "Q" => Derived.quotient
local notation "W" => Derived.quasiIsomorphisms

noncomputable section

variable {k : Type u} [CommRing k]

set_option maxHeartbeats 350000
set_option linter.style.haveILetI false

/-- The standard G04 and G08 shifts and triangulations. -/
private def coneLocalization (A : DGCategory.{u,max v w,w} k) (h : HomotopyCategoryLaws A) :
    ConeLocalization A h := by
  let L := (RightDGModule.quasiIsomorphisms A).Q
  letI : (RightDGModule.quasiIsomorphisms A).HasLeftCalculusOfFractions :=
    quasiIsomorphisms_hasLeftCalculusOfFractions
  letI : (RightDGModule.quasiIsomorphisms A).IsStableUnderFiniteProducts :=
    quasiIsomorphisms_isStableUnderFiniteProducts
  letI : (RightDGModule.quasiIsomorphisms A).IsCompatibleWithTriangulation :=
    quasiIsomorphisms_isCompatibleWithTriangulation
  have : L.mapArrow.EssSurj := Localization.essSurj_mapArrow L (RightDGModule.quasiIsomorphisms A)
  let SD : HasShift (RightDGModule.quasiIsomorphisms A).Localization ℤ := inferInstance
  let AD : Preadditive (RightDGModule.quasiIsomorphisms A).Localization := inferInstance
  let ZD : HasZeroObject (RightDGModule.quasiIsomorphisms A).Localization := inferInstance
  let LD (n : ℤ) : (shiftFunctor (RightDGModule.quasiIsomorphisms A).Localization n).Additive := inferInstance
  let I : L.CommShift ℤ := inferInstance
  let TD : Pretriangulated (RightDGModule.quasiIsomorphisms A).Localization := inferInstance
  have hT : IsTriangulated (RightDGModule.quasiIsomorphisms A).Localization := inferInstance
  have hL : L.IsTriangulated :=
    Triangulated.Localization.isTriangulated_functor L (RightDGModule.quasiIsomorphisms A)
  refine
    { shiftK := homotopyHasShift
      addK := homotopyPreadditive
      zeroK := homotopyHasZeroObject
      addShiftK := homotopyShiftAdditive
      shiftObj := fun _ _ => rfl
      shiftMap := ?_
      homGroup := fun _ _ => HEq.rfl
      trianglesK := homotopyPretriangulated
      isTriangulatedK := homotopyIsTriangulated
      shiftD := SD
      addD := AD
      zeroD := ZD
      addShiftD := LD
      quotientShift := I
      trianglesD := TD
      isTriangulated := hT
      quotientTriangulated := hL
      coneTriangles := ?_
      localizedConeTriangles := ?_ }
  · intro M N f n
    exact @quotientShift_map_heq k _ A M N n f
  · intro U
    simpa only [specConeTriangle_eq] using RightDGModule.distinguished_iff_cone_triangle U
  · constructor
    · intro M N f
      change L.mapTriangle.obj (DerivedTriangles.coneTriangle h homotopyHasShift rfl f) ∈
        distTriang (RightDGModule.quasiIsomorphisms A).Localization
      simpa only [specConeTriangle_eq] using L.map_distinguished _ (RightDGModule.coneTriangle_distinguished f)
    · intro U hU
      change Triangle (RightDGModule.quasiIsomorphisms A).Localization at U
      change ∃ (M N : RightDGModule A) (_ : RightDGModule.IsKProjective M) (_ : RightDGModule.IsKProjective N)
        (f : M ⟶ N), Nonempty (U ≅ L.mapTriangle.obj
          (DerivedTriangles.coneTriangle h homotopyHasShift rfl f))
      simpa only [specConeTriangle_eq] using (derived_distinguished_iff_projective_cone L U).mp hU


private theorem coneLocalization_onShift_hom
    {A : DGCategory.{u,max v w,w} k} (h : HomotopyCategoryLaws A) (M : RightDGModule A) (s : ℤ) :
    let c := coneLocalization.{u,v,w} A h
    letI : Category (D A h) := derivedCategoryInstance A h
    let QA : RightDGModule.K A ⥤ D A h := Q A h
    letI := c.shiftD
    letI : QA.CommShift ℤ := c.quotientShift
    (c.onShift M s).hom = (QA.commShiftIso s).hom.app (M : RightDGModule.K A) := by
  let c := coneLocalization.{u,v,w} A h
  letI : Category (D A h) := derivedCategoryInstance A h
  let QA : RightDGModule.K A ⥤ D A h := Q A h
  letI := c.shiftD
  letI : QA.CommShift ℤ := c.quotientShift
  change 𝟙 _ ≫ (QA.commShiftIso s).hom.app (M : RightDGModule.K A) =
    (QA.commShiftIso s).hom.app (M : RightDGModule.K A)
  exact Category.id_comp _

section Coordinates

open Specs.DerivedFormalization.DG.ShiftCone (shift shiftMap)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component dgModuleCategory ofStrict)
open CochainComplex.HomComplex

variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {T : bimodule A B} {L : TensorModel T} {G : InternalHomModel T}


private abbrev reindex (C : ModuleCochain.{u,vA} k) {i j : ℤ} (e : i = j) : C.X i ⟶ C.X j :=
  eqToHom (congrArg C.X e)

private theorem strictZero_f {C : DGCategoryModel.{u,vA,w} k}
    (M : RightDGModuleModel C) (a : C.Obj) (i : ℤ) :
    (((strictShiftZero (A := C)).hom.app M).app a).f i =
      reindex (M.complex a) (add_zero i) := rfl

private theorem strictAdd_f {C : DGCategoryModel.{u,vA,w} k}
    (M : RightDGModuleModel C) (a : C.Obj) (s t i : ℤ) :
    (((strictShiftAdd (A := C) s t).hom.app M).app a).f i =
      reindex (M.complex a) (show i + (s + t) = i + t + s by omega) := rfl

private theorem tensor_reindex (M : RightDGModuleModel A) (a : A.Obj) (b : B.Obj)
    {i i' j n n' : ℤ} (e : i = i') (e' : n = n') (h : i+j=n) (h' : i'+j=n')
    (x : (M.complex a).X i) (y : ((T.obj a).complex b).X j) :
    reindex (((ordinaryTensor.{u,v,w,z} L).obj M).complex b) e' (L.degree M b n (tmul T M b a i j n h x y)) =
      L.degree M b n' (tmul T M b a i' j n' h' (reindex (M.complex a) e x) y) := by
  subst i' n'
  simp only [reindex, eqToHom_refl, ModuleCat.id_apply]

private theorem tensor_map_f {M N : RightDGModuleModel A} (f : M ⟶ N)
    (a : A.Obj) (b : B.Obj) (i j n : ℤ) (h : i+j=n)
    (x : (M.complex a).X i) (y : ((T.obj a).complex b).X j) :
    (((ordinaryTensor.{u,v,w,z} L).map f).app b).f n (L.degree M b n (tmul T M b a i j n h x y)) =
      L.degree N b n (tmul T N b a i j n h ((f.app a).f i x) y) :=
  L.map_tmul f a b i j n h x y

private theorem tensor_hom_ext {M : RightDGModuleModel A} {N : RightDGModuleModel B}
    {f g : (ordinaryTensor.{u,v,w,z} L).obj M ⟶ N}
    (h : ∀ (a : A.Obj) (b : B.Obj) (i j n : ℤ) (e : i+j=n)
      (x : (M.complex a).X i) (y : ((T.obj a).complex b).X j),
      (f.app b).f n (L.degree M b n (tmul T M b a i j n e x y)) =
      (g.app b).f n (L.degree M b n (tmul T M b a i j n e x y))) : f = g := by
  apply RightDGModuleModel.hom_ext
  intro b
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let f' := ((f.app b).f n).hom.comp (L.degree M b n).toLinearMap
  let g' := ((g.app b).f n).hom.comp (L.degree M b n).toLinearMap
  have he : f' = g' := DGBimodule.linearMap_ext T M (fun a i j e x y => h a b i j n e x y)
  obtain ⟨x, rfl⟩ := (L.degree M b n).surjective x
  exact LinearMap.congr_fun he x

private theorem tensorShiftZero (S : ShiftConeComparisons (ordinaryTensor.{u,v,w,z} L))
    (hS : TensorComparisonLaws.{u,v,w,z} S) (M : RightDGModuleModel A) :
    (S.shiftIso M 0).hom ≫ (strictShiftZero (A := B)).hom.app ((ordinaryTensor.{u,v,w,z} L).obj M) =
      (ordinaryTensor.{u,v,w,z} L).map ((strictShiftZero (A := A)).hom.app M) := by
  apply tensor_hom_ext
  intro a b i j n e x y
  simp only [RightDGModuleModel.comp_app, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    (tensor_map_f.{u,v,w,z} (L := L)), hS.1, strictZero_f, Functor.id_obj]
  exact tensor_reindex.{u,v,w,z} (L := L) M a b (add_zero i) (add_zero n) (by omega) e x y

private theorem tensorShiftAdd (S : ShiftConeComparisons (ordinaryTensor.{u,v,w,z} L))
    (hS : TensorComparisonLaws.{u,v,w,z} S) (M : RightDGModuleModel A) (s t : ℤ) :
    (S.shiftIso M (s+t)).hom ≫ (strictShiftAdd (A := B) s t).hom.app ((ordinaryTensor.{u,v,w,z} L).obj M) =
      (ordinaryTensor.{u,v,w,z} L).map ((strictShiftAdd (A := A) s t).hom.app M) ≫
        (S.shiftIso (shift M s) t).hom ≫ shiftMap t (S.shiftIso M s).hom := by
  apply tensor_hom_ext
  intro a b i j n e x y
  simp only [RightDGModuleModel.comp_app, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    (tensor_map_f.{u,v,w,z} (L := L)), hS.1, strictAdd_f]
  let x' : ((shift (shift M s) t).complex a).X i :=
    reindex (M.complex a) (show i+(s+t)=i+t+s by omega) x
  change _ = (((S.shiftIso M s).hom.app b).f (n+t))
    ((((S.shiftIso (shift M s) t).hom.app b).f n)
      (L.degree (shift (shift M s) t) b n (tmul T (shift (shift M s) t) b a i j n e x' y)))
  rw [hS.1 (shift M s) t a b i j n e x' y]
  change _ = (((S.shiftIso M s).hom.app b).f (n+t))
    (L.degree (shift M s) b (n+t) (tmul T (shift M s) b a (i+t) j (n+t) (by omega)
      (reindex (M.complex a) (show i + (s+t) = i+t+s by omega) x) y))
  rw [hS.1]
  exact tensor_reindex.{u,v,w,z} (L := L) M a b
    (show i+(s+t)=i+t+s by omega) (show n+(s+t)=n+t+s by omega) (by omega) (by omega) x y

private abbrev homDegreeIso (N : RightDGModuleModel B) (a : A.Obj) (r : ℤ) :=
  (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℤ) r).mapIso (G.objectwise N a)

private theorem hom_map_component {N N' : RightDGModuleModel B} (f : N ⟶ N')
    (a : A.Obj) (b : B.Obj) (r i j : ℤ) (h : i+r=j) (x : (((ordinaryHom.{u,v,w,z} G).obj N).complex a).X r)
    (y : ((T.obj a).complex b).X i) :
    component ((G.objectwise N' a).inv.f r ((((ordinaryHom.{u,v,w,z} G).map f).app a).f r x)) b i j h y =
      (f.app b).f j (component ((G.objectwise N a).inv.f r x) b i j h y) := by
  obtain ⟨g, hg⟩ := (homDegreeIso.{u,v,w,z} (G := G) N a r).toLinearEquiv.surjective x
  change (G.objectwise N a).hom.f r g = x at hg
  subst x
  have cancel {X : RightDGModuleModel B} (g' : gradedHom (T.obj a) X r) :
      (G.objectwise X a).inv.f r ((G.objectwise X a).hom.f r g') = g' := by
    exact (homDegreeIso.{u,v,w,z} (G := G) X a r).toLinearEquiv.symm_apply_apply g'
  rw [show (((ordinaryHom.{u,v,w,z} G).map f).app a).f r ((G.objectwise N a).hom.f r g) =
      (G.objectwise N' a).hom.f r ((dgModuleCategory B).comp 0 r r (zero_add r) (ofStrict f) g)
        from G.map f a r g, cancel, cancel]
  change ((g.val b).comp (Cochain.ofHom (f.app b)) (add_zero r)).v i j h y = _
  rw [Cochain.comp_v (g.val b) _ _ i j j h (add_zero j)]
  simp only [Cochain.ofHom_v, ModuleCat.comp_apply, component]

private theorem hom_reindex (N : RightDGModuleModel B) (a : A.Obj) (b : B.Obj)
    {r r' i j j' : ℤ} (e : r = r') (e' : j = j') (h : i+r=j) (h' : i+r'=j')
    (x : (((ordinaryHom.{u,v,w,z} G).obj N).complex a).X r) (y : ((T.obj a).complex b).X i) :
    component ((G.objectwise N a).inv.f r' (reindex (((ordinaryHom.{u,v,w,z} G).obj N).complex a) e x)) b i j' h' y =
      reindex (N.complex b) e'
        (component ((G.objectwise N a).inv.f r x) b i j h y) := by
  subst r' j'
  simp only [reindex, eqToHom_refl, ModuleCat.id_apply]

private theorem hom_inv_shift_component (R : ShiftConeComparisons (ordinaryHom.{u,v,w,z} G))
    (hR : HomComparisonLaws.{u,v,w,z} R) (N : RightDGModuleModel B) (s : ℤ) (a : A.Obj)
    (b : B.Obj) (r i j : ℤ) (h : i+r=j) (x : (((ordinaryHom.{u,v,w,z} G).obj N).complex a).X (r+s))
    (y : ((T.obj a).complex b).X i) :
    component ((G.objectwise (shift N s) a).inv.f r (((R.shiftIso N s).inv.app a).f r x)) b i j h y =
      component ((G.objectwise N a).inv.f (r+s) x) b i (j+s) (by omega) y := by
  obtain ⟨g, hg⟩ := (homDegreeIso.{u,v,w,z} (G := G) N a (r+s)).toLinearEquiv.surjective x
  change (G.objectwise N a).hom.f (r+s) g = x at hg
  subst x
  have cancel : (G.objectwise N a).inv.f (r+s) ((G.objectwise N a).hom.f (r+s) g) = g :=
    (homDegreeIso.{u,v,w,z} (G := G) N a (r+s)).toLinearEquiv.symm_apply_apply g
  rw [cancel]
  exact congrArg (fun f : ((T.obj a).complex b).X i ⟶ ((shift N s).complex b).X j => f y)
    (hR.1 N s a r g b i j h)

private theorem hom_hom_ext {M : RightDGModuleModel A} {N : RightDGModuleModel B}
    {f g : M ⟶ (ordinaryHom.{u,v,w,z} G).obj N}
    (h : ∀ (a : A.Obj) (b : B.Obj) (r i j : ℤ) (e : i+r=j)
      (x : (M.complex a).X r) (y : ((T.obj a).complex b).X i),
      component ((G.objectwise N a).inv.f r ((f.app a).f r x)) b i j e y =
      component ((G.objectwise N a).inv.f r ((g.app a).f r x)) b i j e y) : f = g := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (homDegreeIso.{u,v,w,z} (G := G) N a r).toLinearEquiv.symm.injective
  apply Subtype.ext
  funext b
  ext i j e : 1
  apply ModuleCat.hom_ext
  exact LinearMap.ext (h a b r i j e x)

private theorem homShiftZero_inv (R : ShiftConeComparisons (ordinaryHom.{u,v,w,z} G))
    (hR : HomComparisonLaws.{u,v,w,z} R) (N : RightDGModuleModel B) :
    (R.shiftIso N 0).inv ≫ (ordinaryHom.{u,v,w,z} G).map ((strictShiftZero (A := B)).hom.app N) =
      (strictShiftZero (A := A)).hom.app ((ordinaryHom.{u,v,w,z} G).obj N) := by
  apply hom_hom_ext
  intro a b r i j h x y
  simp only [RightDGModuleModel.comp_app, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    (hom_map_component.{u,v,w,z} (G := G)), hom_inv_shift_component R hR, strictZero_f, Functor.id_obj]
  exact (hom_reindex N a b (add_zero r) (add_zero j) (by omega) h x y).symm

private theorem homShiftAdd_inv (R : ShiftConeComparisons (ordinaryHom.{u,v,w,z} G))
    (hR : HomComparisonLaws.{u,v,w,z} R) (N : RightDGModuleModel B) (s t : ℤ) :
    (strictShiftAdd (A := A) s t).hom.app ((ordinaryHom.{u,v,w,z} G).obj N) ≫
        shiftMap t (R.shiftIso N s).inv ≫ (R.shiftIso (shift N s) t).inv =
      (R.shiftIso N (s+t)).inv ≫ (ordinaryHom.{u,v,w,z} G).map ((strictShiftAdd (A := B) s t).hom.app N) := by
  apply hom_hom_ext
  intro a b r i j h x y
  simp only [RightDGModuleModel.comp_app, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    (hom_map_component.{u,v,w,z} (G := G)), hom_inv_shift_component R hR, strictAdd_f]
  change component ((G.objectwise (shift N s) a).inv.f (r+t)
    (((R.shiftIso N s).inv.app a).f (r+t) _)) b i (j+t) (by omega) y = _
  rw [hom_inv_shift_component R hR]
  exact hom_reindex N a b (show r+(s+t)=r+t+s by omega) (show j+(s+t)=j+t+s by omega)
    (by omega) (by omega) x y

private theorem strictUnitShift_inv {E : OrdinaryCurryFamily.{u,v,w,z} L G}
    {adj : (ordinaryTensor.{u,v,w,z} L) ⊣ (ordinaryHom.{u,v,w,z} G)} (laws : StrictLaws.{u,v,w,z} L G E adj)
    (S : ShiftConeComparisons (ordinaryTensor.{u,v,w,z} L)) (hS : TensorComparisonLaws.{u,v,w,z} S)
    (R : ShiftConeComparisons (ordinaryHom.{u,v,w,z} G)) (hR : HomComparisonLaws.{u,v,w,z} R)
    (M : RightDGModuleModel A) (s : ℤ) :
    adj.unit.app (shift M s) ≫ (ordinaryHom.{u,v,w,z} G).map (S.shiftIso M s).hom =
      shiftMap s (adj.unit.app M) ≫ (R.shiftIso ((ordinaryTensor.{u,v,w,z} L).obj M) s).inv := by
  apply hom_hom_ext
  intro a b i j n h x y
  simp only [RightDGModuleModel.comp_app, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    (hom_map_component.{u,v,w,z} (G := G)), hom_inv_shift_component R hR]
  rw [laws.unit (shift M s) a b i j n (by omega)]
  change _ = component ((G.objectwise ((ordinaryTensor.{u,v,w,z} L).obj M) a).inv.f (i+s)
    (((adj.unit.app M).app a).f (i+s) x)) b j (n+s) (by omega) y
  rw [laws.unit M a b (i+s) j (n+s) (by omega), hS.1]

end Coordinates

section Adjunctions

private theorem composedAdjunctionCommShift
    {KA KB DA DB : Type*} [Category* KA] [Category* KB] [Category* DA] [Category* DB]
    [HasShift KA ℤ] [HasShift KB ℤ] [HasShift DA ℤ] [HasShift DB ℤ]
    {QA : KA ⥤ DA} {QB : KB ⥤ DB} {FK : KA ⥤ KB} {HK : KB ⥤ KA}
    {J : DA ⥤ KA} {HD : DB ⥤ DA} [QA.CommShift ℤ] [QB.CommShift ℤ]
    [FK.CommShift ℤ] [HK.CommShift ℤ] [J.CommShift ℤ] [HD.CommShift ℤ]
    (aJ : J ⊣ QA) (aK : FK ⊣ HK) (aD : (J ⋙ FK) ⋙ QB ⊣ HD)
    [aJ.CommShift ℤ] [aK.CommShift ℤ]
    (b : QB ⋙ HD ≅ HK ⋙ QA) [NatTrans.CommShift b.hom ℤ]
    (h : ∀ X, aD.unit.app X =
      aJ.unit.app X ≫ QA.map (aK.unit.app (J.obj X)) ≫ b.inv.app (FK.obj (J.obj X))) :
    aD.CommShift ℤ := by
  apply Adjunction.CommShift.mk'
  let φ : 𝟭 DA ⟶ ((J ⋙ FK) ⋙ QB) ⋙ HD :=
    (aJ.comp aK).unit ≫ Functor.whiskerLeft (J ⋙ FK) b.inv ≫
      (Functor.associator (J ⋙ FK) QB HD).inv
  have he : aD.unit = φ := by
    ext X
    simpa [φ, Adjunction.comp, Category.assoc] using h X
  rw [he]
  dsimp only [φ]
  infer_instance

private def resolutionCounitComparison
    {C C' E E' : Type*} [Category* C] [Category* C'] [Category* E] [Category* E']
    {J : C' ⥤ C} {q : C ⥤ C'} (aJ : J ⊣ q) (f : C ⥤ E) (r : E ⥤ E') :
    q ⋙ ((J ⋙ f) ⋙ r) ⟶ f ⋙ r :=
  (Functor.associator q (J ⋙ f) r).inv ≫
    Functor.whiskerRight (Functor.associator q J f).inv r ≫
    Functor.whiskerRight (Functor.whiskerRight aJ.counit f) r ≫
    Functor.whiskerRight f.leftUnitor.hom r

private theorem resolutionCounitComparison_app
    {C C' E E' : Type*} [Category* C] [Category* C'] [Category* E] [Category* E']
    {J : C' ⥤ C} {q : C ⥤ C'} (aJ : J ⊣ q) (f : C ⥤ E) (r : E ⥤ E') (X : C) :
    (resolutionCounitComparison aJ f r).app X = r.map (f.map (aJ.counit.app X)) := by
  simp [resolutionCounitComparison]

private theorem resolutionCounitComparison_commShift
    {C C' E E' : Type*} [Category* C] [Category* C'] [Category* E] [Category* E']
    [HasShift C ℤ] [HasShift C' ℤ] [HasShift E ℤ] [HasShift E' ℤ]
    {J : C' ⥤ C} {q : C ⥤ C'} [J.CommShift ℤ] [q.CommShift ℤ]
    (aJ : J ⊣ q) [aJ.CommShift ℤ] (f : C ⥤ E) [f.CommShift ℤ] (r : E ⥤ E') [r.CommShift ℤ] :
    NatTrans.CommShift (resolutionCounitComparison aJ f r) ℤ := by
  unfold resolutionCounitComparison
  infer_instance

private theorem isIso_counit_of_map
    {C D₀ : Type*} [Category* C] [Category* D₀]
    {L : D₀ ⥤ C} {R : C ⥤ D₀} (a : L ⊣ R) (P : C)
    (surj : Function.Surjective (R.map : (P ⟶ L.obj (R.obj P)) → _))
    (inj : Function.Injective (R.map : (P ⟶ P) → _)) : IsIso (a.counit.app P) := by
  let X := R.obj P
  obtain ⟨i, hi⟩ := surj (a.unit.app X)
  have htri := a.right_triangle_components P
  have hleft : i ≫ a.counit.app P = 𝟙 P := by
    apply inj
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, hi]
    exact htri
  have hright : a.counit.app P ≫ i = 𝟙 (L.obj X) := by
    apply (a.homEquiv X (L.obj X)).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, CategoryTheory.Functor.map_id]
    rw [← Category.assoc, htri, Category.id_comp, hi]
    exact (Category.comp_id _).symm
  exact ⟨i, hright, hleft⟩

private theorem isIso_resolutionCounit
    {A : DGCategoryModel.{u,v,w} k} (hA : HomotopyCategoryLaws A)
    (J : @Functor (D A hA) (derivedCategoryInstance A hA) (K A) (Derived.homotopyCategory A hA))
    (aJ : letI := Derived.homotopyCategory A hA; letI := derivedCategoryInstance A hA;
      J ⊣ Q A hA)
    (P : RightDGModuleModel A)
    (hp : isKProjective P) :
    letI := Derived.homotopyCategory A hA
    letI := derivedCategoryInstance A hA
    IsIso (aJ.counit.app (P : K A)) := by
  letI := Derived.homotopyCategory A hA
  letI := derivedCategoryInstance A hA
  let QA : K A ⥤ D A hA := Q A hA
  exact isIso_counit_of_map aJ (P : K A)
    (RightDGModule.IsKProjective.Q_map_bijective hA (N := J.obj (QA.obj P)) hp).2
    (RightDGModule.IsKProjective.Q_map_bijective hA (N := P) hp).1

end Adjunctions

local instance (A : DGCategory.{u,v,w} k) : Category (K A) :=
  RightDGModule.instCategoryK A

local instance (A : DGCategory.{u,v,w} k) : HasShift (K A) ℤ :=
  homotopyHasShift (A := A)

section QuotientShifts

open CategoryTheory.Functor

variable {C C' E : Type*} [Category* C] [Category* C'] [Category* E]
variable [HasShift C ℤ] [HasShift C' ℤ] [HasShift E ℤ]
variable (q : C ⥤ C') [q.CommShift ℤ] {f : C ⥤ E} [f.CommShift ℤ] {g : C' ⥤ E}
variable (e : q ⋙ g ≅ f)
variable [((whiskeringLeft C C' E).obj q).Full] [((whiskeringLeft C C' E).obj q).Faithful]

/-- Precomposition by the strict quotient determines the shift isomorphism. -/
private def quotientShift (s : ℤ) : shiftFunctor C' s ⋙ g ≅ g ⋙ shiftFunctor E s :=
  ((whiskeringLeft C C' E).obj q).preimageIso
    ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (q.commShiftIso s).symm g ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e ≪≫ f.commShiftIso s ≪≫
      isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _)

private theorem quotientShift_hom_app (s : ℤ) (X : C) :
    (quotientShift q e s).hom.app (q.obj X) =
      g.map ((q.commShiftIso s).inv.app X) ≫ e.hom.app (X⟦s⟧) ≫ (f.commShiftIso s).hom.app X ≫
        (shiftFunctor E s).map (e.inv.app X) := by
  let a := ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (q.commShiftIso s).symm g ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e ≪≫ f.commShiftIso s ≪≫
      isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _)
  have h := ((whiskeringLeft C C' E).obj q).map_preimage a.hom
  have hX : (quotientShift q e s).hom.app (q.obj X) = a.hom.app X :=
    congrArg (fun i => i.app X) h
  rw [hX]
  simp [a]

omit [HasShift C ℤ] [HasShift C' ℤ] [HasShift E ℤ] [q.CommShift ℤ]
  [((whiskeringLeft C C' E).obj q).Full] [((whiskeringLeft C C' E).obj q).Faithful] in
private theorem quotientNatTrans_ext (hq : Function.Surjective q.obj) {G H : C' ⥤ E}
    {a b : G ⟶ H} (h : ∀ X, a.app (q.obj X) = b.app (q.obj X)) : a = b := by
  ext Y
  obtain ⟨X, rfl⟩ := hq Y
  exact h X

/-- The localization argument for coherent shifts also applies to a quotient
whose precomposition is fully faithful on natural transformations. -/
@[instance_reducible] private def quotientCommShift (hq : Function.Surjective q.obj) : g.CommShift ℤ where
  commShiftIso := quotientShift q e
  commShiftIso_zero := by
    ext1
    apply quotientNatTrans_ext q hq
    intro X
    dsimp
    simp only [quotientShift_hom_app, comp_obj, commShiftIso_zero,
      CommShift.isoZero_inv_app, map_comp, CommShift.isoZero_hom_app, Category.assoc,
      ← NatTrans.naturality_assoc, ← NatTrans.naturality]
    dsimp
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, id_obj, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app_assoc]
  commShiftIso_add a b := by
    ext1
    apply quotientNatTrans_ext q hq
    intro X
    dsimp
    simp only [quotientShift_hom_app, comp_obj, commShiftIso_add,
      CommShift.isoAdd_inv_app, map_comp, CommShift.isoAdd_hom_app, Category.assoc]
    congr 1
    rw [← cancel_epi (g.map ((shiftFunctor C' b).map ((q.commShiftIso a).hom.app X))),
      ← g.map_comp_assoc, ← map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    conv_lhs =>
      erw [← NatTrans.naturality_assoc]
      dsimp
      rw [← Functor.map_comp_assoc, ← map_comp_assoc, Category.assoc,
        ← map_comp, Iso.inv_hom_id_app]
      dsimp
      rw [CategoryTheory.Functor.map_id, Category.comp_id, ← NatTrans.naturality]
      dsimp
    conv_rhs =>
      erw [← NatTrans.naturality_assoc]
      dsimp
      rw [← Functor.map_comp_assoc, ← map_comp, Iso.hom_inv_id_app]
      dsimp
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
        quotientShift_hom_app, Category.assoc, Category.assoc, Category.assoc, ← map_comp_assoc,
        Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem quotientIso_commShift (hq : Function.Surjective q.obj) :
    letI := quotientCommShift q e hq
    NatTrans.CommShift e.hom ℤ := by
  letI := quotientCommShift q e hq
  constructor
  intro s
  ext X
  change (Functor.commShiftIso (q ⋙ g) s).hom.app X ≫
      (shiftFunctor E s).map (e.hom.app X) =
    e.hom.app (X⟦s⟧) ≫ (f.commShiftIso s).hom.app X
  rw [Functor.commShiftIso_comp_hom_app]
  change (g.map ((q.commShiftIso s).hom.app X) ≫ (quotientShift q e s).hom.app (q.obj X)) ≫
      (shiftFunctor E s).map (e.hom.app X) = _
  simp only [quotientShift_hom_app, Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Iso.inv_hom_id_app, Category.id_comp]
  exact congrArg (fun m => e.hom.app (X⟦s⟧) ≫ m) (Category.comp_id ((f.commShiftIso s).hom.app X))

end QuotientShifts

local instance quotientCommShiftInstance {C : DGCategory.{u,v,w} k} :
    (homotopyQuotient C).CommShift ℤ := toHomotopyCategoryCommShift

local instance compStrictQuotientCommShift {C : Type*} [Category* C] [HasShift C ℤ]
    {B : DGCategory.{u,v,z} k} (F : C ⥤ RightDGModule B) [F.CommShift ℤ] :
    (F ⋙ homotopyQuotient B).CommShift ℤ := by
  letI : (homotopyQuotient B).CommShift ℤ := toHomotopyCategoryCommShift
  exact CategoryTheory.Functor.CommShift.comp (A := ℤ) F (homotopyQuotient B)

section Lifts

open Specs.DerivedFormalization.DG.ShiftCone (shift shiftMap)
open RightDGModule (homotopyShift)

variable {A : DGCategory.{u,vA,w} k} {B : DGCategory.{u,v,z} k}
variable {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
variable {F : RightDGModule A ⥤ RightDGModule B}

@[instance_reducible] private def strictFunctorCommShift (S : ShiftConeComparisons F)
    (hz : ∀ X, (S.shiftIso X 0).hom ≫ (strictShiftZero (A := B)).hom.app (F.obj X) =
      F.map ((strictShiftZero (A := A)).hom.app X))
    (ha : ∀ X s t, (S.shiftIso X (s+t)).hom ≫ (strictShiftAdd (A := B) s t).hom.app (F.obj X) =
      F.map ((strictShiftAdd (A := A) s t).hom.app X) ≫
        (S.shiftIso (shift X s) t).hom ≫ shiftMap t (S.shiftIso X s).hom) :
    F.CommShift ℤ where
  commShiftIso s := NatIso.ofComponents (fun X => S.shiftIso X s)
    (fun f => S.shiftNaturality f s)
  commShiftIso_zero := by
    ext X
    simp only [Functor.CommShift.isoZero_hom_app, NatIso.ofComponents_hom_app]
    exact (strictShiftZero (A := B)).app (F.obj X) |>.eq_comp_inv.mpr (hz X)
  commShiftIso_add s t := by
    ext X
    simp only [Functor.CommShift.isoAdd_hom_app, NatIso.ofComponents_hom_app]
    change (S.shiftIso X (s+t)).hom =
      F.map ((strictShiftAdd (A := A) s t).hom.app X) ≫ (S.shiftIso (shift X s) t).hom ≫
        shiftMap t (S.shiftIso X s).hom ≫ (strictShiftAdd (A := B) s t).inv.app (F.obj X)
    have h := ((strictShiftAdd (A := B) s t).app (F.obj X)).eq_comp_inv.mpr (ha X s t)
    simp only [Category.assoc] at h
    exact h

/-- Classes give a full and faithful restriction on natural transformations,
since the quotient is the identity on objects and surjective on maps. -/
private instance homotopyWhiskeringFull {E : Type*} [Category* E] :
    ((CategoryTheory.Functor.whiskeringLeft _ _ E).obj (homotopyQuotient A)).Full where
  map_surjective {F G} τ := by
    let σ : F ⟶ G :=
      { app := fun X => τ.app (X : RightDGModule A)
        naturality := by
          intro X Y g
          obtain ⟨f, rfl⟩ := RightDGModule.toHomotopyCategory_map_surjective g
          exact τ.naturality f }
    exact ⟨σ, NatTrans.ext rfl⟩

private instance homotopyWhiskeringFaithful {E : Type*} [Category* E] :
    ((CategoryTheory.Functor.whiskeringLeft _ _ E).obj (homotopyQuotient A)).Faithful where
  map_injective h := by
    apply NatTrans.ext
    funext X
    exact congrArg (fun τ => τ.app (X : RightDGModule A)) h

private abbrev homotopyLift (l : ClassLift hA hB F) : RightDGModule.K A ⥤ RightDGModule.K B :=
  l.functor

/-- The object comparison is natural on the strict maps whose classes define the lift. -/
private def classLiftIso (l : ClassLift hA hB F) :
    homotopyQuotient A ⋙ (homotopyLift l) ≅ F ⋙ homotopyQuotient B :=
  NatIso.ofComponents (fun X => eqToIso (l.obj X)) (fun f => l.map f)

@[instance_reducible] private def classLiftCommShift (l : ClassLift hA hB F)
    [F.CommShift ℤ] : (homotopyLift l).CommShift ℤ :=
  quotientCommShift (homotopyQuotient A) (classLiftIso l) (fun X => ⟨X, rfl⟩)

private theorem classLiftIsoCommShift (l : ClassLift hA hB F) [F.CommShift ℤ] :
    letI := classLiftCommShift l
    NatTrans.CommShift (classLiftIso l).hom ℤ :=
  quotientIso_commShift (homotopyQuotient A) (classLiftIso l) (fun X => ⟨X, rfl⟩)

set_option maxHeartbeats 1400000 in
private theorem classLiftShiftSquare (l : ClassLift hA hB F) [F.CommShift ℤ] (X : RightDGModule A)
    (s : ℤ) (ψ : F.obj (shift X s) ⟶ shift (F.obj X) s)
    (hψ : (F.commShiftIso s).hom.app X = ψ) :
    letI := classLiftCommShift l
    ((homotopyLift l).commShiftIso s).hom.app ((homotopyQuotient A).obj X) ≫
        (shiftFunctor (RightDGModule.K B) s).map ((classLiftIso l).hom.app X) =
      (classLiftIso l).hom.app ((shiftFunctor (RightDGModule A) s).obj X) ≫
        (homotopyQuotient B).map ψ := by
  letI := classLiftCommShift l
  letI := classLiftIsoCommShift l
  let R := homotopyQuotient A
  let qB := homotopyQuotient B
  let e := classLiftIso l
  have h := NatTrans.shift_app_comm e.hom s X
  rw [Functor.commShiftIso_comp_hom_app R (homotopyLift l) s X,
    Functor.commShiftIso_comp_hom_app F qB s X] at h
  have hA := @quotientCommShift_hom k _ A s X
  have hB := @quotientCommShift_hom k _ B s (F.obj X)
  erw [hA, hB, hψ] at h
  simp only [eqToHom_refl, Category.assoc] at h
  erw [(homotopyLift l).map_id, Category.id_comp, Category.comp_id] at h
  exact h

end Lifts


section CategoryArguments

private theorem commShift_of_precomp_surjective
    {C₀ C E : Type*} [Category* C₀] [Category* C] [Category* E]
    [HasShift C₀ ℤ] [HasShift C ℤ] [HasShift E ℤ]
    (q : C₀ ⥤ C) [q.CommShift ℤ] (hq : Function.Surjective q.obj)
    {F G : C ⥤ E} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    [NatTrans.CommShift (Functor.whiskerLeft q τ) ℤ] : NatTrans.CommShift τ ℤ := by
  constructor
  intro s
  ext X
  obtain ⟨Y, rfl⟩ := hq X
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft q τ) s Y
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app, Category.assoc] at h
  rw [← NatTrans.naturality_assoc] at h
  exact (cancel_epi (F.map ((q.commShiftIso s).hom.app Y))).mp h

private theorem shiftSquareOfRepresentative
    {C C' E E' : Type*} [Category* C] [Category* C'] [Category* E] [Category* E']
    [HasShift C ℤ] [HasShift C' ℤ] [HasShift E ℤ] [HasShift E' ℤ]
    {q : C ⥤ C'} {r : E ⥤ E'} {f : C ⥤ E} {d : C' ⥤ E'}
    [q.CommShift ℤ] [r.CommShift ℤ] [f.CommShift ℤ] [d.CommShift ℤ]
    (b : q ⋙ d ⟶ f ⋙ r) [NatTrans.CommShift b ℤ] (X : C) (s : ℤ) {Z Z' : E}
    (e : f.obj X ≅ Z) (e' : f.obj (X⟦s⟧) ≅ Z') (p : Z' ⟶ Z⟦s⟧)
    (he : (f.commShiftIso s).hom.app X ≫ (shiftFunctor E s).map e.hom = e'.hom ≫ p) :
    d.map ((q.commShiftIso s).hom.app X) ≫ (d.commShiftIso s).hom.app (q.obj X) ≫
      (shiftFunctor E' s).map (b.app X ≫ r.map e.hom) =
    b.app (X⟦s⟧) ≫ r.map e'.hom ≫ r.map p ≫ (r.commShiftIso s).hom.app Z := by
  have hb := NatTrans.shift_app_comm b s X
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hb
  simp only [Functor.map_comp]
  have hb' := congrArg (fun g => g ≫ (shiftFunctor E' s).map (r.map e.hom)) hb
  simp only [Category.assoc] at hb'
  rw [hb']
  rw [← r.commShiftIso_hom_naturality e.hom s, ← r.map_comp_assoc, he, r.map_comp, Category.assoc]

private theorem isTriangulated_of_localizedCones
    {C C' E' : Type*} [Category* C] [Category* C'] [Category* E']
    [HasShift C ℤ] [HasShift C' ℤ] [HasShift E' ℤ]
    [Preadditive C] [Preadditive C'] [Preadditive E']
    [HasZeroObject C] [HasZeroObject C'] [HasZeroObject E']
    [∀ s : ℤ, (shiftFunctor C s).Additive] [∀ s : ℤ, (shiftFunctor C' s).Additive]
    [∀ s : ℤ, (shiftFunctor E' s).Additive]
    [Pretriangulated C] [Pretriangulated C'] [Pretriangulated E']
    {q : C ⥤ C'} {d : C' ⥤ E'} {g : C ⥤ E'}
    [q.CommShift ℤ] [d.CommShift ℤ] [g.CommShift ℤ]
    (b : q ⋙ d ≅ g) [NatTrans.CommShift b.hom ℤ] [g.IsTriangulated]
    (covered : ∀ U : Triangle C', U ∈ distTriang C' →
      ∃ V : Triangle C, V ∈ distTriang C ∧ Nonempty (U ≅ q.mapTriangle.obj V)) :
    d.IsTriangulated where
  map_distinguished U hU := by
    obtain ⟨V, hV, ⟨e⟩⟩ := covered U hU
    let i := d.mapTriangle.mapIso e ≪≫ (Functor.mapTriangleCompIso q d).symm.app V ≪≫
      (Functor.mapTriangleIso b).app V
    exact isomorphic_distinguished _ (g.map_distinguished V hV) _ i

end CategoryArguments


section Exactness

open Specs.DerivedFormalization.DG.ShiftCone (shift shiftMap cone coneInclusion coneProjection)
open RightDGModule (homotopyShift)
open CategoryTheory.Functor
  (isoWhiskerRight isoWhiskerLeft isoWhiskerRight_hom isoWhiskerLeft_hom)

set_option maxHeartbeats 1000000 in
private theorem classLiftTriangulated
    {A : DGCategory.{u,vA,w} k} {B : DGCategory.{u,v,z} k}
    {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
    {F : RightDGModule A ⥤ RightDGModule B} [F.CommShift ℤ]
    (l : ClassLift hA hB F) (S : ShiftConeComparisons F)
    (hS : ∀ X : RightDGModule A, (F.commShiftIso (1 : ℤ)).hom.app X = (S.shiftIso X 1).hom)
    [Functor.Additive (homotopyLift l)] :
    letI := classLiftCommShift l
    (homotopyLift l).IsTriangulated := by
  letI := classLiftCommShift l
  let l' : RightDGModule.K A ⥤ RightDGModule.K B := l.functor
  let e := classLiftIso l
  let qA := homotopyQuotient A
  let qB := homotopyQuotient B
  let S' := shiftFunctor (RightDGModule.K B) (1 : ℤ)
  constructor
  intro U hU
  obtain ⟨M, N, f, ⟨i⟩⟩ := (RightDGModule.distinguished_iff_cone_triangle U).mp hU
  refine isomorphic_distinguished _ (RightDGModule.coneTriangle_distinguished (F.map f)) _
    (l'.mapTriangle.mapIso i ≪≫ ?_)
  refine Triangle.isoMk _ _ (e.app M) (e.app N)
    (e.app (cone f) ≪≫ qB.mapIso (S.coneIso f)) ?_ ?_ ?_
  · exact e.hom.naturality f
  · change l'.map (qA.map (coneInclusion f)) ≫
        (e.hom.app (cone f) ≫ qB.map (S.coneIso f).hom) =
      e.hom.app N ≫ qB.map (coneInclusion (F.map f))
    have h := e.hom.naturality (coneInclusion f)
    change l'.map (qA.map (coneInclusion f)) ≫ e.hom.app (cone f) =
      e.hom.app N ≫ qB.map (F.map (coneInclusion f)) at h
    rw [reassoc_of% h, ← qB.map_comp, S.inclusion]
  · change (l'.map (-(qA.map (coneProjection f)) ≫ 𝟙 _) ≫
      (l'.commShiftIso (1 : ℤ)).hom.app (M : RightDGModule.K A)) ≫ S'.map (e.hom.app M) =
      (e.hom.app (cone f) ≫ qB.map (S.coneIso f).hom) ≫
        (-(qB.map (coneProjection (F.map f))) ≫ 𝟙 _)
    simp only [Category.comp_id, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg,
      Category.assoc]
    apply congrArg Neg.neg
    have h := e.hom.naturality (coneProjection f)
    change l'.map (qA.map (coneProjection f)) ≫ e.hom.app (shift M 1) =
      e.hom.app (cone f) ≫ qB.map (F.map (coneProjection f)) at h
    rw [classLiftShiftSquare l M 1 (S.shiftIso M 1).hom (hS M)]
    change l'.map (qA.map (coneProjection f)) ≫ e.hom.app (shift M 1) ≫
        qB.map (S.shiftIso M 1).hom =
      e.hom.app (cone f) ≫ qB.map (S.coneIso f).hom ≫ qB.map (coneProjection (F.map f))
    rw [reassoc_of% h, ← qB.map_comp, S.projection, qB.map_comp]

private theorem homotopyAdjunctionCommShift
    {A : DGCategory.{u,vA,w} k} {B : DGCategory.{u,v,z} k}
    {F : RightDGModule A ⥤ RightDGModule B} {H : RightDGModule B ⥤ RightDGModule A}
    [F.CommShift ℤ] [H.CommShift ℤ] {a : F ⊣ H} [NatTrans.CommShift a.unit ℤ]
    {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B} (d : DescentData hA hB F H a)
    [Functor.CommShift (homotopyLift d.FK) ℤ]
    [Functor.CommShift (homotopyLift d.HK) ℤ]
    (eF : homotopyQuotient A ⋙ homotopyLift d.FK ≅ F ⋙ homotopyQuotient B)
    (eH : homotopyQuotient B ⋙ homotopyLift d.HK ≅ H ⋙ homotopyQuotient A)
    [NatTrans.CommShift eF.hom ℤ] [NatTrans.CommShift eH.hom ℤ]
    (eqF : ∀ X : RightDGModule A, eF.hom.app X = eqToHom (d.FK.obj X))
    (eqH : ∀ Y : RightDGModule B, eH.hom.app Y = eqToHom (d.HK.obj Y)) :
    (show (homotopyLift d.FK) ⊣
      (homotopyLift d.HK) from d.aK).CommShift ℤ := by
  let qA := homotopyQuotient A
  let qB := homotopyQuotient B
  let FK : RightDGModule.K A ⥤ RightDGModule.K B := d.FK.functor
  let HK : RightDGModule.K B ⥤ RightDGModule.K A := d.HK.functor
  let aK : FK ⊣ HK := d.aK
  let i : qA ⋙ (FK ⋙ HK) ≅ (F ⋙ H) ⋙ qA :=
    (Functor.associator qA FK HK).symm ≪≫ isoWhiskerRight eF HK ≪≫
      Functor.associator F qB HK ≪≫ isoWhiskerLeft F eH ≪≫ (Functor.associator F H qA).symm
  let u : qA ⋙ 𝟭 _ ⟶ (F ⋙ H) ⋙ qA :=
    qA.rightUnitor.hom ≫ qA.leftUnitor.inv ≫ Functor.whiskerRight a.unit qA
  have he : Functor.whiskerLeft qA aK.unit = u ≫ i.inv := by
    apply (cancel_mono i.hom).mp
    simp only [Category.assoc, i.inv_hom_id, Category.comp_id]
    ext X
    simp only [i, u, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.id_comp, eqF, eqH]
    dsimp only [Functor.comp_obj]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    exact d.unitK X
  letI : NatTrans.CommShift i.hom ℤ := by
    simp only [i, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.symm_hom]
    infer_instance
  letI : NatTrans.CommShift (Functor.whiskerLeft qA aK.unit) ℤ := by
    rw [he]
    dsimp only [u]
    infer_instance
  apply Adjunction.CommShift.mk'
  exact commShift_of_precomp_surjective qA (fun X => ⟨X, rfl⟩) aK.unit


set_option maxHeartbeats 2650000 in
/-- The signed reindexings on strict modules induce the shift structures of
both adjoints on the fixed derived categories. -/
theorem localizedExactness :
    Specs.DerivedFormalization.DG.LocalizedBimoduleExactness.LocalizedExactness.{u,v,w,z} := by
  intro k _ A B T L G E a laws hpT S R hS hR hA hB d
  let cA := coneLocalization.{u,max v z,w} A hA
  let cB := coneLocalization.{u,max v w,z} B hB
  letI : Category (D A hA) := derivedCategoryInstance A hA
  letI : Category (D B hB) := derivedCategoryInstance B hB
  letI := cA.shiftD
  letI := cA.addD
  letI := cA.zeroD
  letI := cA.addShiftD
  letI := cA.trianglesD
  letI := cB.shiftD
  letI := cB.addD
  letI := cB.zeroD
  letI := cB.addShiftD
  letI := cB.trianglesD
  let F := ordinaryTensor.{u,v,w,z} L
  let H := ordinaryHom.{u,v,w,z} G
  let rA := homotopyQuotient A
  let rB := homotopyQuotient B
  letI : rA.CommShift ℤ := toHomotopyCategoryCommShift
  letI : rB.CommShift ℤ := toHomotopyCategoryCommShift
  let FK : RightDGModule.K A ⥤ RightDGModule.K B := d.FK.functor
  let HK : RightDGModule.K B ⥤ RightDGModule.K A := d.HK.functor
  let aK : FK ⊣ HK := d.aK
  let QA : RightDGModule.K A ⥤ D A hA := Q A hA
  let QB : RightDGModule.K B ⥤ D B hB := Q B hB
  letI : QA.CommShift ℤ := cA.quotientShift
  letI : QB.CommShift ℤ := cB.quotientShift
  letI : QA.IsTriangulated := cA.quotientTriangulated
  letI : QB.IsTriangulated := cB.quotientTriangulated
  let J : D A hA ⥤ RightDGModule.K A := d.J
  let aJ : J ⊣ QA := d.aJ
  let LD : D A hA ⥤ D B hB := (J ⋙ FK) ⋙ QB
  let HD : D B hB ⥤ D A hA := d.HD
  let aD : LD ⊣ HD := d.aD
  let b : QB ⋙ HD ≅ HK ⋙ QA := d.b
  have zF := tensorShiftZero.{u,v,w,z} S hS
  have aF := tensorShiftAdd.{u,v,w,z} S hS
  have zH (N : RightDGModule B) :
      (R.shiftIso N 0).hom ≫ (strictShiftZero (A := A)).hom.app (H.obj N) =
        H.map ((strictShiftZero (A := B)).hom.app N) :=
    ((R.shiftIso N 0).inv_comp_eq.mp (homShiftZero_inv.{u,v,w,z} R hR N)).symm
  have aH (N : RightDGModule B) (s t : ℤ) :
      (R.shiftIso N (s+t)).hom ≫ (strictShiftAdd (A := A) s t).hom.app (H.obj N) =
        H.map ((strictShiftAdd (A := B) s t).hom.app N) ≫
          (R.shiftIso (shift N s) t).hom ≫ shiftMap t (R.shiftIso N s).hom := by
    let i := R.shiftIso (shift N s) t ≪≫
      (RightDGModule.strictShift (A := A) t).mapIso (R.shiftIso N s)
    have hi : (strictShiftAdd (A := A) s t).hom.app (H.obj N) ≫ i.inv =
        (R.shiftIso N (s+t)).inv ≫ H.map ((strictShiftAdd (A := B) s t).hom.app N) := by
      simpa only [i, Iso.trans_inv, Functor.mapIso_inv, Category.assoc] using
        homShiftAdd_inv.{u,v,w,z} R hR N s t
    change _ = H.map ((strictShiftAdd (A := B) s t).hom.app N) ≫ i.hom
    rw [← cancel_mono i.inv, Category.assoc, hi, Iso.hom_inv_id_assoc,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  letI : F.CommShift ℤ := strictFunctorCommShift S zF aF
  letI : H.CommShift ℤ := strictFunctorCommShift R zH aH
  letI : FK.CommShift ℤ := classLiftCommShift d.FK
  letI : HK.CommShift ℤ := classLiftCommShift d.HK
  letI : NatTrans.CommShift a.unit ℤ := by
    constructor
    intro s
    ext M
    change 𝟙 _ ≫ shiftMap s (a.unit.app M) =
      a.unit.app (shift M s) ≫ H.map (S.shiftIso M s).hom ≫ (R.shiftIso (F.obj M) s).hom
    rw [Category.id_comp]
    exact ((R.shiftIso (F.obj M) s).comp_inv_eq.mp
      (strictUnitShift_inv.{u,v,w,z} laws S hS R hR M s).symm)
  let eF := classLiftIso d.FK
  let eH := classLiftIso d.HK
  letI : NatTrans.CommShift eF.hom ℤ := classLiftIsoCommShift d.FK
  letI : NatTrans.CommShift eH.hom ℤ := classLiftIsoCommShift d.HK
  letI : aK.CommShift ℤ := homotopyAdjunctionCommShift d eF eH (fun _ => rfl) (fun _ => rfl)
  letI : HK.IsRightAdjoint := aK.isRightAdjoint
  letI : HK.Additive := HK.additive_of_preserves_binary_products
  letI : HK.IsTriangulated := classLiftTriangulated d.HK R (fun _ => rfl)
  letI : QB.IsLocalization (W B) := inferInstanceAs ((W B).Q.IsLocalization (W B))
  letI : Localization.Lifting QB (W B) (HK ⋙ QA) HD := ⟨b⟩
  letI : HD.CommShift ℤ := Functor.commShiftOfLocalization QB (W B) ℤ (HK ⋙ QA) HD
  letI : NatTrans.CommShift b.hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization QB (W B) ℤ (HK ⋙ QA) HD
  letI : HD.IsTriangulated := isTriangulated_of_localizedCones b (by
    intro U hU
    obtain ⟨M, N, _, _, f, e⟩ := cB.localizedConeTriangles.2 U hU
    let V := DerivedTriangles.coneTriangle hB cB.shiftK (cB.shiftObj M 1) f
    exact ⟨V, (cB.coneTriangles V).2 ⟨M, N, f, ⟨Iso.refl _⟩⟩, e⟩)
  letI : J.CommShift ℤ := aJ.leftAdjointCommShift ℤ
  letI : aJ.CommShift ℤ := aJ.commShift_of_rightAdjoint ℤ
  letI : aD.CommShift ℤ := composedAdjunctionCommShift aJ aK aD b d.unitD
  letI : LD.IsTriangulated := aD.isTriangulated_leftAdjoint
  refine ⟨cA, cB, inferInstanceAs (LD.CommShift ℤ), inferInstanceAs (HD.CommShift ℤ),
    inferInstanceAs LD.IsTriangulated, inferInstanceAs HD.IsTriangulated, inferInstanceAs (aD.CommShift ℤ),
    ?_, ?_, ?_⟩
  · intro P hP
    letI := isIso_resolutionCounit hA J aJ P hP
    change IsIso (QB.map (FK.map (aJ.counit.app (P : RightDGModule.K A)) ≫ eF.hom.app P))
    infer_instance
  · intro N s
    have he := classLiftShiftSquare d.HK N s (R.shiftIso N s).hom rfl
    have h := shiftSquareOfRepresentative (q := QB) (r := QA) (f := HK) (d := HD)
      b.hom (N : RightDGModule.K B) s
      (eH.app N) (eH.app (shift N s)) (rA.map (R.shiftIso N s).hom) he
    have hb (M : RightDGModule B) : (d.homRepresentative M).hom =
        b.hom.app M ≫ QA.map (eH.hom.app M) := rfl
    erw [coneLocalization_onShift_hom, coneLocalization_onShift_hom, hb, hb,
      Category.assoc (b.hom.app (shift N s))]
    exact h

  · intro P s hP hPs
    let τ : QA ⋙ LD ⟶ FK ⋙ QB := resolutionCounitComparison aJ FK QB
    letI : NatTrans.CommShift τ ℤ := resolutionCounitComparison_commShift aJ FK QB
    have he := classLiftShiftSquare d.FK P s (S.shiftIso P s).hom rfl
    have h := shiftSquareOfRepresentative (q := QA) (r := QB) (f := FK) (d := LD)
      τ (P : RightDGModule.K A) s
      (eF.app P) (eF.app (shift P s)) (rB.map (S.shiftIso P s).hom) he
    have ht (M : RightDGModule A) : τ.app (M : RightDGModule.K A) ≫ QB.map (eF.app M).hom =
        d.tensorRepresentative M := by
      erw [resolutionCounitComparison_app, ← QB.map_comp]
      rfl
    erw [ht P, reassoc_of% ht (shift P s)] at h
    erw [coneLocalization_onShift_hom, coneLocalization_onShift_hom]
    exact h

end Exactness

end

end DerivedFormalization.DGBimodule
