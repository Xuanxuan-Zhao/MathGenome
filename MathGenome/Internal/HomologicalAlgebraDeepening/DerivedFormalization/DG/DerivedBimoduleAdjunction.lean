import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedBimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleTensorComparisons
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.LocalizedBimoduleExactness
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleCoefficientCompatibility
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveInvariance
import Mathlib.CategoryTheory.Localization.Adjunction
import Batteries.Tactic.OpenPrivate

open CategoryTheory HomologicalComplex

universe u v w vA z t s

namespace DerivedFormalization.DGBimodule

open RightDGModule
open Specs.DerivedFormalization.DG.BimoduleAdjunction
open Specs.DerivedFormalization.DG.DerivedBimoduleAdjunction
open Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance)
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)

noncomputable section

variable {k : Type u} [CommRing k]

set_option autoImplicit false

section Descent

universe v' w'

variable {C : DGCategory.{u,v',w'} k} {E : DGCategory.{u,v,z} k}
variable (F : RightDGModule C ⥤ RightDGModule E)

private noncomputable def representative {X Y : K C} (f : X ⟶ Y) : RightDGModuleHomModel X Y :=
  (homotopyClass_surjective f).choose

private theorem representative_class {X Y : K C} (f : X ⟶ Y) :
    homotopyClass (representative f) = f :=
  (homotopyClass_surjective f).choose_spec

set_option maxHeartbeats 700000 in
/-- A strict functor respecting right-linear homotopies induces a functor on classes. -/
@[reducible] private def onHomotopy
    (hF : ∀ {X Y : RightDGModule C} (f g : X ⟶ Y), homotopyClass f = homotopyClass g →
      homotopyClass (F.map f) = homotopyClass (F.map g)) :
    K C ⥤ K E where
  obj X := F.obj X
  map f := homotopyClass (F.map (representative f))
  map_id X := by
    let X₀ : RightDGModule C := X
    let i : X₀ ⟶ X₀ := 𝟙 X₀
    have h₁ : homotopyClass i = 𝟙 X := (toHomotopyCategory C).map_id X₀
    have h₂ : homotopyClass (representative (𝟙 X)) = homotopyClass i :=
      (representative_class (𝟙 X)).trans h₁.symm
    change homotopyClass (F.map (representative (𝟙 X))) = homotopyClass (𝟙 (F.obj X₀))
    exact (@hF X₀ X₀ _ i h₂).trans (congrArg (fun f => homotopyClass f) (F.map_id X₀))
  map_comp f g := by
    change homotopyClass (F.map (representative (f ≫ g))) =
      (toHomotopyCategory E).map (F.map (representative f)) ≫
        (toHomotopyCategory E).map (F.map (representative g))
    rw [← Functor.map_comp, ← F.map_comp]
    apply hF
    rw [representative_class]
    change _ = (toHomotopyCategory C).map (representative f ≫ representative g)
    rw [Functor.map_comp]
    exact (congrArg₂ (fun x y => x ≫ y) (representative_class f) (representative_class g)).symm

private theorem onHomotopy_map
    (hF : ∀ {X Y : RightDGModule C} (f g : X ⟶ Y), homotopyClass f = homotopyClass g →
      homotopyClass (F.map f) = homotopyClass (F.map g))
    {X Y : RightDGModule C} (f : X ⟶ Y) :
    (onHomotopy F hF).map (homotopyClass f) = homotopyClass (F.map f) :=
  hF _ _ (representative_class _)

/-- Localize a strict functor which also preserves objectwise quasi-isomorphisms. -/
private def descend (hC : HomotopyCategoryLaws C) (hE : HomotopyCategoryLaws E)
    (hF : ∀ {X Y : RightDGModule C} (f g : X ⟶ Y), homotopyClass f = homotopyClass g →
      homotopyClass (F.map f) = homotopyClass (F.map g))
    (hQ : ∀ {X Y : RightDGModule C} (f : X ⟶ Y), IsQuasiIso f → IsQuasiIso (F.map f)) :
    LocalizedFunctor hC hE F := by
  letI : (Q C hC).IsLocalization (quasiIsomorphisms C) := Q_isLocalization C hC
  let H := onHomotopy F hF
  have hinv : (quasiIsomorphisms C).IsInvertedBy (H ⋙ Q E hE) := by
    rintro X Y f ⟨g, rfl, hg⟩
    change IsIso ((Q E hE).map (H.map (homotopyClass g)))
    rw [onHomotopy_map]
    exact Localization.inverts (Q E hE) (quasiIsomorphisms E) _
      ⟨F.map g, rfl, hQ g hg⟩
  let F' : D C hC ⥤ D E hE := Localization.lift (H ⋙ Q E hE) hinv (Q C hC)
  let e : Q C hC ⋙ F' ≅ H ⋙ Q E hE := Localization.fac (H ⋙ Q E hE) hinv (Q C hC)
  refine ⟨H, F', fun _ => rfl, ?_, e, fun f => hQ f⟩
  intro X Y f
  exact heq_of_eq (onHomotopy_map F hF f)

end Descent

section Native

variable {A : DGCategory.{u,vA,w} k} {B : DGCategory.{u,v,z} k}
variable {T : DGBimodule A B} (G : InternalHomModel T)

private theorem objectwiseHomSquare {N N' : RightDGModule B} (f : N ⟶ N') (a : A.Obj) :
    (G.objectwise N a).hom ≫ (G.functor.map f).app a =
      homComplexMap (T.obj a) f ≫ (G.objectwise N' a).hom := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact G.map f a i

private theorem nativeHomPreserves {N N' : RightDGModule B} (f : N ⟶ N')
    (hT : ∀ a, IsKProjective (T.obj a)) (hf : IsQuasiIso f) (a : A.Obj) :
    QuasiIso ((G.functor.map f).app a) := by
  have : QuasiIso (homComplexMap (T.obj a) f) := (hT a).homComplexMap_quasiIso f hf
  apply (quasiIso_iff_comp_left (G.objectwise N a).hom _).mp
  rw [objectwiseHomSquare]
  infer_instance

private theorem isoComponent_cancel {C D : ModuleCochain k} (e : C ≅ D) (i : ℤ)
    (x : D.X i) : e.hom.f i (e.inv.f i x) = x :=
  congrArg (fun f : D ⟶ D => f.f i x) e.inv_hom_id

private theorem postcompose_assoc {X Y N P : RightDGModule B} (s i j n ir nr : ℤ)
    (h : i+j=n) (hi : i+s=ir) (hn : n+s=nr)
    (H : GradedHom N P s) (g : GradedHom Y N i) (f : GradedHom X Y j) :
    (dgCategory B).comp s n nr (by omega) H ((dgCategory B).comp i j n h g f) =
      (dgCategory B).comp ir j nr (by omega)
        ((dgCategory B).comp s i ir (by omega) H g) f := by
  apply GradedHom.ext
  intro a p q e
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [compositionFormula s n nr _ H _ a p (p+n) q rfl (by omega),
    compositionFormula i j n h g f a p (p+j) (p+n) rfl (by omega),
    compositionFormula ir j nr _ _ f a p (p+j) q rfl (by omega),
    compositionFormula s i ir _ H g a (p+j) (p+n) q (by omega) (by omega)]

private theorem differential_of_homotopy {N P : RightDGModule B} {f g : N ⟶ P}
    (H : GradedHom N P (-1))
    (e : Specs.DerivedFormalization.DG.HomComplex.HomotopyEquation f g H) :
    (homComplex N P).d (-1) 0 H = (strictCycle f).val - (strictCycle g).val := by
  apply GradedHom.ext
  intro a i q h
  rw [add_zero] at h
  subst h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [boundary_component]
  exact (e a i x).symm

private theorem postcompose_boundary {X N P : RightDGModule B} {f g : N ⟶ P}
    (H : GradedHom N P (-1))
    (e : (homComplex N P).d (-1) 0 H = (strictCycle f).val - (strictCycle g).val)
    (i : ℤ) (x : GradedHom X N (i+1)) :
    (homComplex X P).d i (i+1) ((dgCategory B).comp (-1) (i+1) i (by omega) H x) +
      (dgCategory B).comp (-1) (i+1+1) (i+1) (by omega) H
        ((homComplex X N).d (i+1) (i+1+1) x) =
      (dgCategory B).comp 0 (i+1) (i+1) (zero_add _) (strictCycle f).val x -
        (dgCategory B).comp 0 (i+1) (i+1) (zero_add _) (strictCycle g).val x := by
  rw [(dgCategory B).toData.leibniz]
  change (dgCategory B).comp 0 (i+1) (i+1) _ ((homComplex N P).d (-1) 0 H) x +
      (-1 : ℤ).negOnePow • _ + _ = _
  rw [e, map_sub, LinearMap.sub_apply]
  simp [Int.negOnePow_neg, Int.negOnePow_one]

private theorem postcompose_homotopic {N P : RightDGModule B} (f g : N ⟶ P)
    (h : homotopyClass f = homotopyClass g) :
    homotopyClass ((G.functor ⋙ placeHom.{u,w,vA,max v z}).map f) =
      homotopyClass ((G.functor ⋙ placeHom.{u,w,vA,max v z}).map g) := by
  obtain ⟨H, hh⟩ := (homotopyCriterion f g).mp h
  let F := G.functor ⋙ placeHom.{u,w,vA,max v z}
  let component (a : A.Obj) (i q : ℤ) (e : i+(-1)=q) :
      (F.obj N |>.complex a).X i ⟶ (F.obj P |>.complex a).X q :=
    ModuleCat.ofHom <|
      ULift.moduleEquiv.symm.toLinearMap.comp <|
      (G.objectwise P a).hom.f q |>.hom.comp
        (((dgCategory B).comp (-1) i q (by omega) H).comp
          (((G.objectwise N a).inv.f i).hom.comp ULift.moduleEquiv.toLinearMap))
  let h' : GradedHom (F.obj N) (F.obj P) (-1) :=
    GradedHom.mk component (by
      intro a b i j n ir nr e hi hn x u'
      apply ULift.ext
      let y := (G.objectwise N b).inv.f i x.down
      have hy : (G.objectwise N b).hom.f i y = x.down :=
        isoComponent_cancel (G.objectwise N b) i x.down
      change (G.objectwise P a).hom.f nr
          ((dgCategory B).comp (-1) n nr _ H
            ((G.objectwise N a).inv.f n ((G.functor.obj N).act i j n e x.down u'.down))) =
        (G.functor.obj P).act ir j nr _
          ((G.objectwise P b).hom.f ir ((dgCategory B).comp (-1) i ir _ H y)) u'.down
      rw [← hy, G.action, G.action]
      have cancel (c : A.Obj) (r : ℤ) (b' : GradedHom (T.obj c) N r) :
          (G.objectwise N c).inv.f r ((G.objectwise N c).hom.f r b') = b' :=
        isoComponent_cancel (G.objectwise N c).symm r b'
      rw [cancel, postcompose_assoc (-1) i j n ir nr e hi hn])
  apply (homotopyCriterion (F.map f) (F.map g)).mpr
  refine ⟨h', ?_⟩
  have hd := differential_of_homotopy H hh
  have atSuccessor (a : A.Obj) (i : ℤ) (x : ((F.obj N).complex a).X (i+1)) :
      ((F.map f).app a).f (i+1) x - ((F.map g).app a).f (i+1) x =
        ((F.obj P).complex a).d i (i+1) (h'.app a (i+1) i (by omega) x) +
        h'.app a (i+1+1) (i+1) (by omega) (((F.obj N).complex a).d (i+1) (i+1+1) x) := by
    apply ULift.ext
    let y := (G.objectwise N a).inv.f (i+1) x.down
    have hy : (G.objectwise N a).hom.f (i+1) y = x.down :=
      isoComponent_cancel (G.objectwise N a) (i+1) x.down
    change ((G.functor.map f).app a).f (i+1) x.down -
        ((G.functor.map g).app a).f (i+1) x.down =
      ((G.functor.obj P).complex a).d i (i+1)
        ((G.objectwise P a).hom.f i ((dgCategory B).comp (-1) (i+1) i _ H y)) +
      (G.objectwise P a).hom.f (i+1)
        ((dgCategory B).comp (-1) (i+1+1) (i+1) _ H ((G.objectwise N a).inv.f (i+1+1)
          (((G.functor.obj N).complex a).d (i+1) (i+1+1) x.down)))
    rw [← hy, G.map, G.map]
    have comm {C D : ModuleCochain k} (ϕ : C ⟶ D) (m n : ℤ) (b : C.X m) :
        D.d m n (ϕ.f m b) = ϕ.f n (C.d m n b) :=
      congrArg (fun l : C.X m ⟶ D.X n => l b) (ϕ.comm m n)
    have cancel (r : ℤ) (b : GradedHom (T.obj a) N r) :
        (G.objectwise N a).inv.f r ((G.objectwise N a).hom.f r b) = b :=
      isoComponent_cancel (G.objectwise N a).symm r b
    rw [comm (G.objectwise P a).hom, comm (G.objectwise N a).hom, cancel]
    simp only [← map_sub, ← map_add]
    exact congrArg (fun b => (G.objectwise P a).hom.f (i+1) b)
      (postcompose_boundary H hd i y).symm
  intro a i
  have aux (j i : ℤ) (e : i = j+1) (x : ((F.obj N).complex a).X i) :
      ((F.map f).app a).f i x - ((F.map g).app a).f i x =
        ((F.obj P).complex a).d j i (h'.app a i j (by omega) x) +
        h'.app a (i+1) i (by omega) (((F.obj N).complex a).d i (i+1) x) := by
    subst i
    exact atSuccessor a j x
  exact aux (i-1) i (by omega)

end Native

theorem nativeHomPreservesQuasiIsomorphisms : NativeHomPreservesQuasiIsomorphisms.{u,v,w,vA,z} := by
    intro k _ A B T G hT N N' f hf a
    exact nativeHomPreserves G f hT hf a

theorem nativeHomDescent : NativeHomDescent.{u,v,w,vA,z} := by
  intro k _ A B T G hT hB hA
  refine ⟨descend (G.functor ⋙ placeHom.{u,w,vA,max v z}) hB hA
    (postcompose_homotopic G) ?_⟩
  intro N P f hf a
  have : QuasiIso ((G.functor.map f).app a) := nativeHomPreserves G f hT hf a
  change QuasiIso (((ModuleCat.uliftFunctor.{vA,max v z} k).mapHomologicalComplex
    (ComplexShape.up ℤ)).map ((G.functor.map f).app a))
  infer_instance

theorem tensorPreservesKProjectives : TensorPreservesKProjectives.{u,v,w,z} := by
  intro k _ A B T L G E hT P hP N hN i
  have hGN : ∀ a, (((ordinaryHom.{u,v,w,z} G).obj N).complex a).Acyclic := by
    intro a n
    exact (hT a N hN n).of_iso (G.objectwise N a)
  exact (hP ((ordinaryHom.{u,v,w,z} G).obj N) hGN i).of_iso (E P N).symm

section HomotopyAdjunction

variable {A : DGCategory.{u,max v w z,w} k} {B : DGCategory.{u,max v w z,z} k}
variable {T : DGBimodule A B} {L : TensorModel T} {G : InternalHomModel T}

variable (E : OrdinaryCurryFamily.{u,v,w,z} L G)
variable (adj : ordinaryTensor.{u,v,w,z} L ⊣ ordinaryHom.{u,v,w,z} G)
variable (laws : StrictLaws.{u,v,w,z} L G E adj)

open Specs.DerivedFormalization.DG.Basic (cyclesZero boundariesZero classOf)

universe c

private theorem cohomologyClass_eq_of_iso {C D : ModuleCochain.{u,c} k}
    (e : C ≅ D) (x y : cyclesZero C) (x' y' : cyclesZero D)
    (hx : e.hom.f 0 x.val = x'.val) (hy : e.hom.f 0 y.val = y'.val) :
    classOf x = classOf y ↔ classOf x' = classOf y' := by
  rw [Submodule.Quotient.eq, Submodule.Quotient.eq]
  change (x-y ∈ LinearMap.range _) ↔ (x'-y' ∈ LinearMap.range _)
  rw [LinearMap.mem_range, LinearMap.mem_range]
  have compare (h : C.X (-1)) :
      D.d (-1) 0 (e.hom.f (-1) h) = e.hom.f 0 (C.d (-1) 0 h) :=
    congrArg (fun f : C.X (-1) ⟶ D.X 0 => f h) (e.hom.comm (-1) 0)
  have sub : e.hom.f 0 (x.val - y.val) = x'.val - y'.val := by
    change (e.hom.f 0).hom (x.val - y.val) = _
    rw [map_sub]
    exact congrArg₂ (· - ·) hx hy
  constructor
  · rintro ⟨h, eq⟩
    refine ⟨e.hom.f (-1) h, Subtype.ext ?_⟩
    change D.d (-1) 0 (e.hom.f (-1) h) = x'.val - y'.val
    rw [compare]
    exact (congrArg (fun a => e.hom.f 0 (Subtype.val a)) eq).trans sub
  · rintro ⟨h, eq⟩
    refine ⟨e.inv.f (-1) h, Subtype.ext ?_⟩
    apply (ModuleCat.mono_iff_injective (e.hom.f 0)).mp inferInstance
    change e.hom.f 0 (C.d (-1) 0 (e.inv.f (-1) h)) = e.hom.f 0 (x.val - y.val)
    rw [← compare, isoComponent_cancel, sub]
    exact congrArg Subtype.val eq

include E adj laws

private theorem curryClass_iff {M : RightDGModule A} {N : RightDGModule B}
    (f g : (ordinaryTensor.{u,v,w,z} L).obj M ⟶ N) :
    homotopyClass f = homotopyClass g ↔
      homotopyClass (adj.homEquiv M N f) = homotopyClass (adj.homEquiv M N g) :=
  cohomologyClass_eq_of_iso (E M N) _ _ _ _
    (laws.homEquiv M N f).symm (laws.homEquiv M N g).symm

private theorem tensor_respects_homotopy {M M' : RightDGModule A} (f g : M ⟶ M')
    (h : homotopyClass f = homotopyClass g) :
    homotopyClass ((ordinaryTensor.{u,v,w,z} L).map f) =
      homotopyClass ((ordinaryTensor.{u,v,w,z} L).map g) := by
  apply (curryClass_iff E adj laws _ _).mpr
  rw [← Category.comp_id ((ordinaryTensor.{u,v,w,z} L).map f),
    ← Category.comp_id ((ordinaryTensor.{u,v,w,z} L).map g),
    adj.homEquiv_naturality_left, adj.homEquiv_naturality_left]
  let H := toHomotopyCategory A
  let t := adj.homEquiv M' _ (𝟙 _)
  change H.map (f ≫ t) = H.map (g ≫ t)
  rw [H.map_comp, H.map_comp]
  exact congrArg (fun a => a ≫ (toHomotopyCategory A).map
    (adj.homEquiv M' _ (𝟙 _))) h

private theorem hom_respects_homotopy {N N' : RightDGModule B} (f g : N ⟶ N')
    (h : homotopyClass f = homotopyClass g) :
    homotopyClass ((ordinaryHom.{u,v,w,z} G).map f) =
      homotopyClass ((ordinaryHom.{u,v,w,z} G).map g) := by
  have eq (a : N ⟶ N') :
      adj.homEquiv _ _ (adj.counit.app N ≫ a) = (ordinaryHom.{u,v,w,z} G).map a := by
    rw [adj.homEquiv_naturality_right]
    let X := (ordinaryHom.{u,v,w,z} G).obj N
    have e : adj.homEquiv X N (adj.counit.app N) = 𝟙 X := by
      apply (adj.homEquiv X N).symm.injective
      rw [Equiv.symm_apply_apply, adj.homEquiv_counit]
      have m := (ordinaryTensor.{u,v,w,z} L).map_id X
      rw [m, Category.id_comp]
    change adj.homEquiv X N (adj.counit.app N) ≫ (ordinaryHom.{u,v,w,z} G).map a = _
    rw [e, Category.id_comp]
  rw [← eq f, ← eq g]
  apply (curryClass_iff E adj laws _ _).mp
  let H := toHomotopyCategory B
  change H.map (adj.counit.app N ≫ f) = H.map (adj.counit.app N ≫ g)
  rw [H.map_comp, H.map_comp]
  exact congrArg (fun a => (toHomotopyCategory B).map (adj.counit.app N) ≫ a) h

set_option backward.isDefEq.respectTransparency false in
private def homotopyAdjunction :
    onHomotopy (ordinaryTensor.{u,v,w,z} L) (tensor_respects_homotopy E adj laws) ⊣
      onHomotopy (ordinaryHom.{u,v,w,z} G) (hom_respects_homotopy E adj laws) := by
  let F := onHomotopy (ordinaryTensor.{u,v,w,z} L) (tensor_respects_homotopy E adj laws)
  let H := onHomotopy (ordinaryHom.{u,v,w,z} G) (hom_respects_homotopy E adj laws)
  let unit : 𝟭 (K A) ⟶ F ⋙ H :=
    { app := fun X => homotopyClass (adj.unit.app X)
      naturality := by
        intro X Y f
        obtain ⟨f, rfl⟩ := homotopyClass_surjective f
        change homotopyClass f ≫ homotopyClass (adj.unit.app Y) =
          homotopyClass (adj.unit.app X) ≫ H.map (F.map (homotopyClass f))
        have eF : F.map (homotopyClass f) = homotopyClass ((ordinaryTensor.{u,v,w,z} L).map f) :=
          onHomotopy_map _ (tensor_respects_homotopy E adj laws) f
        have eH : H.map (homotopyClass ((ordinaryTensor.{u,v,w,z} L).map f)) =
            homotopyClass ((ordinaryHom.{u,v,w,z} G).map ((ordinaryTensor.{u,v,w,z} L).map f)) :=
          onHomotopy_map _ (hom_respects_homotopy E adj laws) _
        rw [eF, eH]
        let Q := toHomotopyCategory A
        change Q.map f ≫ Q.map (adj.unit.app Y) =
          Q.map (adj.unit.app X) ≫ Q.map ((ordinaryHom.{u,v,w,z} G).map
            ((ordinaryTensor.{u,v,w,z} L).map f))
        rw [← Q.map_comp, ← Q.map_comp]
        exact congrArg (fun g => Q.map g) (adj.unit.naturality f) }
  let counit : H ⋙ F ⟶ 𝟭 (K B) :=
    { app := fun X => homotopyClass (adj.counit.app X)
      naturality := by
        intro X Y f
        obtain ⟨f, rfl⟩ := homotopyClass_surjective f
        change F.map (H.map (homotopyClass f)) ≫ homotopyClass (adj.counit.app Y) =
          homotopyClass (adj.counit.app X) ≫ homotopyClass f
        have eH : H.map (homotopyClass f) = homotopyClass ((ordinaryHom.{u,v,w,z} G).map f) :=
          onHomotopy_map _ (hom_respects_homotopy E adj laws) f
        have eF : F.map (homotopyClass ((ordinaryHom.{u,v,w,z} G).map f)) =
            homotopyClass ((ordinaryTensor.{u,v,w,z} L).map ((ordinaryHom.{u,v,w,z} G).map f)) :=
          onHomotopy_map _ (tensor_respects_homotopy E adj laws) _
        rw [eH, eF]
        let Q := toHomotopyCategory B
        change Q.map ((ordinaryTensor.{u,v,w,z} L).map
          ((ordinaryHom.{u,v,w,z} G).map f)) ≫ Q.map (adj.counit.app Y) =
            Q.map (adj.counit.app X) ≫ Q.map f
        rw [← Q.map_comp, ← Q.map_comp]
        exact congrArg (fun g => Q.map g) (adj.counit.naturality f) }
  exact
    { unit := unit
      counit := counit
      left_triangle_components := fun X => by
        change F.map (homotopyClass (adj.unit.app X)) ≫
          homotopyClass (adj.counit.app ((ordinaryTensor.{u,v,w,z} L).obj X)) = 𝟙 _
        rw [onHomotopy_map]
        let Q := toHomotopyCategory B
        change Q.map ((ordinaryTensor.{u,v,w,z} L).map (adj.unit.app X)) ≫
          Q.map (adj.counit.app ((ordinaryTensor.{u,v,w,z} L).obj X)) = Q.map (𝟙 _)
        rw [← Q.map_comp]
        exact congrArg (fun g => Q.map g) (adj.left_triangle_components (X : RightDGModule A))
      right_triangle_components := fun Y => by
        change homotopyClass (adj.unit.app ((ordinaryHom.{u,v,w,z} G).obj Y)) ≫
          H.map (homotopyClass (adj.counit.app Y)) = 𝟙 _
        rw [onHomotopy_map]
        let Q := toHomotopyCategory A
        change Q.map (adj.unit.app ((ordinaryHom.{u,v,w,z} G).obj Y)) ≫
          Q.map ((ordinaryHom.{u,v,w,z} G).map (adj.counit.app Y)) = Q.map (𝟙 _)
        rw [← Q.map_comp]
        exact congrArg (fun g => Q.map g) (adj.right_triangle_components (Y : RightDGModule B)) }

end HomotopyAdjunction

section DerivedAdjunction

open Specs.DerivedFormalization.DG.DerivedKProjective (kProjectiveObjects)

universe v' w'

local instance specHomotopyCategory (C : DGCategory.{u,v',w'} k) :
    Category (Specs.DerivedFormalization.DG.HomComplex.homotopyCategory C) :=
  inferInstanceAs (Category (K C))

variable {A : DGCategory.{u,max v w z,w} k} {B : DGCategory.{u,max v w z,z} k}
variable {T : DGBimodule A B} {L : TensorModel T} {G : InternalHomModel T}
variable (E : OrdinaryCurryFamily.{u,v,w,z} L G)
variable (adj : ordinaryTensor.{u,v,w,z} L ⊣ ordinaryHom.{u,v,w,z} G)
variable (laws : StrictLaws.{u,v,w,z} L G E adj)

open Specs.DerivedFormalization.DG.BalancedTensor (tmul)

private def representableTensorIso (L : TensorModel T) (a : A.Obj) :
    (ordinaryTensor.{u,v,w,z} L).obj (representable a) ≅ T.obj a := by
  let M := representable a
  let F := (ordinaryTensor.{u,v,w,z} L).obj M
  let e (b : B.Obj) (i : ℤ) := (L.degree M b i).symm.trans (representableEquiv T a b i)
  have el (b : B.Obj) (i) x : e b i (L.degree M b i x) = representableEquiv T a b i x := by
    simp [e]
  apply DG.CoefficientLift.isoOfComponents e
  · intro b n x
    obtain ⟨x, rfl⟩ := (L.degree M b n).surjective x
    let f := (e b (n+1)).toLinearMap.comp (((F.complex b).d n (n+1)).hom.comp
      (L.degree M b n).toLinearMap)
    let g := ((T.obj a |>.complex b).d n (n+1)).hom.comp
      ((e b n).toLinearMap.comp (L.degree M b n).toLinearMap)
    have h : f = g := by
      apply linearMap_ext T M
      intro c i j h m t
      change e b (n+1) (((L.functor.obj M).complex b).d n (n+1)
        (L.degree M b n (tmul T M b c i j n h m t))) =
        (T.obj a |>.complex b).d n (n+1) (e b n (L.degree M b n (tmul T M b c i j n h m t)))
      rw [L.d_tmul M c b i j n h m t, map_add, Units.smul_def, map_zsmul, el, el, el]
      have eq := representableEquiv_d T a b n (tmul T M b c i j n h m t)
      rw [mixedTensorComplex_d_tmul, map_add, Units.smul_def, map_zsmul] at eq
      exact eq
    exact LinearMap.congr_fun h x
  · intro b c n l q h x u'
    obtain ⟨x, rfl⟩ := (L.degree M c n).surjective x
    let f := (e b q).toLinearMap.comp (((F.act n l q h).flip u').comp
      (L.degree M c n).toLinearMap)
    let g := ((T.obj a).act n l q h).flip u' |>.comp
      ((e c n).toLinearMap.comp (L.degree M c n).toLinearMap)
    have hh : f = g := by
      apply linearMap_ext T M
      intro c' i j h' m t
      change e b q ((L.functor.obj M).act n l q h
        (L.degree M c n (tmul T M c c' i j n h' m t)) u') =
        (T.obj a).act n l q h (e c n (L.degree M c n (tmul T M c c' i j n h' m t))) u'
      rw [L.act_tmul M c' i j n l q h' h m t u', el, el]
      have eq := representableEquiv_act T a n l q h (tmul T M c c' i j n h' m t) u'
      rw [mixedTensorModule_act_tmul T M c' i j n l (j+l) q h' h rfl] at eq
      exact eq
    exact LinearMap.congr_fun hh x

set_option linter.checkUnivs false in
private abbrev resolutionFunctor (h : HomotopyCategoryLaws A) : D A h ⥤ K A :=
  (kProjectiveLocalizationEquivalence.{u,max v z,w} A h).inverse ⋙ (kProjectiveObjects A).ι

private def resolutionIso (h : HomotopyCategoryLaws A) :
    resolutionFunctor.{u,v,w,z} h ⋙ Q A h ≅ 𝟭 (D A h) :=
  (kProjectiveLocalizationEquivalence.{u,max v z,w} A h).counitIso

private theorem resolution_projective (h : HomotopyCategoryLaws A) (X : D A h) :
    IsKProjective ((resolutionFunctor.{u,v,w,z} h).obj X) :=
  ((kProjectiveLocalizationEquivalence.{u,max v z,w} A h).inverse.obj X).property

set_option backward.isDefEq.respectTransparency false in
private def resolutionAdjunction (h : HomotopyCategoryLaws A) :
    resolutionFunctor.{u,v,w,z} h ⊣ Q A h := by
  let J := resolutionFunctor.{u,v,w,z} h
  let α := resolutionIso.{u,v,w,z} h
  let eqv (X : D A h) (N : K A) : (J.obj X ⟶ N) ≃ (X ⟶ (Q A h).obj N) :=
    (Equiv.ofBijective ((Q A h).map : (J.obj X ⟶ N) → _)
      (IsKProjective.localizationMap_bijective (resolution_projective.{u,v,w,z} h X))).trans
      (α.app X).homFromEquiv
  refine Adjunction.mkOfHomEquiv ⟨eqv, ?_, ?_⟩
  · intro X' X N f g
    apply (eqv X' N).injective
    rw [Equiv.apply_symm_apply]
    change f ≫ g =
      α.inv.app X' ≫ (Q A h).map (J.map f ≫ (eqv X N).symm g)
    rw [Functor.map_comp, ← Category.assoc]
    have hn : f ≫ α.inv.app X = α.inv.app X' ≫ (Q A h).map (J.map f) :=
      α.inv.naturality f
    rw [← hn, Category.assoc]
    exact congrArg (f ≫ ·) ((eqv X N).apply_symm_apply g).symm
  · intro X N N' f g
    change α.inv.app X ≫ (Q A h).map (f ≫ g) =
      (α.inv.app X ≫ (Q A h).map f) ≫ (Q A h).map g
    rw [Functor.map_comp, Category.assoc]

private theorem resolutionCounitOnProjective (h : HomotopyCategoryLaws A)
    (P : (kProjectiveObjects A).FullSubcategory) :
    (resolutionAdjunction.{u,v,w,z} h).counit.app P.obj =
      (kProjectiveObjects A).ι.map
        ((kProjectiveLocalizationEquivalence.{u,max v z,w} A h).unitInv.app P) := by
  let QA := Q A h
  let eqv := kProjectiveLocalizationEquivalence.{u,max v z,w} A h
  let adj := resolutionAdjunction.{u,v,w,z} h
  have hε := (adj.homEquiv (QA.obj P.obj) P.obj).apply_symm_apply (𝟙 (QA.obj P.obj))
  rw [Adjunction.homEquiv_counit, (resolutionFunctor.{u,v,w,z} h).map_id,
    Category.id_comp] at hε
  simp only [adj, resolutionAdjunction, Adjunction.mkOfHomEquiv_homEquiv] at hε
  change (resolutionIso.{u,v,w,z} h).inv.app (QA.obj P.obj) ≫
    QA.map (adj.counit.app P.obj) = 𝟙 _ at hε
  apply (IsKProjective.localizationMap_bijective (resolution_projective.{u,v,w,z} h _)).1
  change QA.map (adj.counit.app P.obj) = eqv.functor.map (eqv.unitInv.app P)
  rw [← eqv.counit_app_functor]
  apply (cancel_epi ((resolutionIso.{u,v,w,z} h).inv.app (QA.obj P.obj))).mp
  exact hε.trans (eqv.counitIso.inv_hom_id_app (QA.obj P.obj)).symm

private def localizeAdjunctionTarget
    {C K' D' : Type*} [Category* C] [Category* K'] [Category* D']
    {F : C ⥤ K'} {H : K' ⥤ C} (a : F ⊣ H)
    (Q' : K' ⥤ D') (W : MorphismProperty K') [Q'.IsLocalization W]
    (H' : D' ⥤ C) (e : Q' ⋙ H' ≅ H) : F ⋙ Q' ⊣ H' := by
  letI : CatCommSq F (𝟭 C) Q' (F ⋙ Q') := ⟨(F ⋙ Q').leftUnitor.symm⟩
  letI : CatCommSq H Q' (𝟭 C) H' := ⟨H.rightUnitor ≪≫ e.symm⟩
  exact a.localization (𝟭 C) (MorphismProperty.isomorphisms C) Q' W (F ⋙ Q') H'

set_option backward.isDefEq.respectTransparency false in
private theorem localizeAdjunctionTarget_unit
    {C K' D' : Type*} [Category* C] [Category* K'] [Category* D']
    {F : C ⥤ K'} {H : K' ⥤ C} (a : F ⊣ H)
    (Q' : K' ⥤ D') (W : MorphismProperty K') [Q'.IsLocalization W]
    (H' : D' ⥤ C) (e : Q' ⋙ H' ≅ H) (X : C) :
    (localizeAdjunctionTarget a Q' W H' e).unit.app X =
      a.unit.app X ≫ e.inv.app (F.obj X) := by
  letI : CatCommSq F (𝟭 C) Q' (F ⋙ Q') := ⟨(F ⋙ Q').leftUnitor.symm⟩
  letI : CatCommSq H Q' (𝟭 C) H' := ⟨H.rightUnitor ≪≫ e.symm⟩
  have h := a.localization_unit_app (𝟭 C) (MorphismProperty.isomorphisms C) Q' W (F ⋙ Q') H' X
  change (localizeAdjunctionTarget a Q' W H' e).unit.app X =
    a.unit.app X ≫ (H.rightUnitor ≪≫ e.symm).hom.app (F.obj X) ≫
      H'.map ((F ⋙ Q').leftUnitor.symm.hom.app X) at h
  simpa using h

set_option backward.isDefEq.respectTransparency false in
private theorem localizeAdjunctionTarget_counit
    {C K' D' : Type*} [Category* C] [Category* K'] [Category* D']
    {F : C ⥤ K'} {H : K' ⥤ C} (a : F ⊣ H)
    (Q' : K' ⥤ D') (W : MorphismProperty K') [Q'.IsLocalization W]
    (H' : D' ⥤ C) (e : Q' ⋙ H' ≅ H) (Y : K') :
    (localizeAdjunctionTarget a Q' W H' e).counit.app (Q'.obj Y) =
      (F ⋙ Q').map (e.hom.app Y) ≫ Q'.map (a.counit.app Y) := by
  simp [localizeAdjunctionTarget, CatCommSq.iso]

open private representable_kProjective from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeKProjective

include E adj laws in
private theorem buildDerivedAdjunction (hT : ∀ a, IsKProjective (T.obj a)) :
    ∀ (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B),
      ∃ d : DerivedAdjunctionData.{u,v,w,z} L G hA hB,
        d.Realizes adj ∧ d.ComputesRepresentatives := by
  intro hA hB
  let F := ordinaryTensor.{u,v,w,z} L
  let H := ordinaryHom.{u,v,w,z} G
  let FH := onHomotopy F (tensor_respects_homotopy E adj laws)
  let dG := descend H hB hA (hom_respects_homotopy E adj laws)
    (fun f hf a => nativeHomPreserves G f hT hf a)
  let J := resolutionFunctor.{u,v,w,z} hA
  let QA := Q A hA
  let QB := Q B hB
  let FD := (J ⋙ FH) ⋙ QB
  let GH : K B ⥤ K A := dG.homotopy
  let GD : D B hB ⥤ D A hA := dG.derived
  let rAdj : J ⊣ QA := resolutionAdjunction.{u,v,w,z} hA
  let hAdj : FH ⊣ GH := homotopyAdjunction E adj laws
  let a₀ : J ⋙ FH ⊣ GH ⋙ QA := rAdj.comp hAdj
  let eG : QB ⋙ GD ≅ GH ⋙ QA := dG.square
  let aD : FD ⊣ GD :=
    localizeAdjunctionTarget a₀ (Q B hB) (quasiIsomorphisms B) GD eG
  let R := kProjectiveLocalizationEquivalence.{u,max v z,w} A hA
  let s : (kProjectiveObjects A).ι ⋙ QA ⋙ FD ≅
      (kProjectiveObjects A).ι ⋙ FH ⋙ QB :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (Functor.isoWhiskerRight R.unitIso.symm
      (kProjectiveObjects A).ι) FH) QB
  letI := derivedCategoryInstance B hB
  refine ⟨⟨FH, dG, J, rAdj, hAdj, aD, fun _ => rfl, s⟩,
    ⟨resolution_projective.{u,v,w,z} hA, ?_, fun _ => HEq.rfl, fun _ => HEq.rfl, ?_, ?_, ?_⟩,
    ?_, ?_⟩
  · intro X Y f
    exact heq_of_eq (onHomotopy_map F (tensor_respects_homotopy E adj laws) f)
  · intro X
    change aD.unit.app X = rAdj.unit.app X ≫ QA.map (hAdj.unit.app (J.obj X)) ≫ eG.inv.app _
    refine (localizeAdjunctionTarget_unit a₀ QB (quasiIsomorphisms B) GD eG
      (X : D A hA)).trans ?_
    have h := Adjunction.comp_unit_app rAdj hAdj (X : D A hA)
    exact (congrArg (fun η => η ≫ eG.inv.app (FH.obj (J.obj X))) h).trans
      (Category.assoc _ _ _)
  · intro Y
    change aD.counit.app (QB.obj Y) = FD.map (eG.hom.app Y) ≫
      QB.map (FH.map (rAdj.counit.app (GH.obj Y))) ≫ QB.map (hAdj.counit.app Y)
    rw [localizeAdjunctionTarget_counit a₀ QB (quasiIsomorphisms B) GD eG,
      Adjunction.comp_counit_app, QB.map_comp]
  · intro a
    exact ⟨s.app ⟨representable a, representable_kProjective a⟩ ≪≫
      QB.mapIso ((toHomotopyCategory B).mapIso (representableTensorIso.{u,v,w,z} L a))⟩
  · intro P hp
    change QB.map (FH.map ((kProjectiveObjects A).ι.map (R.unitInv.app ⟨P, hp⟩))) =
      QB.map (FH.map (rAdj.counit.app P))
    rw [resolutionCounitOnProjective.{u,v,w,z} hA ⟨P, hp⟩]
    rfl
  · intro a
    refine ⟨representableTensorIso.{u,v,w,z} L a, ?_, ?_⟩
    · intro b c i j n he f x
      change representableEquiv T a b n ((L.degree (representable a) b n).symm
        (L.degree (representable a) b n (tmul T (representable a) b c i j n he f x))) = _
      rw [LinearEquiv.symm_apply_apply, representableEquiv_apply]
    · intro b n x
      change L.degree (representable a) b n ((representableEquiv T a b n).symm x) = _
      rw [representableEquiv_symm_apply]

theorem derivedAdjunctionAt : DerivedAdjunctionAt.{u,v,w,z} := by
  intro k _ A B T L G E adj laws hT hA hB
  obtain ⟨d, hd, _⟩ := buildDerivedAdjunction.{u,v,w,z} E adj laws hT hA hB
  exact ⟨d, hd⟩

end DerivedAdjunction

section CommonBound

open Specs.DerivedFormalization.DG.AmbientDerived (category strictInput)
open Specs.DerivedFormalization.DG.DerivedCoefficientLift (strictTransition)
open DG.DerivedCoefficientLift (kProjectiveCoefficientTransition
  derivedCoefficientTransitionOnInputs nativeDerivedCoefficientTransition)

theorem ambientDerivedAdjunction : AmbientDerivedAdjunction.{u,v,w,vA,z,t} := by
  intro k _ A B T
  obtain ⟨S, K, L, G, E, L', G', E', adj, D, laws, _, hex, _, _⟩ :=
    ambientAdjunction.{u,v,w,z,vA,t} A B T
  refine ⟨S, K, L', G', E', adj, laws, hex, ?_⟩
  intro hT hA hB
  obtain ⟨d, hd, _⟩ := buildDerivedAdjunction.{u,max vA v t,w,z} E' adj hex hT hA hB
  exact ⟨d, hd⟩


open private kProjective_of_homotopyRetract from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift

theorem ambientProjectivityTransition : AmbientProjectivityTransition.{u,v,w,vA,z,t,s} := by
  intro k _ A B T hT a
  let C := category.{u,v,z,max vA w t} B
  let C' := category.{u,v,z,max vA w t s} B
  let P := (strictInput.{u,v,z,max vA w t} B).obj (T.obj a)
  have hP : IsKProjective ((strictTransition.{u,v,z,max vA w t,s} B).obj P) :=
    kProjectiveCoefficientTransition.{u,v,z,max vA w t,s} B P (hT a)
  obtain ⟨alpha, _, _⟩ := derivedCoefficientTransitionOnInputs.{u,v,z,max vA w t,s} B
    ⟨instCategoryK B, rfl⟩ ⟨instCategoryK C, rfl⟩ ⟨instCategoryK C', rfl⟩
  let e := alpha.app (T.obj a)
  exact kProjective_of_homotopyRetract e.hom e.inv hP
    (congrArg (fun g => homotopyClass g) e.inv_hom_id)

theorem adequateNativeProjectivityTransition : AdequateNativeProjectivityTransition.{u,v,w,vA,z,t} := by
  intro k _ A B T hT a
  let C := category.{u,max v z,z,max vA w t} B
  exact (nativeDerivedCoefficientTransition.{u,v,z,max vA w z t} B
    ⟨instCategoryK B, rfl⟩ ⟨instCategoryK C, rfl⟩).2 (T.obj a) (hT a)

end CommonBound

section TargetShift

open CochainComplex.HomComplex

variable {B : DGCategory.{u,v,z} k} {P N : RightDGModule B}

/-- Shifting only the target reindexes the degrees and leaves each component
map unchanged, using the same right action at the reindexed degree. -/
private def shiftTargetDegrees (s t r : ℤ) (e : r+s=t) :
    GradedHom P N t ≃ₗ[k] GradedHom P (shift N s) r where
  toFun f := ⟨fun a => (f.val a).rightShift s r e, by
    intro a b i j n ir nr h hi hn x y
    change ((f.val a).rightShift s r e).v n nr hn (P.act i j n h x y) =
      N.act (ir+s) j (nr+s) _ (((f.val b).rightShift s r e).v i ir hi x) y
    rw [Cochain.rightShift_v _ s r e n nr hn (nr+s) (by omega),
      Cochain.rightShift_v _ s r e i ir hi (ir+s) (by omega)]
    simp only [CochainComplex.shiftFunctorObjXIso, XIsoOfEq, eqToIso_refl, Iso.refl_inv,
      Category.comp_id]
    exact f.comm_act i j n (ir+s) (nr+s) h (by omega) (by omega) x y⟩
  invFun f := ⟨fun a => (f.val a).rightUnshift t e, by
    intro a b i j n ir nr h hi hn x y
    obtain ⟨ir, rfl⟩ : ∃ p : ℤ, p+s=ir := ⟨ir-s, by omega⟩
    obtain ⟨nr, rfl⟩ : ∃ p : ℤ, p+s=nr := ⟨nr-s, by omega⟩
    change ((f.val a).rightUnshift t e).v n (nr+s) hn (P.act i j n h x y) =
      (shift N s).act ir j nr (by omega) (((f.val b).rightUnshift t e).v i (ir+s) hi x) y
    rw [Cochain.rightUnshift_v _ t e n (nr+s) hn nr (by omega),
      Cochain.rightUnshift_v _ t e i (ir+s) hi ir (by omega)]
    simp only [CochainComplex.shiftFunctorObjXIso, XIsoOfEq, eqToIso_refl, Iso.refl_hom]
    exact f.comm_act i j n ir nr h (by omega) (by omega) x y⟩
  left_inv f := Subtype.ext (funext fun a => Cochain.rightUnshift_rightShift (f.val a) s r e)
  right_inv f := Subtype.ext (funext fun a => Cochain.rightShift_rightUnshift (f.val a) t e)
  map_add' f g := Subtype.ext (funext fun a =>
    Cochain.rightShift_add (f.val a) (g.val a) s r e)
  map_smul' c f := Subtype.ext (funext fun a => Cochain.rightShift_smul (f.val a) s r e c)

private theorem shiftTargetDegrees_app (s t r : ℤ) (e : r+s=t)
    (f : GradedHom P N t) (a : B.Obj) (i j : ℤ) (h : i+r=j) :
    (shiftTargetDegrees s t r e f).app a i j h = f.app a i (j+s) (by omega) := by
  change ((f.val a).rightShift s r e).v i j h = _
  rw [Cochain.rightShift_v _ s r e i j h (j+s) (by omega)]
  simp only [CochainComplex.shiftFunctorObjXIso, XIsoOfEq, eqToIso_refl, Iso.refl_inv,
    Category.comp_id]

private theorem shiftTargetDegrees_d (s t r : ℤ) (e : r+s=t) (f : GradedHom P N t) :
    (homComplex P (shift N s)).d r (r+1) (shiftTargetDegrees s t r e f) =
      s.negOnePow • shiftTargetDegrees s (t+1) (r+1) (by omega) ((homComplex P N).d t (t+1) f) :=
  Subtype.ext (funext fun a => Cochain.δ_rightShift (f.val a) s r (r+1) e (t+1) (by omega))

end TargetShift

section HomShift

open private gradedHom_ext_apply from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveClosure

variable {A : DGCategory.{u,max v w z,w} k} {B : DGCategory.{u,max v w z,z} k}
variable {T : DGBimodule A B} (G : InternalHomModel T)

private abbrev homDegree (N : RightDGModule B) (a : A.Obj) (n : ℤ) :
    GradedHom (T.obj a) N n ≃ₗ[k] ((G.functor.obj N).complex a).X n :=
  ((HomologicalComplex.eval _ _ n).mapIso (G.objectwise N a)).toLinearEquiv

private def homShiftDegree (N : RightDGModule B) (s : ℤ) (a : A.Obj) (r : ℤ) :
    ((shift ((ordinaryHom.{u,v,w,z} G).obj N) s).complex a).X r ≃ₗ[k] (((ordinaryHom.{u,v,w,z} G).obj (shift N s)).complex a).X r :=
  (homDegree.{u,v,w,z} G N a (r+s)).symm.trans
    ((shiftTargetDegrees s (r+s) r rfl).trans (homDegree.{u,v,w,z} G (shift N s) a r))

private theorem homShiftDegree_eval (N : RightDGModule B) (s : ℤ) (a : A.Obj) (r : ℤ)
    (f : GradedHom (T.obj a) N (r+s)) :
    homShiftDegree.{u,v,w,z} G N s a r ((G.objectwise N a).hom.f (r+s) f) =
      (G.objectwise (shift N s) a).hom.f r (shiftTargetDegrees s (r+s) r rfl f) := by
  change homShiftDegree.{u,v,w,z} G N s a r (homDegree.{u,v,w,z} G N a (r+s) f) = _
  simp only [homShiftDegree, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

universe c

private theorem complexMap_comm_apply {C D : ModuleCochain.{u,c} k}
    (f : C ⟶ D) (i j : ℤ) (x : C.X i) :
    D.d i j (f.f i x) = f.f j (C.d i j x) :=
  congrArg (fun g : C.X i ⟶ D.X j => g x) (f.comm i j)

set_option backward.isDefEq.respectTransparency false in
private def homShiftIso (N : RightDGModule B) (s : ℤ) : shift ((ordinaryHom.{u,v,w,z} G).obj N) s ≅ (ordinaryHom.{u,v,w,z} G).obj (shift N s) :=
  DG.CoefficientLift.isoOfComponents (homShiftDegree.{u,v,w,z} G N s)
    (by
      intro a r x
      obtain ⟨f, rfl⟩ := (homDegree.{u,v,w,z} G N a (r+s)).surjective x
      change homShiftDegree.{u,v,w,z} G N s a (r+1)
          (s.negOnePow • ((G.functor.obj N).complex a).d (r+s) (r+1+s)
            ((G.objectwise N a).hom.f (r+s) f)) =
        ((G.functor.obj (shift N s)).complex a).d r (r+1)
          (homShiftDegree.{u,v,w,z} G N s a r ((G.objectwise N a).hom.f (r+s) f))
      have d : (homComplex (T.obj a) (shift N s)).d r (r+1) (shiftTargetDegrees s (r+s) r rfl f) =
          s.negOnePow • shiftTargetDegrees s (r+1+s) (r+1) rfl
            ((homComplex (T.obj a) N).d (r+s) (r+1+s) f) := by
        have e (q : ℤ) (hq : q=r+1+s) (hq' : q=r+s+1) :
            (homComplex (T.obj a) (shift N s)).d r (r+1) (shiftTargetDegrees s (r+s) r rfl f) =
              s.negOnePow • shiftTargetDegrees s q (r+1) hq.symm
                ((homComplex (T.obj a) N).d (r+s) q f) := by
          subst hq'
          exact shiftTargetDegrees_d s (r+s) r rfl f
        exact e _ rfl (by omega)
      simp only [Units.smul_def, map_zsmul]
      rw [complexMap_comm_apply.{u,max v w z} (G.objectwise N a).hom, homShiftDegree_eval,
        homShiftDegree_eval, complexMap_comm_apply.{u,max v w z} (G.objectwise (shift N s) a).hom]
      have h := congrArg (fun g => (G.objectwise (shift N s) a).hom.f (r+1) g) d
      simpa only [Units.smul_def, map_zsmul] using h.symm)
    (by
      intro a b i j n h x f
      obtain ⟨g, rfl⟩ := (homDegree.{u,v,w,z} G N b (i+s)).surjective x
      change homShiftDegree.{u,v,w,z} G N s a n
          ((G.functor.obj N).act (i+s) j (n+s) (by omega)
            ((G.objectwise N b).hom.f (i+s) g) f) =
        (G.functor.obj (shift N s)).act i j n h
          (homShiftDegree.{u,v,w,z} G N s b i ((G.objectwise N b).hom.f (i+s) g)) f
      rw [G.action, homShiftDegree_eval, homShiftDegree_eval, G.action]
      apply congrArg (fun g => (G.objectwise (shift N s) a).hom.f n g)
      apply gradedHom_ext_apply
      intro c p q e x
      rw [shiftTargetDegrees_app]
      let a' : GradedHom (T.obj a) (T.obj b) j := (T.map a b).f j f
      let x' := a'.app c p (p+j) rfl x
      calc
        _ = GradedHom.app g c (p+j) (q+s) (by omega) x' :=
          compositionFormula (i+s) j (n+s) (by omega) g a' c p (p+j) (q+s) rfl (by omega) x
        _ = (shiftTargetDegrees s (i+s) i rfl g).app c (p+j) q (by omega) x' :=
          congrArg (fun m : ((T.obj b).complex c).X (p+j) ⟶ (N.complex c).X (q+s) => m x') (shiftTargetDegrees_app s (i+s) i rfl g c (p+j) q (by omega)).symm
        _ = _ := (compositionFormula i j n h _ a' c p (p+j) q rfl (by omega) x).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem homShiftIso_natural {N N' : RightDGModule B} (f : N ⟶ N') (s : ℤ) :
    shiftMap s ((ordinaryHom.{u,v,w,z} G).map f) ≫ (homShiftIso.{u,v,w,z} G N' s).hom =
      (homShiftIso.{u,v,w,z} G N s).hom ≫ (ordinaryHom.{u,v,w,z} G).map (shiftMap s f) := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨g, rfl⟩ := (homDegree.{u,v,w,z} G N a (r+s)).surjective x
  change homShiftDegree.{u,v,w,z} G N' s a r
      (((G.functor.map f).app a).f (r+s) ((G.objectwise N a).hom.f (r+s) g)) =
    ((G.functor.map (shiftMap s f)).app a).f r
      (homShiftDegree.{u,v,w,z} G N s a r ((G.objectwise N a).hom.f (r+s) g))
  rw [G.map, homShiftDegree_eval, homShiftDegree_eval, G.map]
  apply congrArg (fun g => (G.objectwise (shift N' s) a).hom.f r g)
  apply gradedHom_ext_apply
  intro b i j e x
  change (shiftTargetDegrees s (r+s) r rfl ((homComplexMap (T.obj a) f).f (r+s) g)).app b i j e x =
    GradedHom.app ((homComplexMap (T.obj a) (shiftMap s f)).f r
      (shiftTargetDegrees s (r+s) r rfl g)) b i j e x
  rw [shiftTargetDegrees_app]
  calc
    _ = (f.app b).f (j+s) (g.app b i (j+s) (by omega) x) :=
      homComplexMap_app f g b i (j+s) (by omega) x
    _ = ((shiftMap s f).app b).f j ((shiftTargetDegrees s (r+s) r rfl g).app b i j e x) := by
      rw [shiftTargetDegrees_app]
      rfl
    _ = _ := (homComplexMap_app (shiftMap s f) _ b i j e x).symm

end HomShift

section HomCone

open private coneHomTarget coneHomTarget_app coneHomSource coneHomSource_app coneHomPair
  coneHomTarget_pair coneHomSource_pair coneHomTarget_d coneHomSource_d coneHom_ext
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveInvariance
open private gradedHom_ext_apply from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveClosure

variable {A : DGCategory.{u,max v w z,w} k} {B : DGCategory.{u,max v w z,z} k}
variable {T : DGBimodule A B} (G : InternalHomModel T)
variable {M N P : RightDGModule B} (f : M ⟶ N)

set_option linter.checkUnivs false in
private def coneHomDegrees (P : RightDGModule B) (r : ℤ) :
    GradedHom P (cone f) r ≃ₗ[k] (GradedHom P N r × GradedHom P M (r+1)) where
  toFun g := (coneHomTarget f r g, coneHomSource f r g)
  invFun p := coneHomPair f p.1 p.2
  left_inv _ := coneHom_ext f (coneHomTarget_pair f _ _) (coneHomSource_pair f _ _)
  right_inv _ := Prod.ext (coneHomTarget_pair f _ _) (coneHomSource_pair f _ _)
  map_add' x y := Prod.ext (map_add (coneHomTarget f r) x y) (map_add (coneHomSource f r) x y)
  map_smul' c x := Prod.ext (map_smul (coneHomTarget f r) c x) (map_smul (coneHomSource f r) c x)

private def homConeDegree (a : A.Obj) (r : ℤ) :
    (((ordinaryHom.{u,v,w,z} G).obj (cone f)).complex a).X r ≃ₗ[k]
      ((cone ((ordinaryHom.{u,v,w,z} G).map f)).complex a).X r :=
  (homDegree.{u,v,w,z} G (cone f) a r).symm.trans <|
    (coneHomDegrees.{u,v,w,z} f (T.obj a) r).trans <|
      (homDegree.{u,v,w,z} G N a r).prodCongr (homDegree.{u,v,w,z} G M a (r+1))

private theorem homConeDegree_eval (a : A.Obj) (r : ℤ)
    (g : GradedHom (T.obj a) (cone f) r) :
    homConeDegree.{u,v,w,z} G f a r ((G.objectwise (cone f) a).hom.f r g) =
      ((G.objectwise N a).hom.f r (coneHomTarget f r g),
        (G.objectwise M a).hom.f (r+1) (coneHomSource f r g)) := by
  change homConeDegree.{u,v,w,z} G f a r (homDegree.{u,v,w,z} G (cone f) a r g) = _
  simp only [homConeDegree, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def homConeIso :
    (ordinaryHom.{u,v,w,z} G).obj (cone f) ≅ cone ((ordinaryHom.{u,v,w,z} G).map f) :=
  DG.CoefficientLift.isoOfComponents (homConeDegree.{u,v,w,z} G f)
    (by
      intro a r x
      obtain ⟨g, rfl⟩ := (homDegree.{u,v,w,z} G (cone f) a r).surjective x
      change homConeDegree.{u,v,w,z} G f a (r+1)
            (((G.functor.obj (cone f)).complex a).d r (r+1) ((G.objectwise (cone f) a).hom.f r g)) =
        ((cone ((ordinaryHom.{u,v,w,z} G).map f)).complex a).d r (r+1)
          (homConeDegree.{u,v,w,z} G f a r ((G.objectwise (cone f) a).hom.f r g))
      rw [complexMap_comm_apply.{u,max v w z}, homConeDegree_eval, homConeDegree_eval,
        cone_d, coneHomTarget_d, coneHomSource_d]
      apply Prod.ext
      · change (G.objectwise N a).hom.f (r+1)
            ((homComplex (T.obj a) N).d r (r+1) (coneHomTarget f r g) +
              (homComplexMap (T.obj a) f).f (r+1) (coneHomSource f r g)) =
          ((G.functor.obj N).complex a).d r (r+1) ((G.objectwise N a).hom.f r (coneHomTarget f r g)) +
            ((G.functor.map f).app a).f (r+1) ((G.objectwise M a).hom.f (r+1) (coneHomSource f r g))
        rw [map_add, complexMap_comm_apply.{u,max v w z}, G.map]
        rfl
      · change (G.objectwise M a).hom.f (r+1+1)
            (-(homComplex (T.obj a) M).d (r+1) (r+1+1) (coneHomSource f r g)) =
          -((G.functor.obj M).complex a).d (r+1) (r+1+1)
              ((G.objectwise M a).hom.f (r+1) (coneHomSource f r g))
        rw [map_neg, complexMap_comm_apply.{u,max v w z}])
    (by
      intro a b i j n h x u'
      obtain ⟨g, rfl⟩ := (homDegree.{u,v,w,z} G (cone f) b i).surjective x
      change homConeDegree.{u,v,w,z} G f a n ((G.functor.obj (cone f)).act i j n h
          ((G.objectwise (cone f) b).hom.f i g) u') =
        ((G.functor.obj N).act i j n h
            (homConeDegree.{u,v,w,z} G f b i ((G.objectwise (cone f) b).hom.f i g)).1 u',
          (G.functor.obj M).act (i+1) j (n+1) (by omega)
            (homConeDegree.{u,v,w,z} G f b i ((G.objectwise (cone f) b).hom.f i g)).2 u')
      rw [G.action, homConeDegree_eval, homConeDegree_eval, G.action, G.action]
      apply Prod.ext
      · apply congrArg (fun g => (G.objectwise N a).hom.f n g)
        apply gradedHom_ext_apply
        intro c p q e x
        rw [coneHomTarget_app,
          compositionFormula i j n _ g _ c p (p+j) q rfl (by omega),
          compositionFormula i j n _ _ _ c p (p+j) q rfl (by omega), coneHomTarget_app]
      · apply congrArg (fun g => (G.objectwise M a).hom.f (n+1) g)
        apply gradedHom_ext_apply
        intro c p q e x
        obtain ⟨q, rfl⟩ : ∃ q' : ℤ, q'+1=q := ⟨q-1, by omega⟩
        rw [coneHomSource_app f _ c p q (by omega),
          compositionFormula i j n _ g _ c p (p+j) q rfl (by omega),
          compositionFormula (i+1) j (n+1) _ _ _ c p (p+j) (q+1) rfl (by omega),
          coneHomSource_app])

set_option backward.isDefEq.respectTransparency false in
private theorem homConeIso_inclusion :
    (ordinaryHom.{u,v,w,z} G).map (coneInclusion f) ≫ (homConeIso.{u,v,w,z} G f).hom =
      coneInclusion ((ordinaryHom.{u,v,w,z} G).map f) := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨g, rfl⟩ := (homDegree.{u,v,w,z} G N a r).surjective x
  let g' : GradedHom (T.obj a) (cone f) r := (homComplexMap (T.obj a) (coneInclusion f)).f r g
  change homConeDegree.{u,v,w,z} G f a r
      (((G.functor.map (coneInclusion f)).app a).f r ((G.objectwise N a).hom.f r g)) =
    ((G.objectwise N a).hom.f r g, 0)
  rw [G.map, homConeDegree_eval]
  apply Prod.ext
  · apply congrArg (fun z => (G.objectwise N a).hom.f r z)
    change coneHomTarget f r g' = g
    apply gradedHom_ext_apply
    intro b i j e y
    rw [coneHomTarget_app]
    exact congrArg Prod.fst (homComplexMap_app (coneInclusion f) g b i j e y)
  · have e : coneHomSource f r g' = 0 := by
      apply gradedHom_ext_apply
      intro b i j e y
      obtain ⟨j, rfl⟩ : ∃ q : ℤ, q+1=j := ⟨j-1, by omega⟩
      rw [coneHomSource_app f _ b i j (by omega)]
      exact congrArg Prod.snd (homComplexMap_app (coneInclusion f) g b i j (by omega) y)
    change (G.objectwise M a).hom.f (r+1) (coneHomSource f r g') = 0
    rw [e, map_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem homConeIso_projection :
    (homConeIso.{u,v,w,z} G f).hom ≫ coneProjection ((ordinaryHom.{u,v,w,z} G).map f) ≫
      (homShiftIso.{u,v,w,z} G M 1).hom =
        (ordinaryHom.{u,v,w,z} G).map (coneProjection f) := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨g, rfl⟩ := (homDegree.{u,v,w,z} G (cone f) a r).surjective x
  change homShiftDegree.{u,v,w,z} G M 1 a r
      (homConeDegree.{u,v,w,z} G f a r ((G.objectwise (cone f) a).hom.f r g)).2 =
    ((G.functor.map (coneProjection f)).app a).f r ((G.objectwise (cone f) a).hom.f r g)
  rw [homConeDegree_eval, homShiftDegree_eval, G.map]
  apply congrArg (fun z => (G.objectwise (shift M 1) a).hom.f r z)
  apply gradedHom_ext_apply
  intro b i j e y
  rw [shiftTargetDegrees_app]
  change (coneHomSource f r g).app b i (j+1) (by omega) y =
    GradedHom.app ((homComplexMap (T.obj a) (coneProjection f)).f r g) b i j e y
  rw [coneHomSource_app]
  exact (homComplexMap_app (coneProjection f) g b i j e y).symm

theorem homShiftConeComparison : HomShiftConeComparison.{u,v,w,z} := by
  intro k _ A B T G
  refine ⟨homShiftIso.{u,v,w,z} G, fun f => homConeIso.{u,v,w,z} G f, ?_, ?_, ?_⟩
  · intro N s a r g b i j h
    have cancel (x : GradedHom (T.obj a) (shift N s) r) :
        (G.objectwise (shift N s) a).inv.f r ((G.objectwise (shift N s) a).hom.f r x) = x :=
      isoComponent_cancel (G.objectwise (shift N s) a).symm r x
    change GradedHom.app ((G.objectwise (shift N s) a).inv.f r
      (homShiftDegree.{u,v,w,z} G N s a r ((G.objectwise N a).hom.f (r+s) g))) b i j h = _
    rw [homShiftDegree_eval, cancel]
    exact shiftTargetDegrees_app s (r+s) r rfl g b i j h
  · intro N N' f s
    exact homShiftIso_natural.{u,v,w,z} G f s
  · intro M N f
    exact ⟨homConeIso_inclusion.{u,v,w,z} G f, homConeIso_projection.{u,v,w,z} G f⟩


private def homComparisons : ShiftConeComparisons (ordinaryHom.{u,v,w,z} G) where
  shiftIso N s := (homShiftIso.{u,v,w,z} G N s).symm
  coneIso f := homConeIso.{u,v,w,z} G f
  shiftNaturality := by
    intro M N f s
    apply (cancel_mono (homShiftIso.{u,v,w,z} G N s).hom).mp
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      homShiftIso_natural.{u,v,w,z} G f s, Iso.inv_hom_id_assoc]
  inclusion f := homConeIso_inclusion.{u,v,w,z} G f
  projection {M N} f := (homShiftIso.{u,v,w,z} G M 1).comp_inv_eq.mpr
    (homConeIso_projection.{u,v,w,z} G f).symm

private theorem homComparisonsLaws :
    HomComparisonLaws.{u,v,w,z} (homComparisons.{u,v,w,z} G) := by
  constructor
  · intro N s a r g b i j h
    have cancel (x : GradedHom (T.obj a) (shift N s) r) :
        (G.objectwise (shift N s) a).inv.f r ((G.objectwise (shift N s) a).hom.f r x) = x :=
      isoComponent_cancel (G.objectwise (shift N s) a).symm r x
    change GradedHom.app ((G.objectwise (shift N s) a).inv.f r
      (homShiftDegree.{u,v,w,z} G N s a r ((G.objectwise N a).hom.f (r+s) g))) b i j h = _
    rw [homShiftDegree_eval, cancel]
    exact shiftTargetDegrees_app s (r+s) r rfl g b i j h
  · intro M N f a r g b i j h x
    have cancelN (y : GradedHom (T.obj a) N r) :
        (G.objectwise N a).inv.f r ((G.objectwise N a).hom.f r y) = y :=
      isoComponent_cancel (G.objectwise N a).symm r y
    have cancelM (y : GradedHom (T.obj a) M (r+1)) :
        (G.objectwise M a).inv.f (r+1) ((G.objectwise M a).hom.f (r+1) y) = y :=
      isoComponent_cancel (G.objectwise M a).symm (r+1) y
    change
      GradedHom.app ((G.objectwise N a).inv.f r
        (homConeDegree.{u,v,w,z} G f a r ((G.objectwise (cone f) a).hom.f r g)).1)
        b i j h x = (GradedHom.app g b i j h x).1 ∧
      GradedHom.app ((G.objectwise M a).inv.f (r+1)
        (homConeDegree.{u,v,w,z} G f a r ((G.objectwise (cone f) a).hom.f r g)).2)
        b i (j+1) (by omega) x = (GradedHom.app g b i j h x).2
    rw [homConeDegree_eval, cancelN, cancelM]
    exact ⟨coneHomTarget_app f g b i j h x, coneHomSource_app f g b i j h x⟩

end HomCone

section Exactness

open Specs.DerivedFormalization.DG.LocalizedBimoduleExactness (DescentData)
open private commute_heq from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleCoefficientCompatibility

universe v' w'

local instance (C : DGCategory.{u,v',w'} k) :
    Category (Specs.DerivedFormalization.DG.HomComplex.homotopyCategory C) :=
  inferInstanceAs (Category (K C))

private abbrev asExactComparisons
    {A : DGCategory.{u,vA,w} k} {B : DGCategory.{u,v,z} k}
    {F : RightDGModule A ⥤ RightDGModule B} (S : ShiftConeComparisons F) :
    Specs.DerivedFormalization.DG.LocalizedBimoduleExactness.ShiftConeComparisons F :=
  ⟨S.shiftIso, S.coneIso, S.shiftNaturality, S.inclusion, S.projection⟩

private abbrev coneLocalizationOfExactness {A : DGCategory.{u,v,w} k}
    {h : HomotopyCategoryLaws A}
    (c : Specs.DerivedFormalization.DG.LocalizedBimoduleExactness.ConeLocalization A h) :
    ConeLocalization A h :=
  { shiftK := c.shiftK
    addK := c.addK
    zeroK := c.zeroK
    addShiftK := c.addShiftK
    shiftObj := c.shiftObj
    shiftMap := c.shiftMap
    trianglesK := c.trianglesK
    shiftD := c.shiftD
    addD := c.addD
    zeroD := c.zeroD
    addShiftD := c.addShiftD
    quotientShift := c.quotientShift
    trianglesD := c.trianglesD
    isTriangulated := c.isTriangulated
    coneTriangles := c.coneTriangles
    localizedConeTriangles := c.localizedConeTriangles }

variable {A : DGCategory.{u,max v w z,w} k} {B : DGCategory.{u,max v w z,z} k}
variable {T : DGBimodule A B} {L : TensorModel T} {G : InternalHomModel T}
variable {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
variable {adj : ordinaryTensor.{u,v,w,z} L ⊣ ordinaryHom.{u,v,w,z} G}

set_option backward.isDefEq.respectTransparency false in
private abbrev exactnessDescent (d : DerivedAdjunctionData.{u,v,w,z} L G hA hB)
    (hd : d.Realizes adj) :
    DescentData hA hB (ordinaryTensor.{u,v,w,z} L) (ordinaryHom.{u,v,w,z} G) adj := by
  refine
    { FK := ⟨d.tensorH, d.tensorObj, ?_⟩
      HK := ⟨d.hom.homotopy, d.hom.obj, ?_⟩
      aK := d.homotopyAdjunction
      unitK := ?_
      counitK := ?_
      J := d.resolution
      aJ := d.resolutionAdjunction
      projective := hd.1
      HD := d.hom.derived
      b := d.hom.square
      aD := d.adjunction
      unitD := hd.2.2.2.2.1
      counitD := hd.2.2.2.2.2.1 }
  · intro X Y f
    exact commute_heq (d.tensorObj X) (d.tensorObj Y) (hd.2.1 f)
  · intro X Y f
    exact commute_heq (d.hom.obj X) (d.hom.obj Y) (d.hom.map f)
  · intro X
    let e := (congrArg d.hom.homotopy.obj (d.tensorObj X)).trans
      (d.hom.obj ((ordinaryTensor.{u,v,w,z} L).obj X))
    have he := commute_heq (C := K A) rfl e (hd.2.2.1 X)
    change d.homotopyAdjunction.unit.app X ≫ d.hom.homotopy.map (eqToHom (d.tensorObj X)) ≫
      eqToHom (d.hom.obj ((ordinaryTensor.{u,v,w,z} L).obj X)) =
      homotopyClass (adj.unit.app X)
    rw [eqToHom_map, eqToHom_trans]
    simpa only [eqToHom_refl, Category.id_comp] using he
  · intro Y
    let e := (congrArg d.tensorH.obj (d.hom.obj Y)).trans
      (d.tensorObj ((ordinaryHom.{u,v,w,z} G).obj Y))
    have he := commute_heq (C := K B) e rfl (hd.2.2.2.1 Y)
    change d.homotopyAdjunction.counit.app Y = d.tensorH.map (eqToHom (d.hom.obj Y)) ≫
      eqToHom (d.tensorObj ((ordinaryHom.{u,v,w,z} G).obj Y)) ≫ homotopyClass (adj.counit.app Y)
    rw [eqToHom_map, eqToHom_trans_assoc]
    simpa only [eqToHom_refl, Category.comp_id] using he

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
private theorem derivedAdjunctionIsExact (E : OrdinaryCurryFamily.{u,v,w,z} L G)
    (laws : StrictLaws.{u,v,w,z} L G E adj) (hT : ∀ a, IsKProjective (T.obj a))
    (d : DerivedAdjunctionData.{u,v,w,z} L G hA hB)
    (hd : d.Realizes adj) (hc : d.ComputesRepresentatives) : d.IsExact := by
  obtain ⟨S, C, hS, hIn, hPr, hSgen, hCgen⟩ := tensorComparisons.{u,v,w,z} (k := k) A B T L
  let S' : ShiftConeComparisons (ordinaryTensor.{u,v,w,z} L) := ⟨S, C, hS, hIn, hPr⟩
  let R := homComparisons.{u,v,w,z} G
  have hSLaws : TensorComparisonLaws.{u,v,w,z} S' := ⟨hSgen, hCgen⟩
  have hRLaws : HomComparisonLaws.{u,v,w,z} R := homComparisonsLaws.{u,v,w,z} G
  let d' := exactnessDescent.{u,v,w,z} d hd
  obtain ⟨cA, cB, fS, gS, hf, hg, ha, _, hHom, hTensor⟩ :=
    localizedExactness.{u,v,w,z} L G E adj laws hT (asExactComparisons S')
      (asExactComparisons R) hSLaws hRLaws hA hB d'
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  have sameHom (N : RightDGModule B) : (d'.homRepresentative N).hom = (d.onInput N).hom := by
    change d.hom.square.hom.app N ≫ (Q A hA).map (eqToHom (d.hom.obj N)) =
      d.hom.square.hom.app N ≫ eqToHom (congrArg (Q A hA).obj (d.hom.obj N))
    rw [eqToHom_map]
  have sameTensor (P : RightDGModule A) (hP : IsKProjective P) :
      d'.tensorRepresentative P = (d.onProjective P hP).hom := by
    change (Q B hB).map (d.tensorH.map (d.resolutionAdjunction.counit.app P) ≫
      eqToHom (d.tensorObj P)) =
        d.tensorSquare.hom.app ⟨P,hP⟩ ≫ eqToHom (congrArg (Q B hB).obj (d.tensorObj P))
    rw [Functor.map_comp, eqToHom_map, hc.1]
    rfl
  refine ⟨coneLocalizationOfExactness cA, coneLocalizationOfExactness cB, S', R,
    hSLaws, hRLaws, fS, gS, hf, hg, ha, ?_, ?_⟩
  · intro N n
    have he := hHom N n
    rw [sameHom N, sameHom (shift N n)] at he
    exact he
  · intro P n hP hPn
    have he := hTensor P n hP hPn
    rw [sameTensor P hP, sameTensor (shift P n) hPn] at he
    exact he

theorem exactDerivedAdjunctionAt : ExactDerivedAdjunctionAt.{u,v,w,z} := by
  intro k _ A B T m hT hA hB
  obtain ⟨d, hd, hc⟩ := buildDerivedAdjunction.{u,v,w,z} m.curry m.adjunction m.laws hT hA hB
  exact ⟨d, hd, hc, derivedAdjunctionIsExact.{u,v,w,z} m.curry m.laws hT d hd hc⟩

theorem ambientExactDerivedAdjunction : AmbientExactDerivedAdjunction.{u,v,w,vA,z,t} := by
  intro k _ A B T
  obtain ⟨S, K, L, G, E, L', G', E', adj, D, laws, _, hex, _, _⟩ :=
    ambientAdjunction.{u,v,w,z,vA,t} A B T
  refine ⟨⟨S, K, laws, ⟨L', G', E', adj, hex⟩⟩, ?_⟩
  exact exactDerivedAdjunctionAt.{u,max vA v t,w,z} (k := k) ⟨L', G', E', adj, hex⟩

end Exactness

section CoefficientComparisons

open Specs.DerivedFormalization.DG.AmbientDerived (category strictInput transportToAmbient)
open Specs.DerivedFormalization.DG.DerivedCoefficientLift (Descent strictTransition)
open Specs.DerivedFormalization.DG.BimoduleCoefficientCompatibility
  (PreservesQuasiIsomorphisms PreservesKProjectives)
open DG.DerivedCoefficientLift (derivedCoefficientTransition kProjectiveCoefficientTransition
  nativeDerivedCoefficientTransition)
open private kProjective_of_homotopyRetract from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift

universe v' w'

local instance (C : DGCategory.{u,v',w'} k) :
    Category (Specs.DerivedFormalization.DG.HomComplex.homotopyCategory C) :=
  inferInstanceAs (Category (K C))

private abbrev coefficientSignedModels
    {A : DGCategory.{u,max v w z,w} k} {B : DGCategory.{u,max v w z,z} k}
    {T : DGBimodule A B} (m : SignedModels.{u,v,w,z} T) :
    Specs.DerivedFormalization.DG.BimoduleCoefficientCompatibility.SignedModels.{u,v,w,z} T :=
  ⟨m.tensor, m.hom, m.curry, m.adjunction, m.laws⟩

private abbrev coefficientAmbientModels
    {A : DGCategory.{u,vA,w} k} {B : DGCategory.{u,v,z} k} {T : DGBimodule A B}
    (m : AmbientSignedModels.{u,v,w,vA,z,t} T) :
    Specs.DerivedFormalization.DG.BimoduleCoefficientCompatibility.AmbientSignedModels.{u,v,w,z,vA,t} T :=
  ⟨m.bimodule, m.comparison, m.comparisonLaws, coefficientSignedModels m.models⟩

private abbrev adjunctionComparisonOfCoefficient
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    {a : F ⊣ G} {a' : F' ⊣ G'} {I : C ⥤ C'} {J : D ⥤ D'}
    (e : Specs.DerivedFormalization.DG.BimoduleCoefficientCompatibility.AdjunctionComparison a a' I J) :
    AdjunctionComparison a a' I J :=
  ⟨e.tensor, e.hom, e.unit, e.counit⟩

private abbrev coefficientDescent
    {A : DGCategory.{u,max v w z,w} k} {B : DGCategory.{u,max v w z,z} k}
    {T : DGBimodule A B} {L : TensorModel T} {G : InternalHomModel T}
    {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
    (d : DerivedAdjunctionData.{u,v,w,z} L G hA hB) :
    Specs.DerivedFormalization.DG.BimoduleCoefficientCompatibility.DerivedAdjunctionData.{u,v,w,z}
      L G hA hB :=
  { tensorH := d.tensorH
    hom := ⟨d.hom.homotopy, d.hom.derived, d.hom.obj, fun f => d.hom.map f, d.hom.square⟩
    resolution := d.resolution
    resolutionAdjunction := d.resolutionAdjunction
    homotopyAdjunction := d.homotopyAdjunction
    adjunction := d.adjunction
    tensorObj := d.tensorObj
    tensorSquare := d.tensorSquare }

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientDescentRealizes
    {A : DGCategory.{u,max v w z,w} k} {B : DGCategory.{u,max v w z,z} k}
    {T : DGBimodule A B} {L : TensorModel T} {G : InternalHomModel T}
    {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
    {adj : ordinaryTensor.{u,v,w,z} L ⊣ ordinaryHom.{u,v,w,z} G}
    (d : DerivedAdjunctionData.{u,v,w,z} L G hA hB)
    (hd : d.Realizes adj) (hc : d.ComputesRepresentatives) :
    (coefficientDescent.{u,v,w,z} d).Realizes adj := by
  rcases hd with ⟨hp, hf, hu, hcounit, hdu, hdc, _⟩
  exact ⟨hp, hf, hu, hcounit, hdu, hdc, hc.1⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
private theorem derivedComparisonOfStrict
    {A : DGCategory.{u,max v w z,w} k} {B : DGCategory.{u,max v w z,z} k}
    {A' : DGCategory.{u,max s w z,w} k} {B' : DGCategory.{u,max s w z,z} k}
    {T : DGBimodule A B} {T' : DGBimodule A' B'}
    {m : SignedModels.{u,v,w,z} T} {m' : SignedModels.{u,s,w,z} T'}
    {I : RightDGModule A ⥤ RightDGModule A'} {J : RightDGModule B ⥤ RightDGModule B'}
    {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
    {hA' : HomotopyCategoryLaws A'} {hB' : HomotopyCategoryLaws B'}
    (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB)
    (d' : DerivedAdjunctionData.{u,s,w,z} m'.tensor m'.hom hA' hB')
    (hd : d.Realizes m.adjunction) (hd' : d'.Realizes m'.adjunction)
    (hc : d.ComputesRepresentatives) (hc' : d'.ComputesRepresentatives)
    (dI : Descent hA hA' I) (dJ : Descent hB hB' J)
    (e : Specs.DerivedFormalization.DG.BimoduleCoefficientCompatibility.AdjunctionComparison
      m.adjunction m'.adjunction I J)
    (hI : PreservesQuasiIsomorphisms I) (hJ : PreservesQuasiIsomorphisms J)
    (hIP : PreservesKProjectives I) :
    DerivedAdjunctionComparison d d' dI dJ (adjunctionComparisonOfCoefficient e) := by
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  letI := derivedCategoryInstance A' hA'
  letI := derivedCategoryInstance B' hB'
  obtain ⟨ed, hHom, hTensor⟩ := DG.BimoduleCoefficientCompatibility.derivedComparison.{u,v,w,z,s}
    (coefficientSignedModels m) (coefficientSignedModels m') I J hA hB hA' hB' dI dJ
    (coefficientDescent d) (coefficientDescent d') e hI hJ hIP
    (coefficientDescentRealizes d hd hc) (coefficientDescentRealizes d' hd' hc')
  refine ⟨adjunctionComparisonOfCoefficient ed, hHom, ?_⟩
  intro P M p hP hp
  exact ⟨hIP P hP, hI p hp, hTensor p hP hp⟩

private theorem projectiveOfStrictIso {C : DGCategory.{u,v,w} k} {P N : RightDGModule C}
    (e : P ≅ N) (hP : IsKProjective P) : IsKProjective N :=
  kProjective_of_homotopyRetract e.hom e.inv hP (congrArg (fun f => homotopyClass f) e.inv_hom_id)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem ambientDerivedAdjunctionComparison : AmbientDerivedAdjunctionComparison.{u,v,w,vA,z,t,s} := by
  intro k _ A B T m m' hT
  let I := strictTransition.{u,vA,w,max v z t,s} A
  let J := strictTransition.{u,v,z,max vA w t,s} B
  obtain ⟨eT, e, heT, he⟩ := DG.BimoduleCoefficientCompatibility.ambientStrictComparison.{u,v,w,z,s,vA,t}
    (coefficientAmbientModels.{u,v,w,vA,z,t} m)
    (coefficientAmbientModels.{u,v,w,vA,z,max t s} m')
  have hT' (a : A.Obj) : IsKProjective (m'.bimodule.obj a) :=
    projectiveOfStrictIso (eT a) (kProjectiveCoefficientTransition.{u,v,z,max vA w t,s}
      B (m.bimodule.obj a) (hT a))
  refine ⟨hT', ?_⟩
  intro hA hB hA' hB'
  obtain ⟨dI, hIF, _, hIR⟩ := derivedCoefficientTransition.{u,vA,w,max v z t,s} A hA hA'
  obtain ⟨dJ, hJF, _, hJR⟩ := derivedCoefficientTransition.{u,v,z,max vA w t,s} B hB hB'
  have hI : PreservesQuasiIsomorphisms I := fun f hf => (hIR f hf).choose
  have hJ : PreservesQuasiIsomorphisms J := fun f hf => (hJR f hf).choose
  have hIP : PreservesKProjectives I := kProjectiveCoefficientTransition.{u,vA,w,max v z t,s} A
  obtain ⟨d, hd, hc, hx⟩ :=
    exactDerivedAdjunctionAt.{u,max vA v t,w,z} m.models hT hA hB
  obtain ⟨d', hd', hc', hx'⟩ :=
    exactDerivedAdjunctionAt.{u,max vA v t s,w,z} m'.models hT' hA' hB'
  exact ⟨dI, dJ, adjunctionComparisonOfCoefficient e, eT, hIF, hJF, heT, he, d, d',
    hd, hc, hx, hd', hc', hx',
    derivedComparisonOfStrict.{u,max vA v t,w,z,max vA v t s} d d' hd hd' hc hc' dI dJ e hI hJ hIP⟩

private theorem nativeTransportProjective (A : DGCategory.{u,max v w t,w} k) :
    PreservesKProjectives (transportToAmbient.{u,v,w,t} A) := by
  intro P hP
  let A' := category.{u,max v w t,w,t} A
  obtain ⟨_, _, _, e, _⟩ := DG.AmbientDerived.nativeStrictComparison.{u,v,w,t} A
  have hLift : IsKProjective ((strictInput.{u,max v w t,w,t} A).obj P) :=
    (nativeDerivedCoefficientTransition.{u,max v t,w,max w t} A
      ⟨instCategoryK A, rfl⟩ ⟨instCategoryK A', rfl⟩).2 P hP
  exact projectiveOfStrictIso (e.app P) hLift

private theorem nativeTransportDescent (A : DGCategory.{u,max v w t,w} k)
    (h : HomotopyCategoryLaws A)
    (h' : HomotopyCategoryLaws (category.{u,max v w t,w,t} A)) :
    letI := derivedCategoryInstance A h
    letI := derivedCategoryInstance _ h'
    ∃ d : Descent h h' (transportToAmbient.{u,v,w,t} A),
      d.H.IsEquivalence ∧ d.D.IsEquivalence := by
  letI := derivedCategoryInstance A h
  letI := derivedCategoryInstance _ h'
  obtain ⟨e, hobj, hmap, _, e', ⟨sq⟩⟩ :=
    DG.AmbientDerived.nativeLocalizationComparison.{u,v,w,t} A h h'
  let d : Descent h h' (transportToAmbient.{u,v,w,t} A) := ⟨e.functor, e'.functor, hobj, hmap, sq⟩
  exact ⟨d, e.isEquivalence_functor, e'.isEquivalence_functor⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem nativeDerivedAdjunctionCompatibility : NativeDerivedAdjunctionCompatibility.{u,v,w,z} := by
  intro k _ A B T m m' hT
  let I := transportToAmbient.{u,v,w,max v w z} A
  let J := transportToAmbient.{u,v,z,max v w z} B
  obtain ⟨eT, e, heT, he⟩ := DG.BimoduleCoefficientCompatibility.nativeStrictComparison.{u,v,w,z}
    (coefficientSignedModels.{u,v,w,z} m)
    (coefficientAmbientModels.{u,max v w z,w,max v w z,z,0} m')
  have hIP : PreservesKProjectives I := nativeTransportProjective.{u,v,w,max v w z} A
  have hJP : PreservesKProjectives J := nativeTransportProjective.{u,v,z,max v w z} B
  have hT' (a : A.Obj) : IsKProjective (m'.bimodule.obj a) :=
    projectiveOfStrictIso (eT a) (hJP (T.obj a) (hT a))
  refine ⟨hT', ?_⟩
  intro hA hB hA' hB'
  obtain ⟨dI, hIH, hID⟩ := nativeTransportDescent.{u,v,w,max v w z} A hA hA'
  obtain ⟨dJ, hJH, hJD⟩ := nativeTransportDescent.{u,v,z,max v w z} B hB hB'
  have hI : PreservesQuasiIsomorphisms I :=
    fun f => ((DG.AmbientDerived.nativeHomotopyAndQuasiIso.{u,v,w,max v w z} A).2.1 f).mpr
  have hJ : PreservesQuasiIsomorphisms J :=
    fun f => ((DG.AmbientDerived.nativeHomotopyAndQuasiIso.{u,v,z,max v w z} B).2.1 f).mpr
  obtain ⟨d, hd, hc, hx⟩ := exactDerivedAdjunctionAt.{u,v,w,z} m hT hA hB
  obtain ⟨d', hd', hc', hx'⟩ :=
    exactDerivedAdjunctionAt.{u,max v w z,w,z} m'.models hT' hA' hB'
  exact ⟨dI, dJ, adjunctionComparisonOfCoefficient e, eT, hIH, hID, hJH, hJD, heT, he,
    d, d', hd, hc, hx, hd', hc', hx',
    derivedComparisonOfStrict.{u,v,w,z,max v w z} d d' hd hd' hc hc' dI dJ e hI hJ hIP⟩

end CoefficientComparisons

end

end DerivedFormalization.DGBimodule
