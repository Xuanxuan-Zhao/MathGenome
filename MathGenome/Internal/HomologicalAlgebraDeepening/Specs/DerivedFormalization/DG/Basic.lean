import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Linear.Basic

open CategoryTheory
open scoped TensorProduct

universe u v w w'

namespace DerivedFormalization

abbrev ModuleCochain (k : Type u) [CommRing k] :=
  CochainComplex (ModuleCat.{v} k) ℤ

/--
DG structure on a fixed type of objects. The equality argument to `comp` allows
a homogeneous product to be used directly in any degree equal to the sum.
The order is `comp f g = f ∘ g`.
-/
structure DGCategoryData (k : Type u) [CommRing k] (O : Type w) where
  hom : O → O → ModuleCochain.{u,v} k
  comp {a b c : O} (i j n : ℤ) (h : i + j = n) :
    (hom b c).X i →ₗ[k] (hom a b).X j →ₗ[k] (hom a c).X n
  id (a : O) : (hom a a).X 0
  d_id (a : O) : (hom a a).d 0 1 (id a) = 0
  id_comp {a b : O} (i : ℤ) (f : (hom a b).X i) :
    comp 0 i i (zero_add i) (id b) f = f
  comp_id {a b : O} (i : ℤ) (f : (hom a b).X i) :
    comp i 0 i (add_zero i) f (id a) = f
  assoc {a b c e : O} (i j l : ℤ)
      (f : (hom c e).X i) (g : (hom b c).X j) (h : (hom a b).X l) :
    comp (i+j) l (i+j+l) rfl (comp i j (i+j) rfl f g) h =
      comp i (j+l) (i+j+l) (add_assoc i j l).symm f (comp j l (j+l) rfl g h)
  leibniz {a b c : O} (i j n : ℤ) (h : i+j = n)
      (f : (hom b c).X i) (g : (hom a b).X j) :
    (hom a c).d n (n+1) (comp i j n h f g) =
      comp (i+1) j (n+1) (by omega) ((hom b c).d i (i+1) f) g +
        i.negOnePow • comp i (j+1) (n+1) (by omega) f ((hom a b).d j (j+1) g)

namespace DGCategoryData

variable {k : Type u} [CommRing k]

/-- Pull back the morphism complexes along a function on objects. -/
def reindex {O : Type w} {P : Type w'} (A : DGCategoryData.{u,v} k O) (f : P → O) :
    DGCategoryData.{u,v} k P where
  hom a b := A.hom (f a) (f b)
  comp i j n h := A.comp i j n h
  id a := A.id (f a)
  d_id a := A.d_id (f a)
  id_comp := A.id_comp
  comp_id := A.comp_id
  assoc := A.assoc
  leibniz := A.leibniz

end DGCategoryData

/-- The canonical bundled model of a small dg category. -/
structure DGCategoryModel (k : Type u) [CommRing k] where
  Obj : Type w
  toData : DGCategoryData.{u,v} k Obj

/-- The one-object dg structure is the single-complex model of a dg algebra. -/
abbrev DGAlgebraModel (k : Type u) [CommRing k] := DGCategoryData.{u,v} k Unit

namespace DGCategoryModel

variable {k : Type u} [CommRing k]

abbrev hom (A : DGCategoryModel.{u,v,w} k) := A.toData.hom
abbrev comp (A : DGCategoryModel.{u,v,w} k) := @A.toData.comp
abbrev id (A : DGCategoryModel.{u,v,w} k) := A.toData.id

end DGCategoryModel

/-- A dg functor has a chain map on each morphism complex. -/
structure DGFunctorModel {k : Type u} [CommRing k]
    (A : DGCategoryModel.{u,v,w} k) (B : DGCategoryModel.{u,v,w'} k) where
  obj : A.Obj → B.Obj
  map (a b : A.Obj) : A.hom a b ⟶ B.hom (obj a) (obj b)
  map_id (a : A.Obj) : (map a a).f 0 (A.id a) = B.id (obj a)
  map_comp {a b c : A.Obj} (i j n : ℤ) (h : i+j = n)
      (f : (A.hom b c).X i) (g : (A.hom a b).X j) :
    (map a c).f n (A.comp i j n h f g) =
      B.comp i j n h ((map b c).f i f) ((map a b).f j g)

end DerivedFormalization

namespace Specs.DerivedFormalization.DG.Basic

open _root_.DerivedFormalization

set_option linter.checkUnivs false

variable {k : Type u} [CommRing k]

def DGAlgebraType := ∀ (k : Type u) [CommRing k], Type (max u (v+1))
abbrev dgAlgebra (k : Type u) [CommRing k] := DGAlgebraModel.{u,v} k

def DGCategoryType := ∀ (k : Type u) [CommRing k], Type (max u (max (v+1) (w+1)))
abbrev dgCategory (k : Type u) [CommRing k] := DGCategoryModel.{u,v,w} k

def DGFunctorType :=
  ∀ {k : Type u} [CommRing k] (_A : DGCategoryModel.{u,v,w} k)
    (_B : DGCategoryModel.{u,v,w'} k), Type (max v (max w w'))

abbrev dgFunctor (A : DGCategoryModel.{u,v,w} k) (B : DGCategoryModel.{u,v,w'} k) :=
  DGFunctorModel A B

@[reducible] def toDGCategory (A : DGAlgebraModel.{u,v} k) : DGCategoryModel.{u,v,0} k :=
  ⟨Unit, A⟩

def endAlgebra (A : DGCategoryModel.{u,v,w} k) (a : A.Obj) : DGAlgebraModel.{u,v} k :=
  A.toData.reindex (fun _ => a)

def AlgebraRoundTrip : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGAlgebraModel.{u,v} k), endAlgebra (toDGCategory A) () = A

def ToDGCategoryType := ∀ {k : Type u} [CommRing k],
  DGAlgebraModel.{u,v} k → DGCategoryModel.{u,v,0} k

def EndAlgebraType := ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
  A.Obj → DGAlgebraModel.{u,v} k

/-- Reindexing from a point in a singleton DG category is an isomorphism:
the object map is bijective and the indicated DG functor is an isomorphism
on each morphism complex. -/
def OneObjectIdentification : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k) (a : A.Obj), (∀ b : A.Obj, b = a) →
    ∃ F : DGFunctorModel (toDGCategory (endAlgebra A a)) A,
      F.obj () = a ∧ Function.Bijective F.obj ∧ ∀ x y, IsIso (F.map x y)

noncomputable section

open HomologicalComplex

/-- The ordinary module tensor bifunctor in any module universe. -/
@[reducible] def moduleTensor (k : Type u) [CommRing k] :
    ModuleCat.{v} k ⥤ ModuleCat.{v} k ⥤ ModuleCat.{v} k where
  obj M :=
    { obj := fun N => ModuleCat.of k (M ⊗[k] N)
      map := fun f => ModuleCat.ofHom (TensorProduct.map LinearMap.id f.hom)
      map_id := by
        intro N
        apply ModuleCat.hom_ext
        exact TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => by simp)
      map_comp := by
        intro N N' N'' f g
        apply ModuleCat.hom_ext
        exact TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => by simp) }
  map f :=
    { app := fun N => ModuleCat.ofHom (TensorProduct.map f.hom LinearMap.id)
      naturality := by
        intro N N' g
        apply ModuleCat.hom_ext
        exact TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => by simp) }
  map_id := by
    intro M
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    exact TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => by simp)
  map_comp := by
    intro M M' M'' f g
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    exact TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => by simp)

instance : (moduleTensor.{u,v} k).PreservesZeroMorphisms where
  map_zero M N := by
    apply NatTrans.ext
    funext T
    apply ModuleCat.hom_ext
    change TensorProduct.map ((0 : M ⟶ N).hom) LinearMap.id = 0
    rw [ModuleCat.hom_zero, TensorProduct.map_zero_left]

instance (M : ModuleCat.{v} k) : ((moduleTensor k).obj M).PreservesZeroMorphisms where
  map_zero N N' := by
    apply ModuleCat.hom_ext
    change TensorProduct.map LinearMap.id ((0 : N ⟶ N').hom) = 0
    rw [ModuleCat.hom_zero, TensorProduct.map_zero_right]

abbrev cochainTensor (C D : ModuleCochain.{u,v} k) :=
  mapBifunctor C D (moduleTensor k) (ComplexShape.up ℤ)

abbrev cochainTensorInclusion (C D : ModuleCochain.{u,v} k) (i j n : ℤ)
    (h : i+j = n) :=
  ιMapBifunctor C D (moduleTensor k) (ComplexShape.up ℤ) i j n h

/-- Each tensor summand uses the original bilinear composition. -/
def TensorComposition : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k) (a b c : A.Obj),
    ∃ m : cochainTensor (A.hom b c) (A.hom a b) ⟶ A.hom a c,
      ∀ (i j n : ℤ) (h : i+j = n)
        (f : (A.hom b c).X i) (g : (A.hom a b).X j),
        m.f n (cochainTensorInclusion (A.hom b c) (A.hom a b) i j n h (f ⊗ₜ[k] g)) =
          A.comp i j n h f g

/-- The short complex computing degree-zero cohomology of a cochain complex. -/
abbrev zeroShort (C : ModuleCochain.{u,v} k) := C.sc' (-1) 0 1

abbrev cyclesZero (C : ModuleCochain.{u,v} k) :=
  LinearMap.ker (zeroShort C).g.hom

abbrev boundariesZero (C : ModuleCochain.{u,v} k) :=
  LinearMap.range (zeroShort C).moduleCatToCycles

abbrev h0Hom (C : ModuleCochain.{u,v} k) :=
  cyclesZero C ⧸ boundariesZero C

abbrev classOf {C : ModuleCochain.{u,v} k} (f : cyclesZero C) : h0Hom C :=
  Submodule.Quotient.mk f

def cycleId (A : DGCategoryModel.{u,v,w} k) (a : A.Obj) : cyclesZero (A.hom a a) :=
  ⟨A.id a, A.toData.d_id a⟩

def cycleComp (A : DGCategoryModel.{u,v,w} k) {a b c : A.Obj}
    (f : cyclesZero (A.hom b c)) (g : cyclesZero (A.hom a b)) :
    cyclesZero (A.hom a c) :=
  ⟨A.comp 0 0 0 rfl f.val g.val, by
    have hf : (A.hom b c).d 0 1 f.val = 0 := f.property
    have hg : (A.hom a b).d 0 1 g.val = 0 := g.property
    change (A.hom a c).d 0 1 (A.comp 0 0 0 rfl f.val g.val) = 0
    calc
      _ = _ := A.toData.leibniz 0 0 0 rfl f.val g.val
      _ = 0 := by
        change (A.toData.hom b c).d 0 (0+1) f.val = 0 at hf
        change (A.toData.hom a b).d 0 (0+1) g.val = 0 at hg
        rw [hf, hg]
        simp⟩

/-- An expected value for composition, specified using representatives.
Its independence of the representatives is a separate proof obligation. -/
def h0Comp (A : DGCategoryModel.{u,v,w} k) {a b c : A.Obj}
    (f : h0Hom (A.hom b c)) (g : h0Hom (A.hom a b)) : h0Hom (A.hom a c) :=
  classOf (cycleComp A (Quotient.out f) (Quotient.out g))

def H0Composition : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k) {a b c : A.Obj}
    (f : cyclesZero (A.hom b c)) (g : cyclesZero (A.hom a b)),
    h0Comp A (classOf f) (classOf g) = classOf (cycleComp A f g)

def cycleMap {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,w'} k}
    (F : DGFunctorModel A B) {a b : A.Obj} (f : cyclesZero (A.hom a b)) :
    cyclesZero (B.hom (F.obj a) (F.obj b)) :=
  ⟨(F.map a b).f 0 f.val, by
    have hf : (A.hom a b).d 0 1 f.val = 0 := f.property
    change (B.hom (F.obj a) (F.obj b)).d 0 1 ((F.map a b).f 0 f.val) = 0
    have hcomm := (F.map a b).comm 0 1
    rw [← ModuleCat.comp_apply, hcomm, ModuleCat.comp_apply, hf, map_zero]⟩

def h0Map {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,w'} k}
    (F : DGFunctorModel A B) {a b : A.Obj} (f : h0Hom (A.hom a b)) :
    h0Hom (B.hom (F.obj a) (F.obj b)) :=
  classOf (cycleMap F (Quotient.out f))

def H0Map : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,w'} k}
    (F : DGFunctorModel A B) {a b : A.Obj} (f : cyclesZero (A.hom a b)),
    h0Map F (classOf f) = classOf (cycleMap F f)

@[implicit_reducible] def h0Objects (A : DGCategoryModel.{u,v,w} k) := A.Obj

def H0ObjectsType := ∀ {k : Type u} [CommRing k], DGCategoryModel.{u,v,w} k → Type w

/-- The object, morphism, identity and composition data of the cohomology category. -/
@[implicit_reducible] def h0CategoryStruct (A : DGCategoryModel.{u,v,w} k) :
    CategoryStruct.{v} (h0Objects A) where
  Hom a b := h0Hom (A.hom a b)
  id a := classOf (cycleId A a)
  comp f g := h0Comp A g f

def H0CategoryStructure : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k), ∃ C : Category.{v} (h0Objects A),
    C.toCategoryStruct = h0CategoryStruct A

def H0Homology : Prop :=
  ∀ {k : Type u} [CommRing k] (C : ModuleCochain.{u,v} k), Nonempty (ModuleCat.of k (h0Hom C) ≅ C.homology 0)

def h0Prefunctor {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,w'} k}
    (F : DGFunctorModel A B) :
    @Prefunctor (h0Objects A) (h0CategoryStruct A).toQuiver
      (h0Objects B) (h0CategoryStruct B).toQuiver := by
  letI : Quiver (h0Objects A) := (h0CategoryStruct A).toQuiver
  letI : Quiver (h0Objects B) := (h0CategoryStruct B).toQuiver
  exact { obj := F.obj, map := fun {_ _} f => h0Map F f }

def H0FunctorStructure : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,w'} k}
    (F : DGFunctorModel A B),
    ∃ (CA : Category.{v} (h0Objects A)) (CB : Category.{v} (h0Objects B))
      (G : @Functor (h0Objects A) CA (h0Objects B) CB),
      CA.toCategoryStruct = h0CategoryStruct A ∧
      CB.toCategoryStruct = h0CategoryStruct B ∧ HEq G.toPrefunctor (h0Prefunctor F)

def QuasiEquivalenceType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,w'} k},
    DGFunctorModel A B → Prop

/-- The inverse equations are written in the composition order of the source. -/
def quasiEquivalence {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,w'} k}
    (F : DGFunctorModel A B) : Prop :=
  (∀ a b, QuasiIso (F.map a b)) ∧
    ∀ b : B.Obj, ∃ a : A.Obj,
      ∃ f : h0Hom (B.hom (F.obj a) b), ∃ g : h0Hom (B.hom b (F.obj a)),
        h0Comp B f g = classOf (cycleId B b) ∧
          h0Comp B g f = classOf (cycleId B (F.obj a))

end

end Specs.DerivedFormalization.DG.Basic
