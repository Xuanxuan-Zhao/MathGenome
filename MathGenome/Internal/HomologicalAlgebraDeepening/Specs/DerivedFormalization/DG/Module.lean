import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Basic
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w j h

namespace DerivedFormalization

variable {k : Type u} [CommRing k]

/-- The right action uses the source object's complex after multiplication. -/
structure RightDGModuleModel (A : DGCategoryModel.{u,v,w} k) where
  complex : A.Obj → ModuleCochain.{u,v} k
  act {a b : A.Obj} (i j n : ℤ) (h : i + j = n) :
    (complex b).X i →ₗ[k] (A.hom a b).X j →ₗ[k] (complex a).X n
  act_id (a : A.Obj) (i : ℤ) (x : (complex a).X i) :
    act i 0 i (add_zero i) x (A.id a) = x
  act_assoc {a b c : A.Obj} (i j l : ℤ)
      (x : (complex c).X i) (f : (A.hom b c).X j) (g : (A.hom a b).X l) :
    act (i+j) l (i+j+l) rfl (act i j (i+j) rfl x f) g =
      act i (j+l) (i+j+l) (add_assoc i j l).symm x (A.comp j l (j+l) rfl f g)
  leibniz {a b : A.Obj} (i j n : ℤ) (h : i+j = n)
      (x : (complex b).X i) (f : (A.hom a b).X j) :
    (complex a).d n (n+1) (act i j n h x f) =
      act (i+1) j (n+1) (by omega) ((complex b).d i (i+1) x) f +
        i.negOnePow • act i (j+1) (n+1) (by omega) x ((A.hom a b).d j (j+1) f)

/-- The strict degree-zero maps between right dg modules. -/
structure RightDGModuleHomModel {A : DGCategoryModel.{u,v,w} k}
    (M N : RightDGModuleModel A) where
  app (a : A.Obj) : M.complex a ⟶ N.complex a
  comm_act {a b : A.Obj} (i j n : ℤ) (h : i+j = n)
      (x : (M.complex b).X i) (f : (A.hom a b).X j) :
    (app a).f n (M.act i j n h x f) = N.act i j n h ((app b).f i x) f

namespace RightDGModuleModel

variable {A : DGCategoryModel.{u,v,w} k}

@[ext] theorem hom_ext {M N : RightDGModuleModel A} {f g : RightDGModuleHomModel M N}
    (e : ∀ a, f.app a = g.app a) : f = g := by
  cases f
  cases g
  congr
  exact funext e

instance category : Category (RightDGModuleModel A) where
  Hom := RightDGModuleHomModel
  id M := ⟨fun _ => 𝟙 _, fun _ _ _ _ _ _ => rfl⟩
  comp f g :=
    ⟨fun a => f.app a ≫ g.app a, by
      intro a b i j n h x u
      change (g.app a).f n ((f.app a).f n _) = _
      rw [f.comm_act, g.comm_act]
      rfl⟩
  id_comp _ := hom_ext fun _ => Category.id_comp _
  comp_id _ := hom_ext fun _ => Category.comp_id _
  assoc _ _ _ := hom_ext fun _ => Category.assoc _ _ _

instance zeroMorphisms : HasZeroMorphisms (RightDGModuleModel A) where
  zero M N := ⟨fun _ => 0, by
    intro a b i j n h x f
    change (0 : (N.complex a).X n) = N.act i j n h (0 : (N.complex b).X i) f
    rw [map_zero, LinearMap.zero_apply]⟩
  comp_zero _ _ := hom_ext fun _ => comp_zero
  zero_comp X {Y Z} f := hom_ext fun _ => zero_comp

@[simp] theorem id_app (M : RightDGModuleModel A) (a : A.Obj) :
    (𝟙 M : RightDGModuleHomModel M M).app a = 𝟙 _ := rfl

@[simp] theorem comp_app {M N P : RightDGModuleModel A} (f : M ⟶ N) (g : N ⟶ P)
    (a : A.Obj) : (f ≫ g : RightDGModuleHomModel M P).app a = f.app a ≫ g.app a := rfl

@[simp] theorem zero_app (M N : RightDGModuleModel A) (a : A.Obj) :
    ((0 : M ⟶ N) : RightDGModuleHomModel M N).app a = 0 := rfl

/-- Evaluation at an object is a functor to cochain complexes. -/
def eval (a : A.Obj) : RightDGModuleModel A ⥤ ModuleCochain.{u,v} k where
  obj M := M.complex a
  map f := f.app a
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- Evaluation at an object and a cochain degree. -/
abbrev degree (a : A.Obj) (n : ℤ) : RightDGModuleModel A ⥤ ModuleCat.{v} k :=
  eval a ⋙ HomologicalComplex.eval _ _ n

instance (a : A.Obj) : (eval (A := A) a).PreservesZeroMorphisms where
  map_zero _ _ := rfl

instance (a : A.Obj) (n : ℤ) : (degree (A := A) a n).PreservesZeroMorphisms where
  map_zero _ _ := rfl

end RightDGModuleModel

/-- Single-complex formulation of a right module over a dg algebra. -/
structure RightDGAlgebraModuleModel (A : DGAlgebraModel.{u,v} k) where
  complex : ModuleCochain.{u,v} k
  act (i j n : ℤ) (h : i+j = n) :
    complex.X i →ₗ[k] (A.hom () ()).X j →ₗ[k] complex.X n
  act_id (i : ℤ) (x : complex.X i) : act i 0 i (add_zero i) x (A.id ()) = x
  act_assoc (i j l : ℤ) (x : complex.X i) (f : (A.hom () ()).X j) (g : (A.hom () ()).X l) :
    act (i+j) l (i+j+l) rfl (act i j (i+j) rfl x f) g =
      act i (j+l) (i+j+l) (add_assoc i j l).symm x (A.comp j l (j+l) rfl f g)
  leibniz (i j n : ℤ) (h : i+j = n) (x : complex.X i) (f : (A.hom () ()).X j) :
    complex.d n (n+1) (act i j n h x f) =
      act (i+1) j (n+1) (by omega) (complex.d i (i+1) x) f +
        i.negOnePow • act i (j+1) (n+1) (by omega) x ((A.hom () ()).d j (j+1) f)

end DerivedFormalization

namespace Specs.DerivedFormalization.DG.Module

open _root_.DerivedFormalization

set_option linter.checkUnivs false
open Specs.DerivedFormalization.DG.Basic (cochainTensor cochainTensorInclusion toDGCategory)

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}

abbrev rightDGModule := @RightDGModuleModel
abbrev moduleHom := @RightDGModuleHomModel
abbrev rightDGAlgebraModule (B : DGAlgebraModel.{u,v} k) :=
  RightDGModuleModel (toDGCategory B)

def RightDGModuleType := ∀ {k : Type u} [CommRing k], DGCategoryModel.{u,v,w} k → Type (max u w (v+1))

def ModuleHomType := ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
  RightDGModuleModel A → RightDGModuleModel A → Type (max v w)

def RightDGAlgebraModuleType := ∀ {k : Type u} [CommRing k], DGAlgebraModel.{u,v} k → Type (max u (v+1))

def acyclic (M : RightDGModuleModel A) : Prop := ∀ a, (M.complex a).Acyclic

def quasiIsomorphism {M N : RightDGModuleModel A} (f : M ⟶ N) : Prop :=
  ∀ a, QuasiIso (f.app a)

def degreewiseSurjective {M N : RightDGModuleModel A} (f : M ⟶ N) : Prop :=
  ∀ a n, Function.Surjective ((f.app a).f n)

def AcyclicType := ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
  RightDGModuleModel A → Prop

def MapPredicate := ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
  {M N : RightDGModuleModel A}, (M ⟶ N) → Prop

def OneObject : Prop :=
  ∀ {k : Type u} [CommRing k] (B : DGAlgebraModel.{u,v} k),
    ∃ e : RightDGModuleModel (toDGCategory B) ≃ RightDGAlgebraModuleModel B,
      ∀ M, (e M).complex = M.complex () ∧ HEq (e M).act (M.act (a := ()) (b := ()))

def AtUniqueObject : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k) (a : A.Obj)
    (_unique : ∀ b : A.Obj, b = a),
    ∃ e : RightDGModuleModel A ≃ RightDGAlgebraModuleModel (Basic.endAlgebra A a),
      ∀ M, (e M).complex = M.complex a ∧ HEq (e M).act (M.act (a := a) (b := a))

def TensorAction : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (M : RightDGModuleModel A) (a b : A.Obj),
    ∃ m : cochainTensor (M.complex b) (A.hom a b) ⟶ M.complex a,
      ∀ (i j n : ℤ) (h : i+j = n) (x : (M.complex b).X i) (f : (A.hom a b).X j),
        m.f n (cochainTensorInclusion (M.complex b) (A.hom a b) i j n h (x ⊗ₜ[k] f)) =
          M.act i j n h x f

def PointwiseLimits : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {J : Type j} [Category.{h} J] [HasLimitsOfShape J (ModuleCat.{v} k)]
    (F : J ⥤ RightDGModuleModel A),
    ∃ c : Cone F, Nonempty (IsLimit c) ∧
      (∀ a, Nonempty (IsLimit ((RightDGModuleModel.eval a).mapCone c))) ∧
      ∀ a n, Nonempty (IsLimit ((RightDGModuleModel.degree a n).mapCone c))

def PointwiseColimits : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {J : Type j} [Category.{h} J] [HasColimitsOfShape J (ModuleCat.{v} k)]
    (F : J ⥤ RightDGModuleModel A),
    ∃ c : Cocone F, Nonempty (IsColimit c) ∧
      (∀ a, Nonempty (IsColimit ((RightDGModuleModel.eval a).mapCocone c))) ∧
      ∀ a n, Nonempty (IsColimit ((RightDGModuleModel.degree a n).mapCocone c))

/-- A strict kernel is computed by the kernel complexes, including the concrete degree inclusions. -/
def PointwiseKernels : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (f : M ⟶ N),
    ∃ c : KernelFork f, Nonempty (IsLimit c) ∧
      (∀ a, Nonempty (IsLimit (c.map (RightDGModuleModel.eval a)))) ∧
      ∀ a n, ∃ e : (c.pt.complex a).X n ≅ ModuleCat.of k (LinearMap.ker ((f.app a).f n).hom),
        e.hom ≫ ModuleCat.ofHom (LinearMap.ker ((f.app a).f n).hom).subtype = (c.ι.app a).f n

/-- A strict cokernel is computed by the quotient complexes and their concrete projections. -/
def PointwiseCokernels : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (f : M ⟶ N),
    ∃ c : CokernelCofork f, Nonempty (IsColimit c) ∧
      (∀ a, Nonempty (IsColimit (c.map (RightDGModuleModel.eval a)))) ∧
      ∀ a n, ∃ e : (c.pt.complex a).X n ≅
        ModuleCat.of k ((N.complex a).X n ⧸ LinearMap.range ((f.app a).f n).hom),
        (c.π.app a).f n ≫ e.hom = ModuleCat.ofHom (LinearMap.range ((f.app a).f n).hom).mkQ

/-- Every small family has a strict coproduct formed objectwise and degreewise. -/
def StrictSums : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type v} (M : I → RightDGModuleModel A),
    ∃ c : Cocone (Discrete.functor M), Nonempty (IsColimit c) ∧
      (∀ a, Nonempty (IsColimit ((RightDGModuleModel.eval a).mapCocone c))) ∧
      ∀ a n, Nonempty (IsColimit ((RightDGModuleModel.degree a n).mapCocone c))

/-- Every sequence of strict maps has a strict colimit formed objectwise and degreewise. -/
def SequentialColimits : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (M : ℕ → RightDGModuleModel A) (step : ∀ n, M n ⟶ M (n+1)),
    ∃ c : Cocone (Functor.ofSequence step), Nonempty (IsColimit c) ∧
      (∀ a, Nonempty (IsColimit ((RightDGModuleModel.eval a).mapCocone c))) ∧
      ∀ a n, Nonempty (IsColimit ((RightDGModuleModel.degree a n).mapCocone c))

end Specs.DerivedFormalization.DG.Module
