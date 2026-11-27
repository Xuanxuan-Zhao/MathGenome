import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.HomComplex
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Quotient.Basic

open CategoryTheory
open scoped Classical DirectSum TensorProduct

universe u v w z vA s

namespace Specs.DerivedFormalization.DG.BalancedTensor

open _root_.DerivedFormalization
open HomComplex (dgModuleCategory homComplex component)

variable {k : Type u} [CommRing k]

/-- The degree maps of a cochain map between complexes of possibly different
module universes. Commutation with the successor differential determines
commutation with all differentials, by the cochain shape. -/
structure CochainMap (C : ModuleCochain.{u,vA} k) (D : ModuleCochain.{u,v} k) where
  f (i : ℤ) : C.X i →ₗ[k] D.X i
  comm (i : ℤ) (x : C.X i) : f (i+1) (C.d i (i+1) x) = D.d i (i+1) (f i x)

/-- A dg functor to right dg modules, expressed by its object map and its
chain maps on morphisms. The source and target Hom degrees may have
different universes. -/
structure Bimodule (A : DGCategoryModel.{u,vA,w} k)
    (B : DGCategoryModel.{u,v,z} k) where
  obj : A.Obj → RightDGModuleModel B
  map (a b : A.Obj) : CochainMap (A.hom a b) (homComplex (obj a) (obj b))
  map_id (a : A.Obj) : (map a a).f 0 (A.id a) = (dgModuleCategory B).id (obj a)
  map_comp {a b c : A.Obj} (i j n : ℤ) (h : i+j=n)
      (f : (A.hom b c).X i) (g : (A.hom a b).X j) :
    (map a c).f n (A.comp i j n h f g) =
      (dgModuleCategory B).comp i j n h ((map b c).f i f) ((map a b).f j g)

abbrev bimodule (A : DGCategoryModel.{u,vA,w} k) (B : DGCategoryModel.{u,v,z} k) :=
  Bimodule A B

set_option linter.checkUnivs false in
def BimoduleType :=
  ∀ {k : Type u} [CommRing k] (_A : DGCategoryModel.{u,vA,w} k)
    (_B : DGCategoryModel.{u,v,z} k),
    Type (max u w z vA (v+1))

/-- A right dg module with a separate universe for its coefficient complexes.
Its objects and arrows are those of the given dg category. -/
structure RightModule (C : DGCategoryModel.{u,v,w} k) where
  complex : C.Obj → ModuleCochain.{u,s} k
  act {a b : C.Obj} (i j n : ℤ) (h : i+j=n) :
    (complex b).X i →ₗ[k] (C.hom a b).X j →ₗ[k] (complex a).X n
  act_id (a : C.Obj) (i : ℤ) (x : (complex a).X i) :
    act i 0 i (add_zero i) x (C.id a) = x
  act_assoc {a b c : C.Obj} (i j l : ℤ)
      (x : (complex c).X i) (f : (C.hom b c).X j) (g : (C.hom a b).X l) :
    act (i+j) l (i+j+l) rfl (act i j (i+j) rfl x f) g =
      act i (j+l) (i+j+l) (add_assoc i j l).symm x (C.comp j l (j+l) rfl f g)
  leibniz {a b : C.Obj} (i j n : ℤ) (h : i+j=n)
      (x : (complex b).X i) (f : (C.hom a b).X j) :
    (complex a).d n (n+1) (act i j n h x f) =
      act (i+1) j (n+1) (by omega) ((complex b).d i (i+1) x) f +
        i.negOnePow • act i (j+1) (n+1) (by omega) x ((C.hom a b).d j (j+1) f)

/-- Strict maps of right dg modules with these coefficient universes. -/
structure RightModule.Hom {C : DGCategoryModel.{u,v,w} k}
    (M N : RightModule.{u,v,w,s} C) where
  app (a : C.Obj) : M.complex a ⟶ N.complex a
  comm_act {a b : C.Obj} (i j n : ℤ) (h : i+j=n)
      (x : (M.complex b).X i) (f : (C.hom a b).X j) :
    (app a).f n (M.act i j n h x f) = N.act i j n h ((app b).f i x) f

namespace RightModule

variable {C : DGCategoryModel.{u,v,w} k}

@[ext] theorem hom_ext {M N : RightModule.{u,v,w,s} C} {f g : Hom M N}
    (e : ∀ a, f.app a = g.app a) : f = g := by
  cases f
  cases g
  congr
  exact funext e

instance : Category (RightModule.{u,v,w,s} C) where
  Hom := Hom
  id M := ⟨fun _ => 𝟙 _, fun _ _ _ _ _ _ => rfl⟩
  comp f g := ⟨fun a => f.app a ≫ g.app a, by
    intro a b i j n h x u
    change (g.app a).f n ((f.app a).f n _) = _
    rw [f.comm_act, g.comm_act]
    rfl⟩
  id_comp _ := hom_ext fun _ => Category.id_comp _
  comp_id _ := hom_ext fun _ => Category.comp_id _
  assoc _ _ _ := hom_ext fun _ => Category.assoc _ _ _

/-- At equal universes, use the shared right dg module and strict map types. -/
@[reducible] def toOrdinary : RightModule.{u,v,w,v} C ⥤ RightDGModuleModel C where
  obj M := ⟨M.complex, M.act, M.act_id, M.act_assoc, M.leibniz⟩
  map f := ⟨f.app, f.comm_act⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end RightModule

variable {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}
variable (T : bimodule A B) (M : RightDGModuleModel A)

abbrev Index (O : Type w) (n : ℤ) :=
  Σ _ : O, { ij : ℤ × ℤ // ij.1 + ij.2 = n }

abbrev Summand (b : B.Obj) (n : ℤ) (p : Index A.Obj n) :=
  ((M.complex p.1).X p.2.1.1) ⊗[k] (((T.obj p.1).complex b).X p.2.1.2)

abbrev Raw (b : B.Obj) (n : ℤ) := ⨁ p : Index A.Obj n, Summand T M b n p

noncomputable def rawTmul (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) : Raw T M b n :=
  DirectSum.lof k (Index A.Obj n) (Summand T M b n) ⟨a, ⟨(i,j), h⟩⟩ (m ⊗ₜ[k] t)

/-- The coefficient of a homogeneous arrow acting on a bimodule element. -/
abbrev left (b : B.Obj) {a a' : A.Obj} (l j q : ℤ) (e : l+j=q)
    (f : (A.hom a a').X l) (t : ((T.obj a).complex b).X j) :
    ((T.obj a').complex b).X q :=
  component ((T.map a a').f l f) b j q (by omega) t

def Relations (b : B.Obj) (n : ℤ) : Set (Raw T M b n) :=
  { x | ∃ (a a' : A.Obj) (i l j : ℤ) (h : i+l+j=n)
      (m : (M.complex a').X i) (f : (A.hom a a').X l)
      (t : ((T.obj a).complex b).X j),
    x = rawTmul T M b a (i+l) j n h (M.act i l (i+l) rfl m f) t -
      rawTmul T M b a' i (l+j) n (by omega) m (left T b l j (l+j) rfl f t) }

abbrev Balance (b : B.Obj) (n : ℤ) := Submodule.span k (Relations T M b n)

abbrev Degree (b : B.Obj) (n : ℤ) := Raw T M b n ⧸ Balance T M b n

noncomputable def tmul (b : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
    (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j) : Degree T M b n :=
  (Balance T M b n).mkQ (rawTmul T M b a i j n h m t)

/-- The balanced tensor is functorial in the right input module. Its degreewise
identification is with the actual quotient by the span of all balancing relations.
The coefficient universe accommodates the direct sum indexed by the source objects. -/
def TensorConstruction : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,vA,w} k)
    (B : DGCategoryModel.{u,v,z} k) (T : bimodule A B),
  ∃ (F : RightDGModuleModel A ⥤ RightModule.{u,v,z,max vA v w} B)
    (E : ∀ M b n, Degree T M b n ≃ₗ[k] ((F.obj M).complex b).X n),
    (∀ (M : RightDGModuleModel A) (a : A.Obj) (b : B.Obj) (i j n : ℤ) (h : i+j=n)
      (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j),
      ((F.obj M).complex b).d n (n+1) (E M b n (tmul T M b a i j n h m t)) =
        E M b (n+1) (tmul T M b a (i+1) j (n+1) (by omega)
          ((M.complex a).d i (i+1) m) t) +
        i.negOnePow • E M b (n+1) (tmul T M b a i (j+1) (n+1) (by omega) m
          (((T.obj a).complex b).d j (j+1) t))) ∧
    (∀ (M : RightDGModuleModel A) (a : A.Obj) {b c : B.Obj} (i j n l q : ℤ)
      (h : i+j=n) (e : n+l=q) (m : (M.complex a).X i)
      (t : ((T.obj a).complex c).X j) (f : (B.hom b c).X l),
      (F.obj M).act n l q e (E M c n (tmul T M c a i j n h m t)) f =
        E M b q (tmul T M b a i (j+l) q (by omega) m ((T.obj a).act j l (j+l) rfl t f))) ∧
    (∀ {M N : RightDGModuleModel A} (f : M ⟶ N) (a : A.Obj) (b : B.Obj)
      (i j n : ℤ) (h : i+j=n) (m : (M.complex a).X i) (t : ((T.obj a).complex b).X j),
      ((F.map f).app b).f n (E M b n (tmul T M b a i j n h m t)) =
        E N b n (tmul T N b a i j n h ((f.app a).f i m) t))

/-- The internal Hom is functorial in its target. Its right action is
precomposition with the homogeneous morphisms of the bimodule. -/
def HomConstruction : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,vA,w} k)
    (B : DGCategoryModel.{u,v,z} k) (T : bimodule A B),
  ∃ (G : RightDGModuleModel B ⥤ RightModule.{u,vA,w,max v z} A)
    (E : ∀ N a, homComplex (T.obj a) N ≅ (G.obj N).complex a),
    (∀ (N : RightDGModuleModel B) {a a' : A.Obj} (i j n : ℤ) (h : i+j=n)
      (g : (homComplex (T.obj a') N).X i) (f : (A.hom a a').X j),
      (G.obj N).act i j n h ((E N a').hom.f i g) f =
        (E N a).hom.f n ((dgModuleCategory B).comp i j n h g ((T.map a a').f j f))) ∧
    (∀ {N P : RightDGModuleModel B} (f : N ⟶ P) (a : A.Obj) (i : ℤ)
      (g : (homComplex (T.obj a) N).X i),
      ((G.map f).app a).f i ((E N a).hom.f i g) =
        (E P a).hom.f i ((dgModuleCategory B).comp 0 i i (zero_add i)
          (HomComplex.ofStrict f) g))

end Specs.DerivedFormalization.DG.BalancedTensor
