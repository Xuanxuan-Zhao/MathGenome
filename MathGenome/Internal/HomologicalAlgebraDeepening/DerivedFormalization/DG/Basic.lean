import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor

open CategoryTheory
open scoped TensorProduct

universe u v w w'

namespace DerivedFormalization


abbrev DGAlgebra := Specs.DerivedFormalization.DG.Basic.dgAlgebra
set_option linter.checkUnivs false in
abbrev DGCategory := Specs.DerivedFormalization.DG.Basic.dgCategory
abbrev DGFunctor := @Specs.DerivedFormalization.DG.Basic.dgFunctor

variable {k : Type u} [CommRing k]

namespace ModuleCochain

noncomputable abbrev tensor (C D : ModuleCochain.{u,v} k) :=
  Specs.DerivedFormalization.DG.Basic.cochainTensor C D

noncomputable abbrev tensorInclusion (C D : ModuleCochain.{u,v} k) (i j n : ℤ) (h : i+j=n) :=
  Specs.DerivedFormalization.DG.Basic.cochainTensorInclusion C D i j n h

end ModuleCochain

namespace DGAlgebra

abbrev complex (A : DGAlgebra.{u,v} k) := A.hom () ()
abbrev mul (A : DGAlgebra.{u,v} k) (i j n : ℤ) (h : i+j = n) :=
  A.comp (a := ()) (b := ()) (c := ()) i j n h
abbrev one (A : DGAlgebra.{u,v} k) := A.id ()

def toDGCategory (A : DGAlgebra.{u,v} k) : DGCategory.{u,v,0} k :=
  ⟨Unit, A⟩

end DGAlgebra

namespace DGCategory

abbrev hom (A : DGCategory.{u,v,w} k) := A.toData.hom
abbrev comp (A : DGCategory.{u,v,w} k) := @A.toData.comp
abbrev id (A : DGCategory.{u,v,w} k) := A.toData.id

def endAlgebra (A : DGCategory.{u,v,w} k) (a : A.Obj) : DGAlgebra.{u,v} k :=
  A.toData.reindex (fun _ => a)

end DGCategory

theorem algebraRoundTrip : Specs.DerivedFormalization.DG.Basic.AlgebraRoundTrip.{u,v} := by
  intro k _ A
  cases A with
  | mk hom comp id d_id id_comp comp_id assoc leibniz =>
    rfl

theorem oneObjectIdentification : Specs.DerivedFormalization.DG.Basic.OneObjectIdentification.{u,v,w} := by
  intro k _ A a ha
  refine ⟨{ obj := fun _ => a
            map := fun _ _ => 𝟙 _
            map_id := fun _ => rfl
            map_comp := fun _ _ _ _ _ _ => rfl },
    rfl, ⟨fun x y _ => Subsingleton.elim x y, fun b => ⟨(), (ha b).symm⟩⟩, ?_⟩
  intro x y
  change IsIso (𝟙 (A.hom a a))
  infer_instance

noncomputable section

open HomologicalComplex

namespace DGCategory

/-- The component of tensor composition obtained by descending from each summand. -/
private def tensorCompDegree (A : DGCategory.{u,v,w} k) (a b c : A.Obj) (n : ℤ) :
    (ModuleCochain.tensor (A.hom b c) (A.hom a b)).X n ⟶ (A.hom a c).X n :=
  mapBifunctorDesc (fun i j h =>
    ModuleCat.ofHom (TensorProduct.lift (A.comp (a := a) (b := b) (c := c) i j n h)))

private theorem tensorCompDegree_apply (A : DGCategory.{u,v,w} k) (a b c : A.Obj)
    (i j n : ℤ) (h : i+j = n) (f : (A.hom b c).X i) (g : (A.hom a b).X j) :
    tensorCompDegree A a b c n (ModuleCochain.tensorInclusion
      (A.hom b c) (A.hom a b) i j n h (f ⊗ₜ[k] g)) = A.comp i j n h f g := by
  unfold tensorCompDegree
  rw [← ModuleCat.comp_apply, ι_mapBifunctorDesc]
  rfl

/-- Composition as a morphism of the ordinary signed tensor complex. -/
def tensorComp (A : DGCategory.{u,v,w} k) (a b c : A.Obj) :
    ModuleCochain.tensor (A.hom b c) (A.hom a b) ⟶ A.hom a c where
  f := tensorCompDegree A a b c
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    apply mapBifunctor.hom_ext
    intro i j hij
    change i + j = n at hij
    unfold tensorCompDegree
    rw [← Category.assoc, ι_mapBifunctorDesc, mapBifunctor.d_eq,
      Preadditive.add_comp, Preadditive.comp_add, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
    rw [mapBifunctor.d₁_eq _ _ _ _ (i₁' := i + 1) rfl j (n+1) (by change i+1+j=n+1; omega),
      mapBifunctor.d₂_eq _ _ _ _ i (i₂' := j + 1) rfl (n+1) (by change i+(j+1)=n+1; omega)]
    change _ = ((1 : ℤˣ) • _) ≫ _ + (i.negOnePow • _) ≫ _
    simp only [one_smul, Linear.units_smul_comp, Category.assoc,
      ι_mapBifunctorDesc]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro g
    change (A.hom a c).d n (n+1) (A.comp i j n hij f g) =
      A.comp (i+1) j (n+1) (by omega) ((A.hom b c).d i (i+1) f) g +
        i.negOnePow • A.comp i (j+1) (n+1) (by omega) f ((A.hom a b).d j (j+1) g)
    exact A.toData.leibniz i j n hij f g

@[simp] theorem tensorComp_tmul (A : DGCategory.{u,v,w} k) (a b c : A.Obj)
    (i j n : ℤ) (h : i+j = n) (f : (A.hom b c).X i) (g : (A.hom a b).X j) :
    (tensorComp A a b c).f n (ModuleCochain.tensorInclusion
      (A.hom b c) (A.hom a b) i j n h (f ⊗ₜ[k] g)) = A.comp i j n h f g :=
  tensorCompDegree_apply A a b c i j n h f g

end DGCategory

theorem tensorComposition : Specs.DerivedFormalization.DG.Basic.TensorComposition.{u,v,w} := by
  intro k _ A a b c
  exact ⟨DGCategory.tensorComp A a b c, DGCategory.tensorComp_tmul A a b c⟩

open Specs.DerivedFormalization.DG.Basic
  (cyclesZero boundariesZero classOf cycleComp cycleId cycleMap h0Hom h0Comp h0Map zeroShort)

private theorem cycleComp_sub_left (A : DGCategory.{u,v,w} k) {a b c : A.Obj}
    (f f' : cyclesZero (A.hom b c)) (g : cyclesZero (A.hom a b)) :
    cycleComp A (f - f') g = cycleComp A f g - cycleComp A f' g := by
  apply Subtype.ext
  change A.comp 0 0 0 rfl (f.val - f'.val) g.val = _
  rw [map_sub, LinearMap.sub_apply]
  rfl

private theorem cycleComp_sub_right (A : DGCategory.{u,v,w} k) {a b c : A.Obj}
    (f : cyclesZero (A.hom b c)) (g g' : cyclesZero (A.hom a b)) :
    cycleComp A f (g - g') = cycleComp A f g - cycleComp A f g' := by
  apply Subtype.ext
  exact map_sub (A.comp 0 0 0 rfl f.val) g.val g'.val

/-- Composition of degree-zero cycles is a boundary if the left factor is a boundary. -/
theorem DGCategory.cycleComp_boundary_left (A : DGCategory.{u,v,w} k) {a b c : A.Obj}
    (f : cyclesZero (A.hom b c)) (g : cyclesZero (A.hom a b))
    (hf : f ∈ boundariesZero (A.hom b c)) :
    cycleComp A f g ∈ boundariesZero (A.hom a c) := by
  obtain ⟨q, rfl⟩ := hf
  have hg : (A.hom a b).d 0 1 g.val = 0 := g.property
  refine ⟨A.comp (-1) 0 (-1) rfl q g.val, Subtype.ext ?_⟩
  change (A.hom a c).d (-1) 0 (A.comp (-1) 0 (-1) rfl q g.val) =
    A.comp 0 0 0 rfl ((A.hom b c).d (-1) 0 q) g.val
  calc
    _ = _ := A.toData.leibniz (-1) 0 (-1) rfl q g.val
    _ = _ := by
      change (A.toData.hom a b).d 0 (0+1) g.val = 0 at hg
      rw [hg, map_zero, smul_zero, add_zero]
      rfl

/-- Composition of degree-zero cycles is a boundary if the right factor is a boundary. -/
theorem DGCategory.cycleComp_boundary_right (A : DGCategory.{u,v,w} k) {a b c : A.Obj}
    (f : cyclesZero (A.hom b c)) (g : cyclesZero (A.hom a b))
    (hg : g ∈ boundariesZero (A.hom a b)) :
    cycleComp A f g ∈ boundariesZero (A.hom a c) := by
  obtain ⟨q, rfl⟩ := hg
  have hf : (A.hom b c).d 0 1 f.val = 0 := f.property
  refine ⟨A.comp 0 (-1) (-1) (zero_add _) f.val q, Subtype.ext ?_⟩
  change (A.hom a c).d (-1) 0 (A.comp 0 (-1) (-1) (zero_add _) f.val q) =
    A.comp 0 0 0 rfl f.val ((A.hom a b).d (-1) 0 q)
  calc
    _ = _ := A.toData.leibniz 0 (-1) (-1) (zero_add _) f.val q
    _ = _ := by
      change (A.toData.hom b c).d 0 (0+1) f.val = 0 at hf
      rw [hf, map_zero, LinearMap.zero_apply, zero_add, Int.negOnePow_zero, one_smul]
      rfl

private theorem classOf_comp_eq (A : DGCategory.{u,v,w} k) {a b c : A.Obj}
    (f f' : cyclesZero (A.hom b c)) (g g' : cyclesZero (A.hom a b))
    (hf : classOf f = classOf f') (hg : classOf g = classOf g') :
    classOf (cycleComp A f g) = classOf (cycleComp A f' g') := by
  calc
    _ = classOf (cycleComp A f' g) := by
      apply (Submodule.Quotient.eq _).2
      rw [← cycleComp_sub_left]
      exact DGCategory.cycleComp_boundary_left A _ _ ((Submodule.Quotient.eq _).1 hf)
    _ = _ := by
      apply (Submodule.Quotient.eq _).2
      rw [← cycleComp_sub_right]
      exact DGCategory.cycleComp_boundary_right A _ _ ((Submodule.Quotient.eq _).1 hg)

theorem h0Composition : Specs.DerivedFormalization.DG.Basic.H0Composition.{u,v,w} := by
  intro k _ A a b c f g
  apply classOf_comp_eq
  · exact Quotient.out_eq _
  · exact Quotient.out_eq _

theorem h0Map_on_classes : Specs.DerivedFormalization.DG.Basic.H0Map.{u,v,w,w'} := by
  intro k _ A B F a b f
  let g : cyclesZero (A.hom a b) := Quotient.out (classOf f)
  have hgf : classOf g = classOf f := Quotient.out_eq _
  obtain ⟨q, hq⟩ := (Submodule.Quotient.eq _).1 hgf
  change classOf (cycleMap F g) = classOf (cycleMap F f)
  apply (Submodule.Quotient.eq _).2
  refine ⟨(F.map a b).f (-1) q, Subtype.ext ?_⟩
  change (B.hom (F.obj a) (F.obj b)).d (-1) 0 ((F.map a b).f (-1) q) =
    (F.map a b).f 0 g.val - (F.map a b).f 0 f.val
  rw [← ModuleCat.comp_apply, (F.map a b).comm, ModuleCat.comp_apply, ← map_sub]
  exact congrArg ((F.map a b).f 0) (congrArg Subtype.val hq)

namespace DGCategory

/-- The object type of the degree-zero cohomology category. -/
@[implicit_reducible] def H0 (A : DGCategory.{u,v,w} k) :=
  Specs.DerivedFormalization.DG.Basic.h0Objects A

@[simp] theorem h0Comp_mk (A : DGCategory.{u,v,w} k) {a b c : A.Obj}
    (f : cyclesZero (A.hom b c)) (g : cyclesZero (A.hom a b)) :
    h0Comp A (classOf f) (classOf g) = classOf (cycleComp A f g) :=
  h0Composition A f g

instance (A : DGCategory.{u,v,w} k) : Category.{v} (H0 A) where
  toCategoryStruct := Specs.DerivedFormalization.DG.Basic.h0CategoryStruct A
  id_comp {a b} f := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    change h0Comp A (classOf f) (classOf (cycleId A a)) = classOf f
    rw [h0Comp_mk]
    congr 1
    apply Subtype.ext
    exact A.toData.comp_id 0 f.val
  comp_id {a b} f := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    change h0Comp A (classOf (cycleId A b)) (classOf f) = classOf f
    rw [h0Comp_mk]
    congr 1
    apply Subtype.ext
    exact A.toData.id_comp 0 f.val
  assoc {a b c d} f g h := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ g
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    change h0Comp A (classOf h) (h0Comp A (classOf g) (classOf f)) =
      h0Comp A (h0Comp A (classOf h) (classOf g)) (classOf f)
    simp only [h0Comp_mk]
    congr 1
    apply Subtype.ext
    exact (A.toData.assoc 0 0 0 h.val g.val f.val).symm

/-- The quotient model used for each `H0` morphism is canonically
isomorphic to Mathlib's zero-degree cohomology object. -/
def _root_.DerivedFormalization.ModuleCochain.h0HomologyIso (C : ModuleCochain.{u,v} k) :
    ModuleCat.of k (h0Hom C) ≅ C.homology 0 :=
  (zeroShort C).moduleCatHomologyIso.symm ≪≫
    (C.homologyIsoSc' (-1) 0 1
      (ComplexShape.prev_eq' _ (show (-1 : ℤ) + 1 = 0 from rfl))
      (ComplexShape.next_eq' _ (show (0 : ℤ) + 1 = 1 from rfl))).symm

instance (A : DGCategory.{u,v,w} k) : Preadditive (H0 A) where
  homGroup a b := inferInstanceAs (AddCommGroup (h0Hom (A.hom a b)))
  add_comp a b c f f' g := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    obtain ⟨f', rfl⟩ := Submodule.Quotient.mk_surjective _ f'
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ g
    change h0Comp A (classOf g) (classOf (f + f')) =
      h0Comp A (classOf g) (classOf f) + h0Comp A (classOf g) (classOf f')
    simp only [h0Comp_mk, ← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact map_add (A.comp 0 0 0 rfl g.val) f.val f'.val
  comp_add a b c f g g' := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ g
    obtain ⟨g', rfl⟩ := Submodule.Quotient.mk_surjective _ g'
    change h0Comp A (classOf (g + g')) (classOf f) =
      h0Comp A (classOf g) (classOf f) + h0Comp A (classOf g') (classOf f)
    simp only [h0Comp_mk, ← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    change A.comp 0 0 0 rfl (g.val + g'.val) f.val = _
    rw [map_add, LinearMap.add_apply]
    rfl

instance (A : DGCategory.{u,v,w} k) : Linear k (H0 A) where
  homModule a b := inferInstanceAs (Module k (h0Hom (A.hom a b)))
  smul_comp a b c r f g := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ g
    change h0Comp A (classOf g) (classOf (r • f)) =
      r • h0Comp A (classOf g) (classOf f)
    simp only [h0Comp_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    exact map_smul (A.comp 0 0 0 rfl g.val) r f.val
  comp_smul a b c f r g := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ g
    change h0Comp A (classOf (r • g)) (classOf f) =
      r • h0Comp A (classOf g) (classOf f)
    simp only [h0Comp_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    change A.comp 0 0 0 rfl (r • g.val) f.val = _
    rw [map_smul, LinearMap.smul_apply]
    rfl

end DGCategory

theorem h0CategoryStructure : Specs.DerivedFormalization.DG.Basic.H0CategoryStructure.{u,v,w} := by
  intro k _ A
  exact ⟨inferInstanceAs (Category (DGCategory.H0 A)), rfl⟩

theorem h0Homology : Specs.DerivedFormalization.DG.Basic.H0Homology.{u,v} := by
  intro k _ C
  exact ⟨C.h0HomologyIso⟩

namespace DGFunctor

variable {A : DGCategory.{u,v,w} k} {B : DGCategory.{u,v,w'} k}

@[simp] theorem h0Map_mk (F : DGFunctor A B) {a b : A.Obj}
    (f : cyclesZero (A.hom a b)) :
    h0Map F (classOf f) = classOf (cycleMap F f) :=
  h0Map_on_classes F f

/-- The induced functor on degree-zero cohomology categories. -/
def H0 (F : DGFunctor A B) : DGCategory.H0 A ⥤ DGCategory.H0 B where
  obj := F.obj
  map := h0Map F
  map_id a := by
    change h0Map F (classOf (cycleId A a)) = classOf (cycleId B (F.obj a))
    rw [h0Map_mk]
    congr 1
    apply Subtype.ext
    exact F.map_id a
  map_comp f g := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ g
    change h0Map F (h0Comp A (classOf g) (classOf f)) =
      h0Comp B (h0Map F (classOf g)) (h0Map F (classOf f))
    simp only [DGCategory.h0Comp_mk, h0Map_mk]
    congr 1
    apply Subtype.ext
    exact F.map_comp 0 0 0 rfl g.val f.val

instance (F : DGFunctor A B) : (H0 F).Additive where
  map_add := by
    intro a b f g
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ g
    change h0Map F (classOf (f + g)) = h0Map F (classOf f) + h0Map F (classOf g)
    simp only [h0Map_mk, ← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact ((F.map a b).f 0).hom.map_add f.val g.val

instance (F : DGFunctor A B) : Functor.Linear k (H0 F) where
  map_smul := by
    intro a b f r
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    change h0Map F (classOf (r • f)) = r • h0Map F (classOf f)
    simp only [h0Map_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    exact ((F.map a b).f 0).hom.map_smul r f.val

/-- A DG functor is a quasi-equivalence if it is locally a quasi-isomorphism
and induces an essentially surjective functor on degree-zero cohomology. -/
def IsQuasiEquivalence (F : DGFunctor A B) : Prop :=
  Specs.DerivedFormalization.DG.Basic.quasiEquivalence F

theorem isQuasiEquivalence_iff (F : DGFunctor A B) :
    IsQuasiEquivalence F ↔ (∀ a b, QuasiIso (F.map a b)) ∧ (H0 F).EssSurj := by
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    constructor
    intro b
    obtain ⟨a, f, g, h₁, h₂⟩ := h b
    exact ⟨a, ⟨⟨f, g, h₂, h₁⟩⟩⟩
  · intro h b
    obtain ⟨a, ⟨e⟩⟩ := h.mem_essImage b
    exact ⟨a, e.hom, e.inv, e.inv_hom_id, e.hom_inv_id⟩

end DGFunctor

theorem h0FunctorStructure : Specs.DerivedFormalization.DG.Basic.H0FunctorStructure.{u,v,w,w'} := by
  intro k _ A B F
  exact ⟨_, _, DGFunctor.H0 F, rfl, rfl, HEq.rfl⟩

end

end DerivedFormalization
