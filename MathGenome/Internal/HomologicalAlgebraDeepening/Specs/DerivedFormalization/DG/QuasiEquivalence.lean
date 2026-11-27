import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.MoritaCriterion

open CategoryTheory
open _root_.DerivedFormalization

universe u v w z

namespace Specs.DerivedFormalization.DG.QuasiEquivalence

open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance)
open DerivedBimoduleAdjunction (DerivedAdjunctionData LocalizedFunctor SignedModels)

noncomputable section

variable {k : Type u} [CommRing k]

/-- Transport the maps of a dg functor along the same coefficient lift on both categories. -/
def liftFunctor {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,z} k}
    (F : DGFunctorModel A B) :
    DGFunctorModel (AmbientDerived.category.{u,v,w,z} A) (AmbientDerived.category.{u,v,z,w} B) where
  obj := F.obj
  map a b := ((ModuleCat.uliftFunctor.{max w z,v} k).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (F.map a b)
  map_id a := ULift.ext (F.map_id a)
  map_comp i j n h f g := ULift.ext (F.map_comp i j n h f.down g.down)

/-- Restriction precomposes the action and evaluates each component at the image object. -/
def restriction {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,z} k}
    (F : DGFunctorModel A B) : RightDGModuleModel B ⥤ RightDGModuleModel A where
  obj M :=
    { complex := fun a => M.complex (F.obj a)
      act := fun i j n h => (M.act i j n h).compl₂ ((F.map _ _).f j).hom
      act_id := by
        intro a i x
        change M.act i 0 i _ x ((F.map a a).f 0 (A.id a)) = x
        rw [F.map_id, M.act_id]
      act_assoc := by
        intro a b c i j l x f g
        change M.act (i+j) l _ _ (M.act i j _ _ x ((F.map b c).f j f))
            ((F.map a b).f l g) =
          M.act i (j+l) _ _ x ((F.map a c).f (j+l) (A.comp j l _ rfl f g))
        rw [F.map_comp, M.act_assoc]
      leibniz := by
        intro a b i j n h x f
        change (M.complex (F.obj a)).d n (n+1)
            (M.act i j n h x ((F.map a b).f j f)) =
          M.act (i+1) j (n+1) _ ((M.complex (F.obj b)).d i (i+1) x) ((F.map a b).f j f) +
            i.negOnePow • M.act i (j+1) (n+1) _ x ((F.map a b).f (j+1) ((A.hom a b).d j (j+1) f))
        rw [M.leibniz]
        have hcomm := congrArg (fun q => q f) ((F.map a b).comm j (j+1))
        simp only [ModuleCat.comp_apply] at hcomm
        rw [hcomm] }
  map f :=
    { app := fun a => f.app (F.obj a)
      comm_act := fun i j n h x g => f.comm_act i j n h x ((F.map _ _).f j g) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The coefficient lift within an already adequate universe has the canonical
degreewise linear isomorphism. -/
def upIso (C : ModuleCochain.{u,max v z} k) :
    C ≅ Yoneda.liftComplex.{u,max v z,z} C :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => ULift.moduleEquiv.symm.toModuleIso)
    (fun _ _ _ => rfl)

/-- Ambient Yoneda acts by the inverse of enriched evaluation on each arrow. -/
def IsYoneda {B : DGCategoryModel.{u,max v z,z} k}
    (Y : DGFunctorModel B (HomComplex.dgModuleCategory B)) : Prop :=
  Y.obj = Yoneda.representable (A := B) ∧
    ∃ E : Yoneda.EvaluationFamily B, Yoneda.EvaluationLaws E ∧
      ∀ a b : B.Obj,
        HEq (Y.map a b) ((upIso (B.hom a b)).hom ≫
          (E a (Yoneda.representable (A := B) b)).inv)

/-- The left action on the graph bimodule is the dg functor followed by Yoneda. -/
def graph {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
    (F : DGFunctorModel A B) (Y : DGFunctorModel B (HomComplex.dgModuleCategory B)) :
    BalancedTensor.bimodule A B where
  obj a := Y.obj (F.obj a)
  map a b :=
    { f := fun n => ((F.map a b ≫ Y.map (F.obj a) (F.obj b)).f n).hom
      comm := by
        intro n x
        let f := F.map a b ≫ Y.map (F.obj a) (F.obj b)
        change ((A.hom a b).d n (n+1) ≫ f.f (n+1)).hom x =
          (f.f n ≫ ((HomComplex.dgModuleCategory B).hom _ _).d n (n+1)).hom x
        exact congrArg (fun q => q.hom x) (f.comm n (n+1)).symm }
  map_id a := by
    change (Y.map (F.obj a) (F.obj a)).f 0 ((F.map a a).f 0 (A.id a)) = _
    rw [F.map_id, Y.map_id]
  map_comp := by
    intro a b c i j n h f g
    change (Y.map (F.obj a) (F.obj c)).f n
      ((F.map a c).f n (A.comp i j n h f g)) = _
    rw [F.map_comp, Y.map_comp]
    rfl

/-- At the common adequate bound, the functor remains a quasi-equivalence.
Derived tensor with its graph is an equivalence whose inverse descends strict
restriction. The tensor is computed on K-projective replacements. -/
def DerivedQuasiEquivalence : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,z} k}
    (F : DGFunctorModel A B), Basic.quasiEquivalence F →
    let A' := AmbientDerived.category.{u,v,w,z} A
    let B' := AmbientDerived.category.{u,v,z,w} B
    let F' := liftFunctor F
    Basic.quasiEquivalence F' ∧
    ∀ (hA : HomotopyCategoryLaws A') (hB : HomotopyCategoryLaws B'),
      letI := Derived.homotopyCategory A' hA
      letI := Derived.homotopyCategory B' hB
      letI := derivedCategoryInstance A' hA
      letI := derivedCategoryInstance B' hB
      ∃ (Y : DGFunctorModel B' (HomComplex.dgModuleCategory B'))
        (_ : IsYoneda.{u,max v w,z} Y)
        (m : SignedModels.{u,v,w,z} (graph.{u,v,w,z} F' Y))
        (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB)
        (R : LocalizedFunctor hB hA (restriction F')),
        d.Realizes m.adjunction ∧ d.ComputesRepresentatives ∧ d.IsExact ∧
        ∃ e : d.tensor ⊣ R.derived, IsIso e.unit ∧ IsIso e.counit

end

end Specs.DerivedFormalization.DG.QuasiEquivalence
