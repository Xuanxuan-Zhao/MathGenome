import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AcyclicTermComparison

/-! HA-R09 values and connecting maps. Computation uses the actual total
derived comparison on every ordinary resolution. The degree-zero natural
isomorphisms follow from preservation of endpoint kernels or cokernels.
The boundaries are induced by the distinguished triangles of stalk sequences. -/
noncomputable section
set_option linter.checkUnivs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

namespace AdvancedHomologicalAlgebra.ClassicalDerivedValues

theorem rightComputation :
    rightComputationType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ F _ X I hIb i hi hI n
  let XI : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj X, 0, inferInstance⟩
  let II : CochainComplex.Plus A := ⟨I, 0, hIb⟩
  let ii : XI ⟶ II := (CochainComplex.plus A).homMk i
  obtain ⟨e, he⟩ := TotalRightDerivedFunctor.computesReplacement A B F XI II ii hi hI
  exact ⟨(DerivedCategory.Plus.homologyFunctor B (n : ℤ)).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors B (n : ℤ)).app
      ((F.mapHomologicalComplex (.up ℤ)).obj I)⟩

theorem leftComputation :
    leftComputationType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ hA hB F _ R X P hPb p hp hP n
  let PP : KMinus A := ⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, 0, hPb⟩
  let pp : PP ⟶ minusStalkValue X :=
    (minus A).homMk ((HomotopyCategory.quotient A (.up ℤ)).map p)
  have hpp : WMinus A pp := by
    change HomotopyCategory.quasiIso A (.up ℤ) ((HomotopyCategory.quotient A (.up ℤ)).map p)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff p).mpr hp
  obtain ⟨e, he, he'⟩ := TotalLeftDerivedFunctor.computation A B hA hB F R
    PP (minusStalkValue X) pp hP hpp
  exact ⟨(DerivedCategory.homologyFunctor B (-(n : ℤ))).mapIso
      (DerivedCategory.Minus.ι.mapIso e) ≪≫
    (DerivedCategory.homologyFunctorFactorsh B (-(n : ℤ))).app
      ((F.mapHomotopyCategory (.up ℤ)).obj PP.obj) ≪≫
    (HomotopyCategory.homologyFunctorFactors B (.up ℤ) (-(n : ℤ))).app
      ((F.mapHomologicalComplex (.up ℤ)).obj P)⟩

theorem rightInjectiveVanishing :
    rightInjectiveVanishingType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ F _ X hX n
  let K := (CochainComplex.singleFunctor A 0).obj X
  obtain ⟨e⟩ := rightComputation A B F X K (𝟙 K)
    (by infer_instance) (fun q => by dsimp [K]; infer_instance) (n + 1)
  let e' := (HomologicalComplex.homologyFunctor B (.up ℤ) ((n + 1 : ℕ) : ℤ)).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X)
  exact (e ≪≫ e').isZero_iff.mpr
    (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 (F.obj X) _ (by omega))

theorem leftProjectiveVanishing :
    leftProjectiveVanishingType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ hA hB F _ R X hX n
  let K := (CochainComplex.singleFunctor A 0).obj X
  obtain ⟨e⟩ := leftComputation A B hA hB F R X K (𝟙 K)
    (by infer_instance) (fun q => by dsimp [K]; infer_instance) (n + 1)
  let e' := (HomologicalComplex.homologyFunctor B (.up ℤ) (-((n + 1 : ℕ) : ℤ))).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X)
  exact (e ≪≫ e').isZero_iff.mpr
    (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 (F.obj X) _ (by omega))

section Boundaries
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T)

def plusTriangleMap : plusTriangle A hS ⟶ plusTriangle A hT where
  hom₁ := (DerivedCategory.Plus.singleFunctor A 0).map f.τ₁
  hom₂ := (DerivedCategory.Plus.singleFunctor A 0).map f.τ₂
  hom₃ := (DerivedCategory.Plus.singleFunctor A 0).map f.τ₃
  comm₁ := by simpa [plusTriangle, ← Functor.map_comp] using (congrArg
      (DerivedCategory.Plus.singleFunctor A 0).map f.comm₁₂.symm)
  comm₂ := by simpa [plusTriangle, ← Functor.map_comp] using (congrArg
      (DerivedCategory.Plus.singleFunctor A 0).map f.comm₂₃.symm)
  comm₃ := by
    apply DerivedCategory.Plus.ι.map_injective
    rw [← cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor A 0).obj T.X₁))]
    simp only [Functor.map_comp, Category.assoc]
    erw [Functor.commShiftIso_hom_naturality]
    simpa [plusTriangle, Category.assoc, DerivedCategory.Plus.singleFunctor,
      DerivedCategory.Plus.singleFunctors, SingleFunctors.lift, ObjectProperty.lift] using
      (ShortComplex.ShortExact.singleTriangle.map hS hT f).comm₃

def minusTriangleMap : minusTriangle A hS ⟶ minusTriangle A hT where
  hom₁ := (minusSingle A).map f.τ₁
  hom₂ := (minusSingle A).map f.τ₂
  hom₃ := (minusSingle A).map f.τ₃
  comm₁ := by simpa [minusTriangle, ← Functor.map_comp] using (congrArg (minusSingle A).map f.comm₁₂.symm)
  comm₂ := by simpa [minusTriangle, ← Functor.map_comp] using (congrArg (minusSingle A).map f.comm₂₃.symm)
  comm₃ := by
    apply DerivedCategory.Minus.ι.map_injective
    rw [← cancel_mono ((DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app
      ((minusSingle A).obj T.X₁))]
    simp only [Functor.map_comp, Category.assoc]
    erw [Functor.commShiftIso_hom_naturality]
    simpa [minusTriangle, Category.assoc, minusSingle, ObjectProperty.lift] using
      (ShortComplex.ShortExact.singleTriangle.map hS hT f).comm₃
lemma plusTriangle_distinguished :
    plusTriangle A hS ∈ distTriang (DerivedCategory.Plus A) := by
  change DerivedCategory.Plus.ι.mapTriangle.obj (plusTriangle A hS) ∈
    distTriang (DerivedCategory A)
  let e : DerivedCategory.Plus.ι.mapTriangle.obj (plusTriangle A hS) ≅ hS.singleTriangle :=
    Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [plusTriangle, DerivedCategory.Plus.singleFunctor,
        DerivedCategory.Plus.singleFunctors, SingleFunctors.lift, ObjectProperty.lift])
      (by simp [plusTriangle, DerivedCategory.Plus.singleFunctor,
        DerivedCategory.Plus.singleFunctors, SingleFunctors.lift, ObjectProperty.lift])
      (by simp [plusTriangle, Category.assoc, DerivedCategory.Plus.singleFunctor,
        DerivedCategory.Plus.singleFunctors, SingleFunctors.lift, ObjectProperty.lift])
  exact Pretriangulated.isomorphic_distinguished _ hS.singleTriangle_distinguished _ e

lemma minusTriangle_distinguished :
    minusTriangle A hS ∈ distTriang (DerivedCategory.Minus A) := by
  change DerivedCategory.Minus.ι.mapTriangle.obj (minusTriangle A hS) ∈
    distTriang (DerivedCategory A)
  let e : DerivedCategory.Minus.ι.mapTriangle.obj (minusTriangle A hS) ≅ hS.singleTriangle :=
    Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [minusTriangle, minusSingle, ObjectProperty.lift])
      (by simp [minusTriangle, minusSingle, ObjectProperty.lift])
      (by simp [minusTriangle, Category.assoc, minusSingle, ObjectProperty.lift])
  exact Pretriangulated.isomorphic_distinguished _ hS.singleTriangle_distinguished _ e

end Boundaries

theorem rightConnectingNatural :
    rightConnectingNaturalType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ F _ S T hS hT f n
  exact (DerivedCategory.Plus.homologyFunctor B 0).homologySequenceδ_naturality
    (F.rightDerivedFunctorPlus.mapTriangle.map (plusTriangleMap hS hT f))
    (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)

theorem leftConnectingNatural :
    leftConnectingNaturalType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ hA hB F _ R S T hS hT f n
  letI := R.commShift
  exact (DerivedCategory.homologyFunctor B 0).homologySequenceδ_naturality
    ((R.functor ⋙ DerivedCategory.Minus.ι).mapTriangle.map (minusTriangleMap hS hT f))
    (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)

theorem rightZero :
    rightZeroType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ F _ _
  have (X : A) : IsIso ((rightDegreeZeroUnit F).app X) := by
    have : CochainComplex.IsStrictlyGE (plusStalkValue X).obj.as 0 := by
      change ((CochainComplex.singleFunctor A 0).obj X).IsStrictlyGE 0
      infer_instance
    haveI : IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map
        (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X))) :=
      AcyclicTermComparison.rightComparison_lowest_degree_homotopy F (plusStalkValue X) 0
    simp only [rightDegreeZeroUnit, NatTrans.comp_app, isoWhiskerLeft_inv, whiskerLeft_app,
      whiskerRight_app, Functor.map_comp, associator_inv_app, Category.id_comp]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

theorem leftZero :
    leftZeroType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ hA hB F _ R _
  have (X : A) : IsIso ((leftDegreeZeroCounit F R).app X) := by
    have : CochainComplex.IsStrictlyLE (minusStalkValue X).obj.as 0 := by
      change ((CochainComplex.singleFunctor A 0).obj X).IsStrictlyLE 0
      infer_instance
    let stalk : A ⥤ KMinus A :=
      (minus A).lift (HomotopyCategory.singleFunctor A 0)
        (fun Y => (minusStalkValue Y).property)
    haveI : IsIso ((DerivedCategory.homologyFunctor B 0).map
        (DerivedCategory.Minus.ι.map (R.counit.app (stalk.obj X)))) :=
      AcyclicTermComparison.leftComparison_highest_degree F R (minusStalkValue X) 0
    simp only [leftDegreeZeroCounit, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerRight_app,
      whiskerLeft_app, Functor.map_comp, associator_hom_app, associator_inv_app, Category.id_comp]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The value on an object is the canonical one used in HA-R08. -/
lemma rightValue_obj_eq {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (n : ℕ) (X : A) :
    (rightValue F n).obj X = rightDerivedObjectValue F n X := rfl

lemma leftValue_obj_eq {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [(minus A).IsTriangulated] [(minus B).IsTriangulated]
    (F : A ⥤ B) [F.Additive] (R : ExactLeftData.{u, v, u', v', w, w'} F)
    (n : ℕ) (X : A) :
    (leftValue F R n).obj X = leftDerivedObjectValue F R n X := rfl

end AdvancedHomologicalAlgebra.ClassicalDerivedValues
