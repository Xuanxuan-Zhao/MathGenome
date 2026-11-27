import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.OrdinaryStalkComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.OrdinaryComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v t w

namespace DerivedFormalization.Affine.OrdinaryStalkComparison

open Specs.DerivedFormalization.Affine.OrdinaryStalkComparison
open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.DG.CoefficientLiftComparison (restrictModule restrictMap)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom HomotopyEquation homComplex)
open Specs.DerivedFormalization.DG.OrdinaryComplex
  (representedAlgebra representedFunctor degreeZeroCategory scalar)
open Specs.DerivedFormalization.Affine.CotangentComplex (oneObject)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {R : Type v} [CommRing R] [Algebra k R]

set_option quotPrecheck false

set_option hygiene false in
local notation "Lifted" => transported.{u,v,t} k R
set_option hygiene false in
local notation "LiftedRing" => ULift.{t} R

private abbrev ringRepresentative : R ≃+* LiftedRing := ULift.ringEquiv.symm

local instance : Algebra k LiftedRing := representedAlgebra (ringRepresentative (R := R))

set_option hygiene false in
local notation "Stalk" => degreeZeroCategory k LiftedRing

local instance : CommRing (Lifted).toCommDGAlgebra.DegreeZero :=
  CommDGAlgebra.instCommRingDegreeZero _
local instance : Algebra k (Lifted).toCommDGAlgebra.DegreeZero :=
  CommDGAlgebra.instAlgebraDegreeZero _

private def scalarIso : R ≃ₐ[k] (Lifted).toCommDGAlgebra.DegreeZero where
  toFun := ULift.up
  invFun := ULift.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one (R := k) (A := (Lifted).toCommDGAlgebra.DegreeZero)]
    exact congrArg ULift.up (Algebra.algebraMap_eq_smul_one c)

omit [CharZero k] in
private theorem stalkSubsingleton (i : ℤ) (hi : i ≠ 0) :
    Subsingleton (((Stalk).hom () ()).X i) :=
  ⟨fun x y => Subtype.ext ((x.property hi).trans (y.property hi).symm)⟩

private theorem transportedSubsingleton (i : ℤ) (hi : i ≠ 0) :
    Subsingleton ((Lifted).complex.X i) := by
  have hs := ModuleCat.subsingleton_of_isZero
    (isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of k R) i hi)
  exact ⟨fun x y => ULift.ext (hs.elim x.down y.down)⟩

/-- The identity on ring elements in degree zero and the unique isomorphism
between zero terms in each other degree. -/
private def arrowTerm (i : ℤ) : (Lifted).complex.X i ≃ₗ[k] ((Stalk).hom () ()).X i := by
  by_cases hi : i = 0
  · subst i
    refine
      { toFun := fun x => scalar k LiftedRing x
        invFun := fun x => x.val
        left_inv := fun _ => rfl
        right_inv := fun _ => Subtype.ext rfl
        map_add' := fun _ _ => Subtype.ext rfl
        map_smul' := ?_ }
    intro c x
    apply Subtype.ext
    simp only [RingHom.id_apply]
    change (ULift.up (c • (x.down : R)) : LiftedRing) =
      (algebraMap k LiftedRing c) * (show LiftedRing from x)
    exact congrArg ULift.up (Algebra.smul_def (R := k) (A := R) c (x.down : R))
  · exact
      { toFun := fun _ => 0
        invFun := fun _ => 0
        left_inv := fun _ => (transportedSubsingleton i hi).elim _ _
        right_inv := fun _ => (stalkSubsingleton i hi).elim _ _
        map_add' := fun _ _ => (add_zero _).symm
        map_smul' := fun _ _ => (smul_zero _).symm }

private theorem transported_d (i j : ℤ) : (Lifted).complex.d i j = 0 := by
  change (ModuleCat.uliftFunctor.{t,v} k).map
    ((NonpositiveCDGA.ordinaryComplex (CommAlgCat.of k R)).d i j) = 0
  rw [single_obj_d, Functor.map_zero]

private theorem arrowTerm_zero (x : (Lifted).complex.X 0) :
    arrowTerm 0 x = scalar k LiftedRing x := by
  unfold arrowTerm
  rfl

private theorem arrowTerm_mul (i j n : ℤ) (h : i + j = n)
    (x : (Lifted).complex.X i) (y : (Lifted).complex.X j) :
    arrowTerm n ((Lifted).mul i j n h x y) =
      (Stalk).comp i j n h (arrowTerm i x) (arrowTerm j y) := by
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · subst i j
      have hn : 0 = n := h
      cases hn
      rw [arrowTerm_zero, arrowTerm_zero, arrowTerm_zero]
      apply Subtype.ext
      rfl
    · rw [(transportedSubsingleton j hj).elim y 0]
      simp
  · rw [(transportedSubsingleton i hi).elim x 0]
    simp

private abbrev arrowIso : (Lifted).complex ≅ (Stalk).hom () () :=
  Hom.isoOfComponents (fun i => (arrowTerm i).toModuleIso) (by
    intro i j _
    change (arrowTerm i).toModuleIso.hom ≫ 0 =
      (Lifted).complex.d i j ≫ (arrowTerm j).toModuleIso.hom
    rw [transported_d]
    exact Limits.comp_zero.trans Limits.zero_comp.symm)

private abbrev toStalk : DGFunctorModel (oneObject Lifted) Stalk where
  obj := id
  map _ _ := arrowIso.hom
  map_id _ := by
    change arrowTerm 0 (Lifted).one = scalar k LiftedRing 1
    rw [arrowTerm_zero]
    rfl
  map_comp i j n h x y := arrowTerm_mul i j n h x y

private abbrev fromStalk : DGFunctorModel Stalk (oneObject Lifted) where
  obj := id
  map _ _ := arrowIso.inv
  map_id _ := by
    apply (arrowTerm 0).injective
    change arrowTerm 0 ((arrowTerm 0).symm (scalar k LiftedRing 1)) =
      arrowTerm 0 (Lifted).one
    rw [LinearEquiv.apply_symm_apply, arrowTerm_zero]
    rfl
  map_comp i j n h x y := by
    apply (arrowTerm n).injective
    change arrowTerm n ((arrowTerm n).symm ((Stalk).comp i j n h x y)) =
      arrowTerm n ((Lifted).mul i j n h ((arrowTerm i).symm x) ((arrowTerm j).symm y))
    rw [LinearEquiv.apply_symm_apply, arrowTerm_mul,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Pullback of the action, with the same term complexes and strict maps. -/
private abbrev restrictAction {C D : DGCategoryModel.{u,w,0} k}
    (F : DGFunctorModel C D) : RightDGModuleModel D ⥤ RightDGModuleModel C where
  obj := restrictModule F
  map := restrictMap F
  map_id _ := RightDGModuleModel.hom_ext fun _ => rfl
  map_comp _ _ := RightDGModuleModel.hom_ext fun _ => rfl

private abbrev toTransportedModule : RightDGModuleModel Stalk ⥤ (Lifted).Module :=
  restrictAction toStalk

private abbrev toStalkModule : (Lifted).Module ⥤ RightDGModuleModel Stalk :=
  restrictAction fromStalk

private def arrowEquivalence : RightDGModuleModel Stalk ≌ (Lifted).Module where
  functor := toTransportedModule
  inverse := toStalkModule
  unitIso := NatIso.ofComponents (fun M =>
    { hom := ⟨fun a => 𝟙 (M.complex a), by
        intro a b i j n h x z
        change M.act (a := a) (b := b) i j n h x z =
          M.act i j n h x (arrowTerm j ((arrowTerm j).symm z))
        rw [LinearEquiv.apply_symm_apply]⟩
      inv := ⟨fun a => 𝟙 (M.complex a), by
        intro a b i j n h x z
        change M.act (a := a) (b := b) i j n h x (arrowTerm j ((arrowTerm j).symm z)) =
          M.act i j n h x z
        rw [LinearEquiv.apply_symm_apply]⟩
      hom_inv_id := RightDGModuleModel.hom_ext fun _ => Category.comp_id _
      inv_hom_id := RightDGModuleModel.hom_ext fun _ => Category.comp_id _ }) (by
    intro M N f
    apply RightDGModuleModel.hom_ext
    intro a
    exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun M =>
    { hom := ⟨fun a => 𝟙 (M.complex a), by
        intro a b i j n h x z
        change M.act (a := a) (b := b) i j n h x ((arrowTerm j).symm (arrowTerm j z)) =
          M.act i j n h x z
        rw [LinearEquiv.symm_apply_apply]⟩
      inv := ⟨fun a => 𝟙 (M.complex a), by
        intro a b i j n h x z
        change M.act (a := a) (b := b) i j n h x z =
          M.act i j n h x ((arrowTerm j).symm (arrowTerm j z))
        rw [LinearEquiv.symm_apply_apply]⟩
      hom_inv_id := RightDGModuleModel.hom_ext fun _ => Category.comp_id _
      inv_hom_id := RightDGModuleModel.hom_ext fun _ => Category.comp_id _ }) (by
    intro M N f
    apply RightDGModuleModel.hom_ext
    intro a
    exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp M := RightDGModuleModel.hom_ext fun _ => Category.comp_id _

/-- Right linearity along the new arrows is equivalent to right linearity along
the old arrows, with the same underlying homogeneous maps. -/
private def transportedGraded (M N : RightDGModuleModel Stalk) (q : ℤ) :
    gradedHom M N q ≃ₗ[k] gradedHom (toTransportedModule.obj M) (toTransportedModule.obj N) q where
  toFun f := ⟨f.val, by
    intro a b i j n ir nr h hi hn x z
    exact f.property (a := a) (b := b) i j n ir nr h hi hn x (arrowTerm j z)⟩
  invFun f := ⟨f.val, by
    intro a b i j n ir nr h hi hn x z
    have hf := f.property (a := a) (b := b) i j n ir nr h hi hn x ((arrowTerm j).symm z)
    change (f.val a).v n nr hn (M.act i j n h x (arrowTerm j ((arrowTerm j).symm z))) =
      N.act ir j nr (by omega) ((f.val b).v i ir hi x) (arrowTerm j ((arrowTerm j).symm z)) at hf
    simpa only [LinearEquiv.apply_symm_apply] using hf⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private def transportedHom (M N : RightDGModuleModel Stalk) :
    homComplex M N ≅ homComplex (toTransportedModule.obj M) (toTransportedModule.obj N) :=
  Hom.isoOfComponents (fun q => (transportedGraded M N q).toModuleIso) (by
    intro i j _
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact Subtype.ext rfl)

/-- Compare homogeneous maps into an arbitrary target over the A08 algebra. -/
private def gradedIntoTransported (M : RightDGModuleModel Stalk) (N : (Lifted).Module) (q : ℤ) :
    gradedHom M (toStalkModule.obj N) q ≃ₗ[k] gradedHom (toTransportedModule.obj M) N q where
  toFun f := ⟨f.val, by
    intro a b i j n ir nr h hi hn x z
    have hf := f.property (a := a) (b := b) i j n ir nr h hi hn x (arrowTerm j z)
    change (f.val a).v n nr hn (M.act i j n h x (arrowTerm j z)) =
      N.act ir j nr (by omega) ((f.val b).v i ir hi x) ((arrowTerm j).symm (arrowTerm j z)) at hf
    change (f.val a).v n nr hn (M.act i j n h x (arrowTerm j z)) =
      N.act ir j nr (by omega) ((f.val b).v i ir hi x) z
    rw [LinearEquiv.symm_apply_apply] at hf
    exact hf⟩
  invFun f := ⟨f.val, by
    intro a b i j n ir nr h hi hn x z
    have hf := f.property (a := a) (b := b) i j n ir nr h hi hn x ((arrowTerm j).symm z)
    change (f.val a).v n nr hn (M.act i j n h x (arrowTerm j ((arrowTerm j).symm z))) =
      N.act ir j nr (by omega) ((f.val b).v i ir hi x) ((arrowTerm j).symm z) at hf
    change (f.val a).v n nr hn (M.act i j n h x z) =
      N.act ir j nr (by omega) ((f.val b).v i ir hi x) ((arrowTerm j).symm z)
    rw [LinearEquiv.apply_symm_apply] at hf
    exact hf⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private def homIntoTransported (M : RightDGModuleModel Stalk) (N : (Lifted).Module) :
    homComplex M (toStalkModule.obj N) ≅ homComplex (toTransportedModule.obj M) N :=
  Hom.isoOfComponents (fun q => (gradedIntoTransported M N q).toModuleIso)
    (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact Subtype.ext rfl)

private theorem homotopyOnTransported {M N : RightDGModuleModel Stalk} (f g : M ⟶ N) :
    (∃ z : gradedHom M N (-1), HomotopyEquation f g z) ↔
      ∃ z : gradedHom (toTransportedModule.obj M) (toTransportedModule.obj N) (-1),
        HomotopyEquation (toTransportedModule.map f) (toTransportedModule.map g) z :=
  ⟨fun ⟨z, hz⟩ => ⟨transportedGraded M N (-1) z, hz⟩,
    fun ⟨z, hz⟩ => ⟨(transportedGraded M N (-1)).symm z, hz⟩⟩

open Specs.DerivedFormalization.DG.KProjective (isKProjective)

private theorem projectiveOnTransported (M : RightDGModuleModel Stalk) :
    isKProjective M ↔ isKProjective (toTransportedModule.obj M) := by
  constructor
  · intro h N hN i
    exact (h (toStalkModule.obj N) hN i).of_iso (homIntoTransported M N)
  · intro h N hN i
    exact (h (toTransportedModule.obj N) hN i).of_iso (transportedHom M N).symm

private def comparisonAt : Comparison.{u,v,t} k R := by
  let e : R ≃+* LiftedRing := ringRepresentative
  let F := representedFunctor (k := k) e
  obtain ⟨hEquivalence, hAction, _, _, _, hMaps⟩ :=
    DerivedFormalization.OrdinaryComplex.representedRingComparison.{u,max v t,v} k R LiftedRing e
  letI : F.IsEquivalence := hEquivalence
  let E := F.asEquivalence.trans arrowEquivalence
  refine
    { scalar := scalarIso
      scalar_apply := fun _ => rfl
      strict := E
      additive := ?_
      terms := Iso.refl _
      action := ?_
      homotopy := ?_
      quasiIso := ?_
      projective := ?_ }
  · intro X Y f g
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · intro X i r x
    change (F.obj X).act (a := ()) (b := ()) i 0 i (add_zero i) x (arrowTerm 0 (ULift.up r)) = r • x
    exact (congrArg ((F.obj X).act (a := ()) (b := ()) i 0 i (add_zero i) x)
      (arrowTerm_zero (ULift.up r))).trans (hAction X i r x)
  · intro X Y f g
    exact (DerivedFormalization.OrdinaryComplex.representedHomotopyComparison.{u,max v t,v}
      k R LiftedRing e f g).trans (homotopyOnTransported (F.map f) (F.map g))
  · intro X Y f
    exact (hMaps f).1
  · intro X
    obtain ⟨_, _, _, _, hP⟩ :=
      DerivedFormalization.OrdinaryComplex.representedHomComparison.{u,max v t,v} k R LiftedRing e
    exact (hP X).trans (projectiveOnTransported (F.obj X))

theorem comparison : ComparisonExists.{u,v,t} := by
  intro k _ _ R _ _
  exact ⟨comparisonAt⟩

end

end DerivedFormalization.Affine.OrdinaryStalkComparison
