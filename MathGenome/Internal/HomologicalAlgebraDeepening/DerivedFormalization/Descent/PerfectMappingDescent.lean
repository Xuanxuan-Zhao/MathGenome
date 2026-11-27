import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.PerfectMappingDescent
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.PerfectHomBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.UnboundedAmitsurDescent
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomModels
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! Faithfully flat descent of perfect-coefficient internal mapping complexes. -/

namespace DerivedFormalization.Descent.PerfectMappingDescent

open CategoryTheory Opposite
open Specs.DerivedFormalization.CochainModels (internalHomValue internalHomMapValue)
open Specs.DerivedFormalization.Cochains (compValue derivedValue qValue)
open Specs.DerivedFormalization.CochainCoefficientLift (liftDFactors)
open Specs.DerivedFormalization.DerivedHomModels (Models rHomValue)
open Specs.DerivedFormalization.Descent.PerfectMappingDescent
open Specs.DerivedFormalization.Descent.PerfectHomBaseChange
  (changeCoefficients comparison extend restrict)
open AmitsurAlgebrasSpec (degree coface)
open AmitsurTotalComplexSpec (rowIndex)
open scoped BigOperators TensorProduct ZeroObject

universe u v w t a
set_option linter.checkUnivs false
set_option linter.style.haveILetI false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

private theorem boundedAbove_kProjective {R : Type u} [CommRing R]
    (K : compValue.{max u a} R) (U : ℤ)
    (hU : ∀ i, U < i → Subsingleton (K.X i))
    (hP : ∀ i, Module.Projective R (K.X i)) : K.IsKProjective := by
  letI : Small.{max u a} R := small_of_injective (f := (ULift.up : R → ULift.{a} R))
    ULift.up_injective
  letI : ∀ i : ℤ, Module.Projective R (K.X i) := hP
  letI : ∀ i : ℤ, Projective (K.X i) := fun i => inferInstance
  letI : K.IsStrictlyLE U := (CochainComplex.isStrictlyLE_iff K U).mpr
    (fun i hi => ModuleCat.isZero_iff_subsingleton.mpr (hU i hi))
  exact CochainComplex.isKProjective_of_projective K U

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable (I : Inputs.{u,w,t} A)

private theorem liftedPerfect :
    perfect.{u,max u v w t} A (P.{u,v,w,t} A I) := by
  obtain ⟨⟨L, U, h⟩, hF, hP⟩ := I.1.unop.property
  let e (i : ℤ) := CochainCoefficientLift.termEquiv.{max u v t} I.1.unop.obj i
  refine ⟨⟨L, U, fun i hi => ?_⟩, fun i => ?_, fun i => ?_⟩
  · letI := h i hi
    exact (e i).symm.injective.subsingleton
  · letI := hF i
    exact Module.Finite.equiv (e i)
  · letI := hP i
    exact Module.Projective.of_equiv' (e i)

theorem globalKProjective : (P.{u,v,w,t} A I).IsKProjective := by
  obtain ⟨⟨_, U, h⟩, _, hP⟩ := liftedPerfect.{u,v,w,t} A I
  exact boundedAbove_kProjective.{u,max v w t} _ U (fun i hi => h i (Or.inr hi)) hP

theorem localKProjective (p : ℕ) : CochainComplex.IsKProjective (localP A B I p) := by
  obtain ⟨⟨_, U, h⟩, _, hP⟩ := liftedPerfect.{u,v,w,t} A I
  apply boundedAbove_kProjective.{max u v,max w t} _ U
  · intro i hi
    letI := h i (Or.inr hi)
    change Subsingleton (degree A B p ⊗[A] (P.{u,v,w,t} A I).X i)
    infer_instance
  · intro i
    letI := hP i
    change Module.Projective (degree A B p) (degree A B p ⊗[A] (P.{u,v,w,t} A I).X i)
    infer_instance

/-- The tensor over A and the restriction of the extended module use the
same action under the identity on the tensor carrier. -/
private def tensorRestrictionIso (S : Type v) [CommRing S] [Algebra A S]
    (M : ModuleCat.{a} A) :
    ModuleCat.of A (S ⊗[A] M) ≅
      (ModuleCat.restrictScalars.{max v a} (algebraMap A S)).obj
        (ModuleCat.of S (S ⊗[A] M)) := by
  let M₁ : ModuleCat.{max v a} A := ModuleCat.of A (S ⊗[A] M)
  let M₂ := (ModuleCat.restrictScalars.{max v a} (algebraMap A S)).obj
    (ModuleCat.of S (S ⊗[A] M))
  let e : M₁ ≃ₗ[A] M₂ :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change r • (x : S ⊗[A] M) = algebraMap A S r • x
        exact (algebraMap_smul S r x).symm }
  exact e.toModuleIso

open AmitsurTotalComplexSpec.Independent in
/-- The column maps are the canonical signed Hom comparisons, restricted to A. -/
def columnIso (p : ℕ) (q : ℤ) :
    cell A B (globalHom.{u,v,w,t} A I) p q ≅ (column A B I p).X q := by
  let h := liftedPerfect.{u,v,w,t} A I
  let S := degree A B p
  let f := comparison S (P.{u,v,w,t} A I) (X.{u,v,w,t} A I)
  letI : IsIso f := homBaseChange_isIso A S _ _ h.1 h.2.1 h.2.2
  exact tensorRestrictionIso A S ((globalHom.{u,v,w,t} A I).X q) ≪≫
    asIso (((restrict.{u,max u v,max w t} A S).map f).f q)

private theorem columnIso_hom_apply (p : ℕ) (q : ℤ)
    (z : AmitsurTotalComplexSpec.Independent.cell A B (globalHom.{u,v,w,t} A I) p q) :
    (columnIso A B I p q).hom z =
      (comparison (degree A B p) (P.{u,v,w,t} A I) (X.{u,v,w,t} A I)).f q z := rfl

private theorem columnIso_vertical (p : ℕ) (q r : ℤ) :
    (columnIso A B I p q).hom ≫ (column A B I p).d q r =
      AmitsurTotalComplexSpec.Independent.vertical A B (globalHom.{u,v,w,t} A I) p q r ≫
        (columnIso A B I p r).hom := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s z
  let f := comparison (degree A B p) (P.{u,v,w,t} A I) (X.{u,v,w,t} A I)
  let H := globalHom.{u,v,w,t} A I
  have h := ConcreteCategory.congr_hom (f.comm q r)
    (show degree A B p ⊗[A] H.X q from s ⊗ₜ[A] z)
  change (column A B I p).d q r ((columnIso A B I p q).hom (s ⊗ₜ[A] z)) =
    (columnIso A B I p r).hom (s ⊗ₜ[A] H.d q r z)
  rw [columnIso_hom_apply, columnIso_hom_apply]
  exact h

private theorem columnIso_coface {p : ℕ} (i : Fin (p + 2)) (q : ℤ) :
    (columnIso A B I p q).hom ≫ (localCoface A B I i).f q =
      ModuleCat.ofHom (TensorProduct.map (coface (A := A) (B := B) i).toLinearMap
        LinearMap.id) ≫ (columnIso A B I (p + 1) q).hom := by
  let S := degree A B p
  let T := degree A B (p + 1)
  let φ : S →ₐ[A] T := coface i
  letI : Algebra S T := φ.toRingHom.toAlgebra
  letI : IsScalarTower A S T := IsScalarTower.of_algHom φ
  have hc := homBaseChange_changeCoefficients A S T φ
    (P.{u,v,w,t} A I) (X.{u,v,w,t} A I)
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s z
  have hq := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hc q)
    (show S ⊗[A] (globalHom.{u,v,w,t} A I).X q from s ⊗ₜ[A] z)
  change (comparison T (P.{u,v,w,t} A I) (X.{u,v,w,t} A I)).f q
      ((changeCoefficients A S T (globalHom.{u,v,w,t} A I)).f q (s ⊗ₜ[A] z)) =
    (localCoface A B I i).f q
      ((comparison S (P.{u,v,w,t} A I) (X.{u,v,w,t} A I)).f q (s ⊗ₜ[A] z)) at hq
  rw [changeCoefficients_apply A S T φ (globalHom.{u,v,w,t} A I) q s z] at hq
  change (localCoface A B I i).f q ((columnIso A B I p q).hom (s ⊗ₜ[A] z)) =
    (columnIso A B I (p + 1) q).hom (φ s ⊗ₜ[A] z)
  rw [columnIso_hom_apply, columnIso_hom_apply]
  exact hq.symm

private theorem columnIso_horizontal (p : ℕ) (q : ℤ) :
    (columnIso A B I p q).hom ≫
        (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (localCoface A B I i).f q) =
      AmitsurTotalComplexSpec.Independent.horizontal A B (globalHom.{u,v,w,t} A I) p q ≫
        (columnIso A B I (p + 1) q).hom := by
  simp only [AmitsurTotalComplexSpec.Independent.horizontal, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, columnIso_coface]

private theorem columnIso_diagonal (n : ℤ) (p : ℕ) :
    (columnIso A B I p (rowIndex n p)).hom ≫ diagonalHorizontal A B I n p =
      AmitsurTotalComplexSpec.Independent.diagonalHorizontal A B (globalHom.{u,v,w,t} A I) n p ≫
        (columnIso A B I (p + 1) (rowIndex (n + 1) (p + 1))).hom := by
  unfold diagonalHorizontal AmitsurTotalComplexSpec.Independent.diagonalHorizontal
  rw [← Category.assoc, columnIso_horizontal, Category.assoc, Category.assoc]
  congr 1
  apply eqToHom_iso_hom_naturality (columnIso A B I (p + 1))
  change rowIndex n p = (n + 1) - (p + 1 : ℕ)
  rw [AmitsurTotalComplexSpec.rowIndex_eq]
  omega

open AmitsurTotalComplexSpec.Independent in
/-- The componentwise comparison on the full diagonal product. -/
def productIso (n : ℤ) :
    term A B (globalHom.{u,v,w,t} A I) n ≅ totalTerm A B I n :=
  (LinearEquiv.piCongrRight fun p => (columnIso A B I p (rowIndex n p)).toLinearEquiv).toModuleIso

open AmitsurTotalComplexSpec.Independent in
private theorem productIso_step (n : ℤ) :
    (productIso A B I n).hom ≫ totalStep A B I n =
      (total A B (globalHom.{u,v,w,t} A I)).d n (n + 1) ≫ (productIso A B I (n + 1)).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext p
  cases p with
  | zero =>
    change (column A B I 0).d n (n + 1) ((columnIso A B I 0 n).hom (x 0)) =
      (columnIso A B I 0 (n + 1)).hom ((total A B (globalHom.{u,v,w,t} A I)).d n (n + 1) x 0)
    rw [total_d_zero]
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (columnIso_vertical A B I 0 n (n + 1))) (x 0)
  | succ p =>
    change diagonalHorizontal A B I n p ((columnIso A B I p (rowIndex n p)).hom (x p)) +
      (-1 : ℤ) ^ (p + 1) • (column A B I (p + 1)).d (rowIndex n (p + 1))
        (rowIndex (n + 1) (p + 1)) ((columnIso A B I (p + 1) (rowIndex n (p + 1))).hom (x (p + 1))) =
      (columnIso A B I (p + 1) (rowIndex (n + 1) (p + 1))).hom
        ((total A B (globalHom.{u,v,w,t} A I)).d n (n + 1) x (p + 1))
    rw [total_d_succ, map_add, map_zsmul]
    congr 1
    · exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (columnIso_diagonal A B I n p)) (x p)
    · exact congrArg ((-1 : ℤ) ^ (p + 1) • ·) (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        (columnIso_vertical A B I (p + 1) (rowIndex n (p + 1)) (rowIndex (n + 1) (p + 1))))
        (x (p + 1)))

theorem totalStep_sq (n : ℤ) : totalStep A B I n ≫ totalStep A B I (n + 1) = 0 := by
  apply (cancel_epi (productIso A B I n).hom).mp
  rw [← Category.assoc, productIso_step, Category.assoc, productIso_step,
    ← Category.assoc, HomologicalComplex.d_comp_d, Limits.zero_comp, Limits.comp_zero]

open AmitsurTotalComplexSpec.Independent in
/-- The comparison from the Amitsur totalization of global Hom to the
product totalization of the local signed Hom models. -/
def totalIso :
    total A B (globalHom.{u,v,w,t} A I) ≅ localTotal A B I (totalStep_sq A B I) :=
  HomologicalComplex.Hom.isoOfComponents (productIso A B I) fun n m h => by
    obtain rfl : n + 1 = m := h
    exact (congrArg ((productIso A B I n).hom ≫ ·)
      (CochainComplex.of_d (totalTerm A B I) (totalStep A B I) n)).trans
      (productIso_step A B I n)

private def homFunctor (R : Type u) [CommRing R] :
    (compValue.{a} R)ᵒᵖ × compValue.{a} R ⥤ compValue.{a} R where
  obj K := internalHomValue K.1.unop K.2
  map f := internalHomMapValue f.1.unop f.2
  map_id K := internalHomMap_id K.1.unop K.2
  map_comp f g := (internalHomMap_comp f.1.unop g.1.unop f.2 g.2).symm

/-- The signed Hom functor on the original inputs after the same-ring lifts. -/
def globalHomFunctor : Inputs.{u,w,t} A ⥤ compValue.{max u v w t} A :=
  (firstLift.{u,v,w,t} A).op.prod (secondLift.{u,v,w,t} A) ⋙ homFunctor A

/-- The local signed Hom functor on the scalar extensions of the lifts. -/
def localHomFunctor (p : ℕ) :
    Inputs.{u,w,t} A ⥤ compValue.{max u v w t} (degree A B p) :=
  (firstLift.{u,v,w,t} A ⋙ extend A (degree A B p)).op.prod
    (secondLift.{u,v,w,t} A ⋙ extend A (degree A B p)) ⋙ homFunctor (degree A B p)

open AmitsurTotalComplexSpec.Independent in
private theorem columnIso_natural {J : Inputs.{u,w,t} A} (f : I ⟶ J) (p : ℕ) (q : ℤ) :
    AmitsurTotalComplexSpec.Independent.tensorMap A B ((globalMap.{u,v,w,t} f).f q) p ≫ (columnIso A B J p q).hom =
      (columnIso A B I p q).hom ≫
        ((restrict.{u,max u v,max w t} A (degree A B p)).map (localMap B f p)).f q := by
  let S := degree A B p
  have h := homBaseChange_natural A S ((firstLift.{u,v,w,t} A).map f.1.unop)
    ((secondLift.{u,v,w,t} A).map f.2)
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s z
  let H := globalHom.{u,v,w,t} A I
  have hq := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom h q)
    (show S ⊗[A] H.X q from s ⊗ₜ[A] z)
  change (columnIso A B J p q).hom (s ⊗ₜ[A] (globalMap.{u,v,w,t} f).f q z) =
    ((restrict.{u,max u v,max w t} A S).map (localMap B f p)).f q
      ((columnIso A B I p q).hom (s ⊗ₜ[A] z))
  rw [columnIso_hom_apply, columnIso_hom_apply]
  exact hq

open AmitsurTotalComplexSpec.Independent in
private def amitsurHomFunctor : Inputs.{u,w,t} A ⥤ compValue.{max u v w t} A :=
  globalHomFunctor.{u,v,w,t} A ⋙ functor.{u,v,max u v w t} A B

/-- The full product totalization, with the maps in both inputs induced
coordinatewise on local signed Hom. -/
def totalFunctor : Inputs.{u,w,t} A ⥤ compValue.{max u v w t} A where
  obj J := localTotal A B J (totalStep_sq A B J)
  map {J K} f := (totalIso A B J).inv ≫ (amitsurHomFunctor.{u,v,w,t} A B).map f ≫ (totalIso A B K).hom
  map_id J := by
    rw [(amitsurHomFunctor.{u,v,w,t} A B).map_id J]
    exact (congrArg ((totalIso A B J).inv ≫ ·) (Category.id_comp (totalIso A B J).hom)).trans
      (totalIso A B J).inv_hom_id
  map_comp f g := by
    rw [Functor.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

private def totalNatIso : amitsurHomFunctor.{u,v,w,t} A B ≅ totalFunctor A B :=
  NatIso.ofComponents (totalIso A B) (by
    intro J K f
    change _ ≫ (totalIso A B K).hom =
      (totalIso A B J).hom ≫
        ((totalIso A B J).inv ≫ (amitsurHomFunctor.{u,v,w,t} A B).map f ≫ (totalIso A B K).hom)
    simp)

theorem totalFunctor_map {J : Inputs.{u,w,t} A} (f : I ⟶ J) (n : ℤ) :
    ((totalFunctor A B).map f).f n = totalComponent B f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext p
  let y := (productIso A B I n).inv x
  let q := rowIndex n p
  change (columnIso A B J p q).hom
      ((AmitsurTotalComplexSpec.Independent.map A B (globalMap.{u,v,w,t} f)).f n y p) =
    ((restrict.{u,max u v,max w t} A (degree A B p)).map (localMap B f p)).f q (x p)
  rw [AmitsurTotalComplexSpec.Independent.map_apply]
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (columnIso_natural A B I f p q)) (y p)
  change (columnIso A B J p q).hom
      (AmitsurTotalComplexSpec.Independent.tensorMap A B ((globalMap.{u,v,w,t} f).f q) p (y p)) =
    ((restrict.{u,max u v,max w t} A (degree A B p)).map (localMap B f p)).f q
      ((columnIso A B I p q).hom (y p)) at h
  have hy : (columnIso A B I p q).hom (y p) = x p :=
    (columnIso A B I p q).toLinearEquiv.apply_symm_apply (x p)
  rw [hy] at h
  exact h

open AmitsurTotalComplexSpec.Independent in
private def amitsurLiftIso :
    lift.{u,v,max u v w t} A ≅ 𝟭 (compValue.{max u v w t} A) :=
  NatIso.ofComponents
    (fun H => HomologicalComplex.Hom.isoOfComponents
      (fun n => (CochainCoefficientLift.termEquiv.{max u v} H n).symm.toModuleIso)
      (by
        intro n m _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        rfl))
    (by
      intro H K f
      apply HomologicalComplex.hom_ext
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      rfl)

/-- The strict augmentation is the unit followed by the product comparison.
The same-level lift of the global Hom in the Amitsur theorem is removed by
its canonical up/down isomorphism. -/
def augmentation : globalHomFunctor.{u,v,w,t} A ⟶ totalFunctor A B :=
  Functor.whiskerLeft (globalHomFunctor.{u,v,w,t} A) (amitsurLiftIso.{u,v,w,t} A).inv ≫
    Functor.whiskerLeft (globalHomFunctor.{u,v,w,t} A)
      (AmitsurTotalComplexSpec.Independent.naturalAugmentation.{u,v,max u v w t} A B) ≫
    (totalNatIso.{u,v,w,t} A B).hom

theorem augmentation_coordinates (n : ℤ) (z : (globalHom.{u,v,w,t} A I).X n) :
    let x := ((augmentation.{u,v,w,t} A B).app I).f n z
    x 0 = (comparison (degree A B 0) (P.{u,v,w,t} A I) (X.{u,v,w,t} A I)).f n
      (1 ⊗ₜ[A] z) ∧ ∀ p : ℕ, x (p + 1) = 0 := by
  let H := globalHom.{u,v,w,t} A I
  let x := AmitsurTotalComplexSpec.Independent.augmentationComponent A B H n z
  constructor
  · change (columnIso A B I 0 n).hom (x 0) = _
    exact (congrArg (fun y => (columnIso A B I 0 n).hom y)
      (AmitsurTotalComplexSpec.Independent.augmentation_zero A B H n z)).trans
      (columnIso_hom_apply A B I 0 n (1 ⊗ₜ[A] z))
  · intro p
    change (columnIso A B I (p + 1) (rowIndex n (p + 1))).hom (x (p + 1)) = 0
    let f := (columnIso A B I (p + 1) (rowIndex n (p + 1))).hom.hom
    exact (congrArg (fun y => f y)
      (AmitsurTotalComplexSpec.Independent.augmentation_succ A B H n z p)).trans (map_zero f)

variable [Module.FaithfullyFlat A B] in
theorem augmentation_quasiIso : QuasiIso ((augmentation.{u,v,w,t} A B).app I) := by
  let H := globalHom.{u,v,w,t} A I
  have h := UnboundedAmitsurDescent.augmentation_quasiIso A B H
  change QuasiIso ((amitsurLiftIso.{u,v,w,t} A).inv.app H ≫
    (AmitsurTotalComplexSpec.Independent.augmentation A B H ≫ (totalIso A B I).hom))
  exact quasiIso_comp _ _ (hφ' := quasiIso_comp _ _ (hφ := h))

attribute [local instance] HasDerivedCategory.standard

private def modelNatIso {R : Type u} [CommRing R]
    {C₁ C₂ : Type*} [Category C₁] [Category C₂] (M : Models.{u,a} R)
    (U : C₁ ⥤ compValue.{a} R) (V : C₂ ⥤ compValue.{a} R)
    (hP : ∀ Z, (U.obj Z).IsKProjective) :
    (U.op.prod V ⋙ homFunctor R) ⋙ qValue R ≅
      (U ⋙ qValue R).op.prod (V ⋙ qValue R) ⋙ rHomValue M :=
  NatIso.ofComponents
    (fun K => DerivedHomModels.modelIso M
      (DerivedHomModels.representative (Iso.refl ((qValue R).obj (U.obj K.1.unop))))
      (DerivedHomModels.representative (Iso.refl ((qValue R).obj (V.obj K.2))))
      (Or.inl (hP K.1.unop)))
    (by
      intro K L f
      exact DerivedHomModels.modelIso_chain_natural M (Iso.refl _) (Iso.refl _)
        (Iso.refl _) (Iso.refl _) (Or.inl (hP K.1.unop)) (Or.inl (hP L.1.unop))
        ((qValue R).map (U.map f.1.unop)) ((qValue R).map (V.map f.2))
        (U.map f.1.unop) (V.map f.2) (by simp) (by simp))

/-- Identify the global model with derived Hom of the original localized inputs. -/
def globalModelIso (M : Models.{u,max u v w t} A) :
    globalHomFunctor.{u,v,w,t} A ⋙ qValue A ≅
      derivedInputs.{u,v,w,t} A ⋙ rHomValue M :=
  modelNatIso M (firstLift.{u,v,w,t} A) (secondLift.{u,v,w,t} A)
      (fun Z => globalKProjective.{u,v,w,t} A (op Z, (0 : compValue.{t} A))) ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod
        (NatIso.op (Functor.isoWhiskerLeft (perfect.{u,w} A).ι (liftDFactors.{max u v t,w} A)))
        (liftDFactors.{max u v w,t} A).symm)
      (rHomValue M)

/-- All columns compute derived Hom over their respective Amitsur rings. -/
def localModelIso (p : ℕ) (N : Models.{max u v,max u v w t} (degree A B p)) :
    localHomFunctor.{u,v,w,t} A B p ⋙ qValue (degree A B p) ≅
      localDerivedInputs A B p ⋙ rHomValue N :=
  modelNatIso N (firstLift.{u,v,w,t} A ⋙ extend A (degree A B p))
    (secondLift.{u,v,w,t} A ⋙ extend A (degree A B p))
    (fun Z => localKProjective A B (op Z, (0 : compValue.{t} A)) p)

variable [Module.FaithfullyFlat A B]

/-- Faithfully flat descent for perfect-coefficient mapping complexes,
naturally in the bounded perfect complex and the arbitrary target complex. -/
def descentIso (M : Models.{u,max u v w t} A) :
    derivedInputs.{u,v,w,t} A ⋙ rHomValue M ≅ totalFunctor A B ⋙ qValue A := by
  let α := Functor.whiskerRight (augmentation.{u,v,w,t} A B) (qValue A)
  letI : IsIso α := (NatTrans.isIso_iff_isIso_app α).mpr (fun I => by
    letI := augmentation_quasiIso A B I
    change IsIso ((qValue A).map ((augmentation.{u,v,w,t} A B).app I))
    infer_instance)
  exact (globalModelIso A M).symm ≪≫ asIso α

theorem descent : descentType.{u,v,w,t} := by
  intro A B _ _ _ _ M N
  refine ⟨totalStep_sq A B, totalFunctor A B, fun _ => rfl,
    localHomFunctor A B, fun _ _ => rfl, globalHomFunctor A, fun _ => rfl,
    augmentation A B, globalModelIso A M, fun p => localModelIso A B p (N p),
    descentIso A B M, ?_, ?_, ?_, ?_, ?_⟩
  · intro I J f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro p I J f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro I J f n
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using totalFunctor_map A B I f n
  · intro I n z
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact augmentation_coordinates.{u,v,w,t} A B I n z
  · intro I
    rfl

/-- The comparison for the canonical U08a bifunctor at the common bound. -/
def canonicalDescent :
    derivedInputs.{u,v,w,t} A ⋙ DerivedHomModels.rHom.{u,max v w t} A ≅
      totalFunctor A B ⋙ qValue A :=
  descentIso A B (DerivedHomModels.models A)

/-- Identification of each column with the canonical U08a bifunctor over its own ring. -/
def canonicalLocalModel (p : ℕ) :
    localHomFunctor.{u,v,w,t} A B p ⋙ qValue (degree A B p) ≅
      localDerivedInputs A B p ⋙ DerivedHomModels.rHom.{max u v,max w t} (degree A B p) :=
  localModelIso A B p (DerivedHomModels.models (degree A B p))

end

end DerivedFormalization.Descent.PerfectMappingDescent
