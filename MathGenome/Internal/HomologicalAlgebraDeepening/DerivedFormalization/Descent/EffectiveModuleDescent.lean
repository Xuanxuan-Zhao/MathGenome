import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.EffectiveModuleDescent
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurExactness
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.DescentCounit
import Batteries.Tactic.OpenPrivate

/-! Effective descent for modules. -/

open CategoryTheory
open scoped ChangeOfRings TensorProduct

namespace DerivedFormalization.Descent.EffectiveModuleDescent

universe u v w

noncomputable section

open StrictModuleData
open AmitsurAlgebras (TensorPower factor)
open DescentCounitSpec (generator generator_add baseChangePosition)
open DescentCounit (baseChangeTheta baseChangeTheta_generator)

open private diagonalPosition_inv_generator diagonalPosition_hom_tmul from
  MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.DescentCounit
open private alongTheta_generator insertPosition_tmul baseChangePosition_hom_tmul
  baseChangePosition_inv_tmul baseChangeTensor baseChangeTensor_tmul from
  MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.DescentCounit

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 700000

/-- The canonical position comparison becomes the identity along the diagonal. -/
theorem baseChange_normalized {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat.{max u v w} A) :
    (StrictModuleDataSpec.diagonalTheta (baseChangeTheta.{u,v,w} (B := B) M)).hom =
      𝟙 ((ModuleCat.extendScalars (algebraMap A B)).obj M) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  let N := (ModuleCat.extendScalars (algebraMap A B)).obj M
  let x : N := (1 : B) ⊗ₜ[A,algebraMap A B] m
  let G := (diagonal A B).toRingHom
  change (diagonalPosition.{u,v,w} A B 1).hom.app N
    ((ModuleCat.extendScalars G).map (baseChangeTheta (B := B) M).hom
      ((diagonalPosition.{u,v,w} A B 0).inv.app N x)) = x
  rw [diagonalPosition_inv_generator.{u,v,w} 0 N x]
  rw [ModuleCat.ExtendScalars.map_tmul, baseChangeTheta_generator.{u,v,w} M m]
  change (diagonalPosition.{u,v,w} A B 1).hom.app N
    ((1 : B) ⊗ₜ[TensorPower A B 2,G]
      (show (atPosition A B (1 : Fin 2)).obj N from (1 : TensorPower A B 2)
        ⊗ₜ[B,(factor A B (1 : Fin 2)).toRingHom] x)) = x
  rw [diagonalPosition_hom_tmul, map_one, one_mul, one_smul]

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

private theorem baseChange_along_generator {n : ℕ} (f : Fin 2 → Fin n)
    (M : ModuleCat.{max u v w} A) (m : M) :
    let x : (ModuleCat.extendScalars (algebraMap A B)).obj M :=
      (1 : B) ⊗ₜ[A,algebraMap A B] m
    (StrictModuleDataSpec.alongTheta f (baseChangeTheta.{u,v,w} (B := B) M)).hom
        (generator.{u,v,w} (f 0) x) = generator.{u,v,w} (f 1) x := by
  dsimp only
  rw [alongTheta_generator.{u,v,w}, baseChangeTheta_generator.{u,v,w} M m]
  exact (insertPosition_tmul.{u,v,w} f 1 _ 1 _).trans (by rw [map_one]; rfl)

private theorem baseChange_cocycle (M : ModuleCat.{max u v w} A) :
    (StrictModuleDataSpec.alongTheta (StrictModuleDataSpec.pair 2)
        (baseChangeTheta.{u,v,w} (B := B) M)).hom ≫
      (StrictModuleDataSpec.alongTheta (StrictModuleDataSpec.pair 0)
        (baseChangeTheta.{u,v,w} (B := B) M)).hom =
      (StrictModuleDataSpec.alongTheta (StrictModuleDataSpec.pair 1)
        (baseChangeTheta.{u,v,w} (B := B) M)).hom := by
  let e := (baseChangePosition.{u,v,w} (A := A) (B := B) (0 : Fin 3)).app M
  apply (cancel_epi e.hom).mp
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  simp only [ModuleCat.comp_apply]
  let N := (ModuleCat.extendScalars.{u,v,max u v w} (algebraMap A B)).obj M
  let x : N :=
    (1 : B) ⊗ₜ[A,algebraMap A B] m
  have he : e.hom ((1 : TensorPower A B 3) ⊗ₜ[A,algebraMap A (TensorPower A B 3)] m) =
      generator.{u,v,w} (0 : Fin 3) x :=
    baseChangePosition_hom_tmul.{u,v,w} (0 : Fin 3) M 1 m
  have h₂ := baseChange_along_generator.{u,v,w} (B := B) (StrictModuleDataSpec.pair 2) M m
  have h₀ := baseChange_along_generator.{u,v,w} (B := B) (StrictModuleDataSpec.pair 0) M m
  have h₁ := baseChange_along_generator.{u,v,w} (B := B) (StrictModuleDataSpec.pair 1) M m
  let θ := baseChangeTheta.{u,v,w} (B := B) M
  let f₁₂ := (StrictModuleDataSpec.alongTheta (StrictModuleDataSpec.pair 2) θ).hom
  let f₂₃ := (StrictModuleDataSpec.alongTheta (StrictModuleDataSpec.pair 0) θ).hom
  let f₁₃ := (StrictModuleDataSpec.alongTheta (StrictModuleDataSpec.pair 1) θ).hom
  exact (congrArg (fun y : (atPosition A B (0 : Fin 3)).obj N ↦ f₂₃ (f₁₂ y)) he).trans
    ((congrArg (fun y : (atPosition A B (1 : Fin 3)).obj N ↦ f₂₃ y) h₂).trans
      (h₀.trans (h₁.symm.trans
        (congrArg (fun y : (atPosition A B (0 : Fin 3)).obj N ↦ f₁₃ y) he.symm))))

/-- The canonical scalar-extension datum satisfies both strict identities. -/
theorem baseChange_coherence : EffectiveModuleDescentSpec.BaseChangeCoherence.{u,v,w} := by
  intro A B _ _ _
  exact ⟨baseChange_normalized, baseChange_cocycle⟩

/-- Scalar extension with its canonical strict descent datum. -/
abbrev baseChange (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    ModuleCat.{max u v w} A ⥤ Datum.{u,v,w} A B :=
  EffectiveModuleDescentSpec.baseChange A B (baseChange_coherence A B)

open DescentCounit (invariants descend counitMap)

/-- The unit comparison sends a module element to its invariant unit tensor. -/
def unitMap (M : ModuleCat.{max u v w} A) :
    M ⟶ (baseChange.{u,v,w} A B ⋙ descend).obj M :=
  ModuleCat.ofHom
    (((ModuleCat.extendRestrictScalarsAdj.{max u v w,u,v} (algebraMap A B)).unit.app M).hom.codRestrict
      (invariants ((baseChange.{u,v,w} A B).obj M))
      (baseChangeTheta_generator.{u,v,w} M))

@[simp] theorem unitMap_apply (M : ModuleCat.{max u v w} A) (m : M) :
    ((unitMap (B := B) M m).val : ((baseChange.{u,v,w} A B).obj M).module) =
      (1 : B) ⊗ₜ[A,algebraMap A B] m := rfl

private def degreeZeroEquiv (M : ModuleCat.{max u v w} A) :
    ↑(AmitsurComplex.Degree A B M 0) ≃+
      ↑((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
  (TensorProduct.congr (AmitsurAlgebras.oneEquiv A B).toLinearEquiv
    (LinearEquiv.refl A M)).toAddEquiv.trans (baseChangeTensor.{u,v,w} M).symm.toAddEquiv

private theorem degreeZeroEquiv_tmul (M : ModuleCat.{max u v w} A)
    (b : AmitsurAlgebras.Degree A B 0) (m : M) :
    degreeZeroEquiv.{u,v,w} M (b ⊗ₜ[A] m) =
      AmitsurAlgebras.oneEquiv A B b ⊗ₜ[A,algebraMap A B] m := by
  let e := baseChangeTensor.{u,v,w} (B := B) M
  change e.symm (TensorProduct.congr (AmitsurAlgebras.oneEquiv A B).toLinearEquiv
    (LinearEquiv.refl A M) (b ⊗ₜ[A] m)) = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  exact e.symm_apply_eq.mpr (baseChangeTensor_tmul.{u,v,w} M _ m).symm

private theorem degreeZeroEquiv_augmentation (M : ModuleCat.{max u v w} A) (m : M) :
    degreeZeroEquiv.{u,v,w} M (AmitsurComplex.augmentation A B M m) =
      (1 : B) ⊗ₜ[A,algebraMap A B] m := by
  rw [AmitsurComplex.augmentation_apply, degreeZeroEquiv_tmul, map_one]

private def degreeOneEquiv (M : ModuleCat.{max u v w} A) :
    ↑(AmitsurComplex.Degree A B M 1) ≃+
      ↑((ModuleCat.extendScalars (algebraMap A (TensorPower A B 2))).obj M) :=
  (baseChangeTensor.{u,max u v,w} (B := TensorPower A B 2) M).symm.toAddEquiv

private theorem degreeOneEquiv_tmul (M : ModuleCat.{max u v w} A)
    (b : TensorPower A B 2) (m : M) :
    degreeOneEquiv.{u,v,w} M (b ⊗ₜ[A] m) =
      b ⊗ₜ[A,algebraMap A (TensorPower A B 2)] m := by
  let e := baseChangeTensor.{u,max u v,w} (B := TensorPower A B 2) M
  change e.symm (b ⊗ₜ[A] m) = _
  exact e.symm_apply_eq.mpr (baseChangeTensor_tmul.{u,max u v,w} M b m).symm

private theorem degreeZero_coface (i : Fin 2) (b : AmitsurAlgebras.Degree A B 0) :
    AmitsurAlgebras.coface (p := 0) i b =
      factor A B (i.succAbove 0) (AmitsurAlgebras.oneEquiv A B b) := by
  have hb := (AmitsurAlgebras.oneEquiv A B).symm_apply_apply b
  rw [AmitsurAlgebras.oneEquiv_symm_apply] at hb
  exact (congrArg (AmitsurAlgebras.coface (A := A) (B := B) i) hb.symm).trans
    (AmitsurAlgebras.map_factor i.succAbove 0 _)

/-- In the common degree-one coordinates, the invariant equations compare
the two cofaces of the augmented Amitsur complex. -/
private theorem canonical_cofaces (M : ModuleCat.{max u v w} A)
    (z : AmitsurComplex.Degree A B M 0) :
    let x := degreeZeroEquiv.{u,v,w} (B := B) M z
    let p := (baseChangePosition.{u,v,w} (A := A) (B := B) (1 : Fin 2)).app M
    p.inv (generator.{u,v,w} (1 : Fin 2) x) =
      degreeOneEquiv.{u,v,w} M
        (AmitsurComplex.coface A B M (0 : Fin 2) z) ∧
    p.inv ((baseChangeTheta.{u,v,w} (B := B) M).hom (generator.{u,v,w} (0 : Fin 2) x)) =
      degreeOneEquiv.{u,v,w} M (AmitsurComplex.coface A B M (1 : Fin 2) z) := by
  dsimp only
  change AmitsurAlgebras.Degree A B 0 ⊗[A] M at z
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
      let a := AmitsurAlgebras.oneEquiv A B b
      let N := (ModuleCat.extendScalars.{u,v,max u v w} (algebraMap A B)).obj M
      let x : N := a ⊗ₜ[A,algebraMap A B] m
      let y : N := (1 : B) ⊗ₜ[A,algebraMap A B] m
      let p := (baseChangePosition.{u,v,w} (A := A) (B := B) (1 : Fin 2)).app M
      rw [degreeZeroEquiv_tmul, AmitsurComplex.coface_tmul, AmitsurComplex.coface_tmul,
        degreeOneEquiv_tmul, degreeOneEquiv_tmul, degreeZero_coface, degreeZero_coface]
      have h₀ := baseChangePosition_inv_tmul.{u,v,w} (1 : Fin 2) M
        (1 : TensorPower A B 2) a m
      have ht := DescentCounit.baseChangeTheta_tmul.{u,v,w} A B M a 1 m
      simp only [map_one] at ht
      have h₁ := baseChangePosition_inv_tmul.{u,v,w} (1 : Fin 2) M
        (factor A B (0 : Fin 2) a) 1 m
      rw [one_mul] at h₀
      rw [map_one, mul_one] at h₁
      change (baseChangeTheta.{u,v,w} (B := B) M).hom (generator.{u,v,w} (0 : Fin 2) x) =
        factor A B (0 : Fin 2) a ⊗ₜ[B,(factor A B (1 : Fin 2)).toRingHom] y at ht
      exact ⟨h₀, (congrArg (fun z ↦ p.inv z) ht).trans h₁⟩
  | add z₁ z₂ h₁ h₂ =>
      simp only [map_add, generator_add]
      exact ⟨congrArg₂ (· + ·) h₁.1 h₂.1, congrArg₂ (· + ·) h₁.2 h₂.2⟩

private theorem mem_invariants_iff (M : ModuleCat.{max u v w} A)
    (z : AmitsurComplex.Degree A B M 0) :
    degreeZeroEquiv.{u,v,w} M z ∈ invariants ((baseChange.{u,v,w} A B).obj M) ↔
      AmitsurComplex.differential A B M 0 z = 0 := by
  let x := degreeZeroEquiv.{u,v,w} (B := B) M z
  let p := (baseChangePosition.{u,v,w} (A := A) (B := B) (1 : Fin 2)).app M
  let e := degreeOneEquiv.{u,v,w} (B := B) M
  have h := canonical_cofaces.{u,v,w} M z
  have hd : AmitsurComplex.differential A B M 0 =
      AmitsurComplex.coface A B M (0 : Fin 2) - AmitsurComplex.coface A B M (1 : Fin 2) := by
    rw [AmitsurComplex.differential, Fin.sum_univ_two]
    simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_zsmul, sub_eq_add_neg]
  change (baseChangeTheta.{u,v,w} (B := B) M).hom (generator.{u,v,w} (0 : Fin 2) x) =
    generator.{u,v,w} (1 : Fin 2) x ↔ _
  rw [hd]
  change _ ↔ AmitsurComplex.coface A B M (0 : Fin 2) z -
    AmitsurComplex.coface A B M (1 : Fin 2) z = 0
  rw [sub_eq_zero, eq_comm (a := AmitsurComplex.coface A B M (0 : Fin 2) z)]
  have hp : Function.Injective p.inv := p.symm.toLinearEquiv.injective
  constructor
  · intro hx
    exact e.injective (h.2.symm.trans ((congrArg (fun y ↦ p.inv y) hx).trans h.1))
  · intro hz
    exact hp (h.2.trans ((congrArg e hz).trans h.1.symm))

open private exactAt_iff_function_exact from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurExactness

private theorem exact_augmentation [Module.FaithfullyFlat A B] (M : ModuleCat.{max u v w} A) :
    Function.Exact (AmitsurComplex.augmentation A B M) (AmitsurComplex.differential A B M 0) := by
  let K := AmitsurComplex.complex A B M
  have h := (exactAt_iff_function_exact A K 0).mp (AmitsurExactness.exactAt A B M 0)
  change Function.Exact ((AmitsurComplex.complex A B M).d (-1) 0)
    ((AmitsurComplex.complex A B M).d (↑(0 : ℕ)) (↑(0 : ℕ) + 1)) at h
  rwa [AmitsurComplex.complex_d_neg_one, AmitsurComplex.complex_d_ofNat] at h

private theorem injective_augmentation [Module.FaithfullyFlat A B] (M : ModuleCat.{max u v w} A) :
    Function.Injective (AmitsurComplex.augmentation A B M) := by
  let K := AmitsurComplex.complex A B M
  have h := (exactAt_iff_function_exact A K (-1)).mp (AmitsurExactness.exactAt A B M (-1))
  change Function.Exact ((AmitsurComplex.complex A B M).d (-2) (-1))
    ((AmitsurComplex.complex A B M).d (-1) 0) at h
  have hzero : (AmitsurComplex.complex A B M).d (-2) (-1) = 0 :=
    AmitsurComplex.complex_d_succ A B M (-2)
  rw [hzero, AmitsurComplex.complex_d_neg_one] at h
  intro x y hxy
  have hz : AmitsurComplex.augmentation A B M (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz'⟩ := (h (x - y)).mp hz
  change 0 = x - y at hz'
  exact sub_eq_zero.mp hz'.symm

private theorem unitMap_bijective [Module.FaithfullyFlat A B] (M : ModuleCat.{max u v w} A) :
    Function.Bijective (unitMap.{u,v,w} (B := B) M) := by
  let e := degreeZeroEquiv.{u,v,w} (B := B) M
  constructor
  · intro x y hxy
    apply injective_augmentation (B := B) M
    apply e.injective
    exact (degreeZeroEquiv_augmentation.{u,v,w} (B := B) M x).trans
      ((congrArg Subtype.val hxy).trans (degreeZeroEquiv_augmentation.{u,v,w} (B := B) M y).symm)
  · intro x
    let z := e.symm x.val
    have hz : e z = x.val := e.apply_symm_apply _
    have hInv : e z ∈ invariants ((baseChange.{u,v,w} A B).obj M) := hz.symm ▸ x.property
    obtain ⟨m, hm⟩ := (exact_augmentation (B := B) M z).mp ((mem_invariants_iff.{u,v,w} M z).mp hInv)
    refine ⟨m, Subtype.ext ?_⟩
    exact (degreeZeroEquiv_augmentation.{u,v,w} (B := B) M m).symm.trans ((congrArg e hm).trans hz)

/-- The comparison with the descended module is a natural isomorphism. -/
def unitIso (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    𝟭 (ModuleCat.{max u v w} A) ≅ baseChange.{u,v,w} A B ⋙ descend :=
  NatIso.ofComponents
    (fun M ↦ (LinearEquiv.ofBijective (unitMap M).hom (unitMap_bijective M)).toModuleIso)
    (fun f ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      apply Subtype.ext
      rfl)

@[simp] theorem unitIso_hom_app [Module.FaithfullyFlat A B] (M : ModuleCat.{max u v w} A) :
    (unitIso.{u,v,w} A B).hom.app M = unitMap M := rfl

private def strictIso {X Y : Datum.{u,v,w} A B} (e : X.module ≅ Y.module)
    (h : (atPosition A B (0 : Fin 2)).map e.hom ≫ Y.theta.hom =
      X.theta.hom ≫ (atPosition A B (1 : Fin 2)).map e.hom) : X ≅ Y where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, by
    let F₀ := atPosition.{u,v,w} A B (0 : Fin 2)
    let F₁ := atPosition.{u,v,w} A B (1 : Fin 2)
    apply (F₀.mapIso e).inv_comp_eq.mpr
    change X.theta.hom = F₀.map e.hom ≫ Y.theta.hom ≫ F₁.map e.inv
    rw [← Category.assoc, h, Category.assoc, ← F₁.map_comp, e.hom_inv_id, F₁.map_id,
      Category.comp_id]⟩
  hom_inv_id := StrictModuleDataSpec.Hom.ext e.hom_inv_id
  inv_hom_id := StrictModuleDataSpec.Hom.ext e.inv_hom_id

/-- The flat descent counit as a natural isomorphism of strict data. -/
def counitIso (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] :
    descend ⋙ baseChange.{u,v,w} A B ≅ 𝟭 (Datum.{u,v,w} A B) :=
  NatIso.ofComponents
    (fun X ↦ strictIso ((DescentCounit.counitIso.{u,v,w} A B).app X)
      (DescentCounit.counit_compatible.{u,v,w} A B X))
    (fun f ↦ StrictModuleDataSpec.Hom.ext (DescentCounit.counit_natural.{u,v,w} A B f))

@[simp] theorem counitIso_hom_app [Module.Flat A B] (X : Datum.{u,v,w} A B) :
    ((counitIso.{u,v,w} A B).hom.app X).hom = counitMap X := rfl

private theorem unit_counit_triangle [Module.FaithfullyFlat A B] (M : ModuleCat.{max u v w} A) :
    (baseChange.{u,v,w} A B).map ((unitIso A B).hom.app M) ≫
      (counitIso A B).hom.app ((baseChange.{u,v,w} A B).obj M) =
        𝟙 ((baseChange.{u,v,w} A B).obj M) := by
  apply StrictModuleDataSpec.Hom.ext
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  let X := (baseChange.{u,v,w} A B).obj M
  let x : invariants X := unitMap M m
  change counitMap X ((1 : B) ⊗ₜ[A,algebraMap A B]
    (show (descend (A := A) (B := B)).obj X from x)) = (1 : B) ⊗ₜ[A,algebraMap A B] m
  exact (DescentCounit.counitMap_tmul.{u,v,w} A B X 1 x).trans (one_smul B _)

/-- The unit and counit with their specified tensor formulas. -/
def effectiveEquivalence (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] : EffectiveModuleDescentSpec.EffectiveEquivalence.{u,v,w} A B where
  coherence := baseChange_coherence A B
  unitIso := unitIso A B
  counitIso := counitIso A B
  unit_apply := unitMap_apply
  counit_hom := counitIso_hom_app
  triangle := unit_counit_triangle

/-- Faithfully flat scalar extension and the invariant equalizer are inverse equivalences. -/
def equivalence (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] : ModuleCat.{max u v w} A ≌ Datum.{u,v,w} A B :=
  EffectiveModuleDescentSpec.EffectiveEquivalence.toEquivalence A B (effectiveEquivalence A B)

theorem effective : EffectiveModuleDescentSpec.Effective.{u,v,w} := by
  intro A B _ _ _ _
  exact ⟨effectiveEquivalence A B⟩

end

end DerivedFormalization.Descent.EffectiveModuleDescent
