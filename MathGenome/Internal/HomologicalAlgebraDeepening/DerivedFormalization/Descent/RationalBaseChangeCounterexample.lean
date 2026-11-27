import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.RationalBaseChangeCounterexample
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace DerivedFormalization.Descent.RationalBaseChange

attribute [local instance] HasDerivedCategory.standard

theorem intToRatFlat : (algebraMap ℤ ℚ).Flat :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat ℚ (nonZeroDivisors ℤ))

private noncomputable abbrev extendToRat : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ :=
  ModuleCat.extendScalars (algebraMap ℤ ℚ)

private abbrev residueModule (ℓ : ℤ) : ModuleCat.{0} ℤ :=
  ModuleCat.of ℤ (ℤ ⧸ Ideal.span ({ℓ} : Set ℤ))

private theorem residueModuleBaseChangeIsZero (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    IsZero (extendToRat.obj (residueModule ℓ)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  let : Module ℤ ℚ := Module.compHom ℚ (algebraMap ℤ ℚ)
  change (1 : ℚ) ⊗ₜ[ℤ] m = 0
  have hℓm : ℓ • m = 0 := by
    rw [Algebra.smul_def]
    change Ideal.Quotient.mk (Ideal.span ({ℓ} : Set ℤ)) ℓ * m = 0
    rw [Ideal.Quotient.mk_singleton_self, zero_mul]
  let q : ℚ := (algebraMap ℤ ℚ ℓ)⁻¹
  have hq : ℓ • q = 1 := by
    change algebraMap ℤ ℚ ℓ * (algebraMap ℤ ℚ ℓ)⁻¹ = 1
    exact mul_inv_cancel₀ (by simpa using hℓ)
  have h := TensorProduct.smul_tmul (R := ℤ) ℓ q m
  rw [hq, hℓm, TensorProduct.tmul_zero] at h
  exact h

theorem rationalBaseChangeCounterexample (ℓ : ℤ) (hℓ : Prime ℓ) :
    ¬ IsZero (residueComplex ℓ) ∧ IsZero (rationalization.obj (residueComplex ℓ)) := by
  constructor
  · intro h
    have hH := (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) 0).map_isZero h
    have e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app (residueModule ℓ)
    have hM : IsZero (residueModule ℓ) := hH.of_iso e.symm
    exact hℓ.not_isUnit (Ideal.span_singleton_eq_top.mp <|
      Ideal.Quotient.subsingleton_iff.mp (ModuleCat.isZero_iff_subsingleton.mp hM))
  · let : PreservesFiniteLimits extendToRat :=
      ModuleCat.preservesFiniteLimits_extendScalars_of_flat intToRatFlat
    let : extendToRat.Additive := (ModuleCat.extendRestrictScalarsAdj (algebraMap ℤ ℚ)).left_adjoint_additive
    have e := (extendToRat.mapDerivedCategorySingleFunctor 0).app (residueModule ℓ)
    exact ((DerivedCategory.singleFunctor (ModuleCat.{0} ℚ) 0).map_isZero
      (residueModuleBaseChangeIsZero ℓ hℓ.ne_zero)).of_iso e

end DerivedFormalization.Descent.RationalBaseChange
