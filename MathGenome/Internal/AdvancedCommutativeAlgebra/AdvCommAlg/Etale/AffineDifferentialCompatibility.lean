import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.BaseChange
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.AffineDifferentialCompatibility

/-! Compatibility of the affine differential comparisons. All equalities are
on entire modules, not just on their displayed generators. -/
namespace AdvCommAlg.Etale

open TensorProduct
open Specs.AdvCommAlg.Etale.AffineDifferentialCompatibility
open Specs.AdvCommAlg.Differentials (baseChangeEquivValue)
universe u v w z t q
noncomputable section

section Localization
variable (A : Type u) (B : Type v) (T : Type w)
    [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra A T] [Algebra B T] [IsScalarTower A B T]
    (S : Submonoid B) [IsLocalization S T]

/-- This is exactly the canonical comparison used in KD-16. -/
theorem localizationComparison_eq :
    localizationComparison A B T S =
      (Differentials.differential_isBaseChange A B T S).equiv := rfl

theorem localizationComparison_tmul (t : T) (ω : KaehlerDifferential A B) :
    localizationComparison A B T S (t ⊗ₜ ω) =
      t • KaehlerDifferential.map A A B T ω :=
  IsBaseChange.equiv_tmul _ _ _

theorem localizationComparison_tmul_D (t : T) (b : B) :
    localizationComparison A B T S (t ⊗ₜ KaehlerDifferential.D A B b) =
      t • KaehlerDifferential.D A T (algebraMap B T b) := by
  rw [localizationComparison_tmul, KaehlerDifferential.map_D]
end Localization

/-- Iterating principal restriction agrees with restricting at the product. -/
theorem principal_localization_iteration : principalIteration.{u,v,w,z} := by
  intro A B C F _ _ _ _ _ _ _ _ _ _ _ _ _ _ g h _ _
  letI : IsLocalization.Away (g * h) F := IsLocalization.Away.mul' C F g h
  intro x
  have heq :
      (localizationComparison A B F (Submonoid.powers (g * h))).toLinearMap.comp
        (AlgebraTensorModule.cancelBaseChange B C F F (KaehlerDifferential A B)).toLinearMap =
      (localizationComparison A C F (Submonoid.powers (algebraMap B C h))).toLinearMap.comp
        ((localizationComparison A B C (Submonoid.powers g)).toLinearMap.baseChange F) := by
    apply LinearMap.restrictScalars_injective C
    apply TensorProduct.ext
    apply LinearMap.ext
    intro f
    apply LinearMap.restrictScalars_injective B
    apply TensorProduct.ext
    apply LinearMap.ext
    intro c
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    change localizationComparison A B F (Submonoid.powers (g * h))
        ((c • f) ⊗ₜ KaehlerDifferential.D A B b) =
      localizationComparison A C F (Submonoid.powers (algebraMap B C h))
        (f ⊗ₜ localizationComparison A B C (Submonoid.powers g)
          (c ⊗ₜ KaehlerDifferential.D A B b))
    rw [localizationComparison_tmul_D, localizationComparison_tmul_D,
      ← TensorProduct.smul_tmul, localizationComparison_tmul_D,
      ← IsScalarTower.algebraMap_apply B C F]
  exact congrArg (fun L => L x) heq

theorem principal_localization_iteration_generators :
    principalIterationGenerators.{u,v,w,z} := by
  intro A B C F _ _ _ _ _ _ _ _ _ _ _ _ _ _ g h _ _
  letI : IsLocalization.Away (g * h) F := IsLocalization.Away.mul' C F g h
  intro b
  constructor
  · rw [localizationComparison_tmul_D, one_smul]
  · rw [localizationComparison_tmul_D, one_smul,
      localizationComparison_tmul_D, one_smul, ← IsScalarTower.algebraMap_apply B C F]

section BaseChange
variable (A : Type u) (A' : Type v) (B : Type w) (C : Type z)
    (T : Type t) (U : Type q)
    [CommRing A] [CommRing A'] [CommRing B] [CommRing C] [CommRing T] [CommRing U]
    [Algebra A A'] [Algebra A B] [Algebra A C] [Algebra A' C] [Algebra B C]
    [IsScalarTower A A' C] [IsScalarTower A B C]
    [Algebra A T] [Algebra B T] [IsScalarTower A B T]
    [Algebra A U] [Algebra A' U] [Algebra B U] [Algebra C U] [Algebra T U]
    [IsScalarTower A A' U] [IsScalarTower A B U] [IsScalarTower A C U]
    [IsScalarTower A T U] [IsScalarTower A' C U]
    [IsScalarTower B C U] [IsScalarTower B T U]
    [Algebra.IsPushout A A' B C]
    (g : B) [IsLocalization.Away g T]
    [IsLocalization.Away (algebraMap B C g) U]

/-- Equality of the two full comparison maps after arbitrary base change. -/
theorem baseChange_principal_restriction_at :
    baseChangeRestrictionAt A A' B C T U g := by
  letI : Algebra.IsPushout A A' T U := localizedPushout A A' B C T U g
  intro x
  have heq :
      (localizationComparison A' C U (Submonoid.powers (algebraMap B C g))).toLinearMap.comp
        (((baseChangeEquivValue A A' B C).toLinearMap.baseChange U).comp
          (AlgebraTensorModule.cancelBaseChange B C U U (KaehlerDifferential A B)).symm.toLinearMap) =
      (baseChangeEquivValue A A' T U).toLinearMap.comp
        (((localizationComparison A B T (Submonoid.powers g)).toLinearMap.baseChange U).comp
          (AlgebraTensorModule.cancelBaseChange B T U U (KaehlerDifferential A B)).symm.toLinearMap) := by
    apply LinearMap.restrictScalars_injective B
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    change localizationComparison A' C U (Submonoid.powers (algebraMap B C g))
        (u ⊗ₜ baseChangeEquivValue A A' B C (1 ⊗ₜ KaehlerDifferential.D A B b)) =
      baseChangeEquivValue A A' T U
        (u ⊗ₜ localizationComparison A B T (Submonoid.powers g)
          (1 ⊗ₜ KaehlerDifferential.D A B b))
    rw [Differentials.baseChange_formula, one_smul, localizationComparison_tmul_D,
      localizationComparison_tmul_D, one_smul, Differentials.baseChange_formula,
      ← IsScalarTower.algebraMap_apply B C U, ← IsScalarTower.algebraMap_apply B T U]
  exact congrArg (fun L => L x) heq
end BaseChange

/-- Every base change commutes with every principal restriction. -/
theorem baseChange_principal_restriction : baseChangeRestriction.{u,v,w,z,t,q} :=
  baseChange_principal_restriction_at

end
end AdvCommAlg.Etale
