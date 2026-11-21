import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.BaseChange
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.CotangentFibers

/-! KD-24: cotangent fibres commute with passage to the fibre over the
base point and with localization at the two corresponding primes. -/
namespace AdvCommAlg.Differentials

open TensorProduct
universe u v w
noncomputable section
attribute [local instance] Localization.AtPrime.algebraOfLiesOver
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The induced κ(p)-point of κ(p) ⊗_A B. -/
def cotangentFiberPoint :
    Specs.AdvCommAlg.Differentials.CotangentFibers.fiberPointType.{u,v} :=
  Specs.AdvCommAlg.Differentials.CotangentFibers.fiberPointValue

theorem cotangentFiberPoint_apply :
    Specs.AdvCommAlg.Differentials.CotangentFibers.fiberPointFormula.{u,v} := by
  intro A B _ _ _ p q _ _ _ a b
  rfl

/-- Localizing only the base leaves differentials unchanged when the target
already has its compatible localized-base algebra structure. -/
def localBaseDifferentialEquiv
    (A : Type u) (T : Type v) (L : Type w)
    [CommRing A] [CommRing T] [CommRing L]
    [Algebra A T] [Algebra A L] [Algebra L T] [IsScalarTower A L T]
    (U : Submonoid A) [IsLocalization U L] :
    KaehlerDifferential A T ≃ₗ[T] KaehlerDifferential L T := by
  let f := KaehlerDifferential.map A L T T
  haveI : IsLocalization (Algebra.algebraMapSubmonoid T U) T :=
    IsLocalization.of_le_isUnit (by
      rintro _ ⟨a, ha, rfl⟩
      rw [IsScalarTower.algebraMap_apply A L T]
      exact (IsLocalization.map_units L (⟨a, ha⟩ : U)).map (algebraMap L T))
  haveI : IsLocalizedModule U (LinearMap.id :
      KaehlerDifferential A T →ₗ[A] KaehlerDifferential A T) :=
    isLocalizedModule_id U _ L
  let e := IsLocalizedModule.linearEquiv U
    (LinearMap.id : KaehlerDifferential A T →ₗ[A] KaehlerDifferential A T)
    (f.restrictScalars A)
  have he (x : KaehlerDifferential A T) : e x = f x :=
    IsLocalizedModule.linearEquiv_apply U _ _ x
  have hf : Function.Bijective f := by
    have : (e : KaehlerDifferential A T → KaehlerDifferential L T) = f := funext he
    rw [← this]
    exact e.bijective
  exact LinearEquiv.ofBijective f hf

theorem localBaseDifferentialEquiv_D
    (A : Type u) (T : Type v) (L : Type w)
    [CommRing A] [CommRing T] [CommRing L]
    [Algebra A T] [Algebra A L] [Algebra L T] [IsScalarTower A L T]
    (U : Submonoid A) [IsLocalization U L] (t : T) :
    localBaseDifferentialEquiv A T L U (KaehlerDifferential.D A T t) =
      KaehlerDifferential.D L T t := by
  exact KaehlerDifferential.map_D A L T T t

theorem cotangent_fiber_comparison :
    Specs.AdvCommAlg.Differentials.CotangentFibers.cotangentComparison.{u,v} := by
  intro A B _ _ _ p q _ _ _
  let C := p.ResidueField ⊗[A] B
  let K := q.ResidueField
  letI : Algebra C K :=
    (Specs.AdvCommAlg.Differentials.CotangentFibers.fiberPointValue A B p q).toRingHom.toAlgebra
  haveI : IsScalarTower B C K := IsScalarTower.of_algebraMap_eq (fun b => by
    change algebraMap B K b =
      Specs.AdvCommAlg.Differentials.CotangentFibers.fiberPointValue A B p q (1 ⊗ₜ[A] b)
    rw [cotangentFiberPoint_apply, one_smul])
  let e : K ⊗[B] KaehlerDifferential A B ≃ₗ[K]
      K ⊗[C] KaehlerDifferential p.ResidueField C :=
    (AlgebraTensorModule.cancelBaseChange B C K K (KaehlerDifferential A B)).symm.trans
      (LinearEquiv.baseChange C K _ _ (baseChangeEquiv A p.ResidueField B C))
  have he (k : K) (b : B) : e (k ⊗ₜ KaehlerDifferential.D A B b) =
      k ⊗ₜ KaehlerDifferential.D p.ResidueField C (1 ⊗ₜ[A] b) := by
    change k ⊗ₜ[C] (baseChangeEquiv A p.ResidueField B C)
      (1 ⊗ₜ[B] KaehlerDifferential.D A B b) = _
    congr 1
    simpa only [baseChangeEquiv, Specs.AdvCommAlg.Differentials.baseChangeEquivValue,
      one_smul, C, Algebra.TensorProduct.right_algebraMap_apply]
      using baseChange_formula A p.ResidueField B C 1 b
  let T := Localization.AtPrime q
  let L := Localization.AtPrime p
  let t : T ⊗[B] KaehlerDifferential A B ≃ₗ[T] KaehlerDifferential L T :=
    (differential_isBaseChange A B T q.primeCompl).equiv.trans
      (localBaseDifferentialEquiv A T L p.primeCompl)
  have ht (b : B) : t (1 ⊗ₜ KaehlerDifferential.D A B b) =
      KaehlerDifferential.D L T (algebraMap B T b) := by
    dsimp [t]
    rw [one_smul, KaehlerDifferential.map_D, localBaseDifferentialEquiv_D]
  let l : K ⊗[B] KaehlerDifferential A B ≃ₗ[K]
      K ⊗[T] KaehlerDifferential L T :=
    (AlgebraTensorModule.cancelBaseChange B T K K (KaehlerDifferential A B)).symm.trans
      (LinearEquiv.baseChange T K _ _ t)
  have hl (k : K) (b : B) : l (k ⊗ₜ KaehlerDifferential.D A B b) =
      k ⊗ₜ KaehlerDifferential.D L T (algebraMap B T b) := by
    change k ⊗ₜ[T] t (1 ⊗ₜ[B] KaehlerDifferential.D A B b) = _
    rw [ht]
  refine ⟨e, l, l.symm.trans e, he, hl, ?_, ?_⟩
  · intro k b
    change e (l.symm _) = _
    rw [← hl, LinearEquiv.symm_apply_apply, he]
  · intro x
    exact congrArg e (l.symm_apply_apply x)

end
end AdvCommAlg.Differentials
