import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.ModuleLocalization
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.P103.Ch04.RingLocalization
import Mathlib.Algebra.Module.TransferInstance

namespace P103.Ch04.ModuleLocalization

universe u v w x
open TensorProduct

theorem fractionEquality : ModuleLocalizationSpecs.FractionEquality.{u,v} := by
  intro R _ S M _ _ m n s t
  simp only [LocalizedModule.mk_eq, smul_sub, sub_eq_zero, Submonoid.smul_def]

theorem fractionZero : ModuleLocalizationSpecs.FractionZero.{u,v} := by
  intro R _ S M _ _ m s
  rw [← LocalizedModule.zero_mk (1 : S), LocalizedModule.mk_eq]
  simp only [smul_zero, one_smul, Submonoid.smul_def]

theorem everyElementIsFraction : ModuleLocalizationSpecs.EveryElementIsFraction.{u,v} := by
  intro R _ S M _ _ z
  induction z using LocalizedModule.induction_on with
  | _ m s => exact ⟨m, s, rfl⟩

theorem zeroDenominator : ModuleLocalizationSpecs.ZeroDenominator.{u,v} := by
  intro R _ S M _ _ h
  exact LocalizedModule.subsingleton h

noncomputable def tensorEquiv : ModuleLocalizationSpecs.TensorEquivType.{u,v} :=
  ModuleLocalizationSpecs.tensorEquivValue

theorem tensorFormula : ModuleLocalizationSpecs.TensorFormula.{u,v} := by
  intro R _ S M _ _ a s m
  exact (LocalizedModule.equivTensorProduct_symm_apply_tmul S m a s).trans
    (LocalizedModule.smul'_mk a m s)

theorem tensorInverseFormula : ModuleLocalizationSpecs.TensorInverseFormula.{u,v} := by
  intro R _ S M _ _ m s
  exact LocalizedModule.equivTensorProduct_apply_mk S m s

theorem tensorNaturality : ModuleLocalizationSpecs.TensorNaturality.{u,v,w} := by
  intro R _ S M N _ _ _ _ f z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul a m =>
    obtain ⟨r, s, rfl⟩ := RingLocalization.everyElementIsFraction R S a
    rw [TensorProduct.map_tmul, LinearMap.id_apply, tensorFormula R S N,
      tensorFormula R S M, LocalizedModule.map_mk, map_smul]


/-- Transporting the canonical first-factor action through the accepted
commutative comparison gives its action on the shared balanced tensor. -/
theorem balancedTensorEquiv : ModuleLocalizationSpecs.BalancedTensorEquiv.{u,v} := by
  intro R _ S M _ _
  obtain ⟨mR, _, _, cR, hc, hci⟩ :=
    P103.BalancedTensor.satisfiesCommutativeComparison R (Localization S) M
  letI := P103.BalancedTensor.commRightModule R (Localization S)
  letI := mR
  let c := cR.toAddEquiv
  letI act := c.module (Localization S)
  let cL : P103.BalancedTensor.Tensor R (Localization S) M ≃ₗ[Localization S]
      (Localization S ⊗[R] M) := c.linearEquiv (Localization S)
  let e := cL.trans (tensorEquiv R S M)
  refine ⟨act, ?_, e, ?_, ?_⟩
  · intro a b m
    apply cL.injective
    rw [map_smul]
    change a • cR (P103.BalancedTensor.tmul R b m) =
      cR (P103.BalancedTensor.tmul R (a * b) m)
    rw [hc, hc]
    exact (TensorProduct.smul_tmul' a b m).symm
  · intro a s m
    change tensorEquiv R S M (cR (P103.BalancedTensor.tmul R (Localization.mk a s) m)) = _
    rw [hc]
    exact tensorFormula R S M a s m
  · intro m s
    change cR.symm ((tensorEquiv R S M).symm (LocalizedModule.mk m s)) = _
    rw [show (tensorEquiv R S M).symm (LocalizedModule.mk m s) =
      Localization.mk 1 s ⊗ₜ[R] m from tensorInverseFormula R S M m s]
    exact hci _ _

theorem mapFormula : ModuleLocalizationSpecs.MapFormula.{u,v,w} := by
  intro R _ S M N _ _ _ _ f m s
  exact LocalizedModule.map_mk S f m s

theorem preservesExactness : ModuleLocalizationSpecs.PreservesExactness.{u,v,w,x} := by
  intro R _ S L M N _ _ _ _ _ _ f g h
  exact LocalizedModule.map_exact S f g h

theorem preservesInjectivity : ModuleLocalizationSpecs.PreservesInjectivity.{u,v,w} := by
  intro R _ S M N _ _ _ _ f h
  exact LocalizedModule.map_injective S f h

theorem preservesSurjectivity : ModuleLocalizationSpecs.PreservesSurjectivity.{u,v,w} := by
  intro R _ S M N _ _ _ _ f h
  exact LocalizedModule.map_surjective S f h

theorem finiteIntersections : ModuleLocalizationSpecs.FiniteIntersections.{u,v,w} := by
  intro R _ S M _ _ ι I P
  classical
  induction I using Finset.induction_on with
  | empty => simp [Submodule.localized]
  | @insert i I hi h =>
    simp only [Finset.iInf_insert]
    rw [Submodule.localized, Submodule.localized'_inf]
    change (P i).localized S ⊓ (⨅ j ∈ I, P j).localized S = _
    rw [h]

theorem flat : ModuleLocalizationSpecs.Flat.{u} := by
  intro R _ S
  exact IsLocalization.flat (Localization S) S

end P103.Ch04.ModuleLocalization
