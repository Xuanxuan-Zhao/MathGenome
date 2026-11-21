import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.WeakNormFiniteRank
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace ExpandedFA.Supplements
noncomputable section
open scoped Topology

universe u v w
variable {𝕜 : Type u} {E : Type v} {F : Type w} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A weak-to-norm continuous operator has finite-dimensional range. -/
theorem finiteDimensional_range_of_weak_continuous (T : E →L[𝕜] F)
    (h : Continuous (fun x : WeakSpace 𝕜 E => T ((toWeakSpace 𝕜 E).symm x))) :
    FiniteDimensional 𝕜 T.range := by
  classical
  let L : WeakSpace 𝕜 E →ₗ[𝕜] F := T.toLinearMap.comp (toWeakSpace 𝕜 E).symm.toLinearMap
  let p : (E →L[𝕜] 𝕜) → Seminorm 𝕜 (WeakSpace 𝕜 E) :=
    (topDualPairing 𝕜 E).flip.toSeminormFamily
  let q : Seminorm 𝕜 (WeakSpace 𝕜 E) := (normSeminorm 𝕜 F).comp L
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_sum_of_continuous
    (LinearMap.weakBilin_withSeminorms (topDualPairing 𝕜 E).flip) q (continuous_norm.comp h)
  let V : E →ₗ[𝕜] (s → 𝕜) := LinearMap.pi fun f => (f.val : E →ₗ[𝕜] 𝕜)
  have hk : V.ker ≤ T.toLinearMap.ker := by
    intro x hx
    have hx' : ∀ f ∈ s, f x = 0 := by
      intro f hf
      exact congrFun (show V x = 0 from hx) ⟨f, hf⟩
    have hs : (∑ f ∈ s, p f) (toWeakSpace 𝕜 E x) = 0 := by
      change FunLike.coeAddMonoidHom _ _ _ (∑ f ∈ s, p f) (toWeakSpace 𝕜 E x) = 0
      simp only [map_sum, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro f hf
      change ‖f x‖ = 0
      rw [hx' f hf, norm_zero]
    have hb := hC (toWeakSpace 𝕜 E x)
    change ‖T x‖ ≤ C * (∑ f ∈ s, p f) (toWeakSpace 𝕜 E x) at hb
    rw [hs, mul_zero] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
  have : FiniteDimensional 𝕜 (E ⧸ V.ker) :=
    FiniteDimensional.of_injective V.quotKerEquivRange.toLinearMap
      V.quotKerEquivRange.injective
  let U := V.ker.liftQ T.toLinearMap hk
  have hr : U.range = T.toLinearMap.range := Submodule.range_liftQ _ _ _
  rw [← hr]
  infer_instance

/-- Coordinates on a finite-dimensional range are norm-continuous scalar
functionals, and therefore are weak-continuous tests on the original space. -/
theorem weak_continuous_of_finiteDimensional_range (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 T.range] :
    Continuous (fun x : WeakSpace 𝕜 E => T ((toWeakSpace 𝕜 E).symm x)) := by
  let b := Module.finBasis 𝕜 T.range
  let g : E →L[𝕜] (Fin (Module.finrank 𝕜 T.range) → 𝕜) :=
    b.equivFunL.toContinuousLinearMap.comp T.rangeRestrict
  have hg : Continuous (fun x : WeakSpace 𝕜 E => g ((toWeakSpace 𝕜 E).symm x)) := by
    apply continuous_pi
    intro j
    exact WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip
      ((ContinuousLinearMap.proj j).comp g)
  have hr := b.equivFunL.symm.continuous.comp hg
  have hf := continuous_subtype_val.comp hr
  change Continuous (fun x : WeakSpace 𝕜 E =>
    ((b.equivFunL.symm (b.equivFunL (T.rangeRestrict ((toWeakSpace 𝕜 E).symm x)))) : F)) at hf
  simp_rw [ContinuousLinearEquiv.symm_apply_apply] at hf
  exact hf

/-- Paper proposition `fa2:p1:weak-norm-finite-rank`, with the weak topology
supplied by the accepted dual-pair interface. -/
theorem weak_to_norm_continuous_iff_finite_rank : WeakNormFiniteRankSpec.Statement := by
  intro 𝕜 E F _ _ _ _ _ T
  rw [ExpandedFA.P1.dualPairTopology_weakSpace 𝕜 E]
  constructor
  · intro h
    apply finiteDimensional_range_of_weak_continuous T
    have hi : @Continuous (WeakSpace 𝕜 E) E inferInstance
        (TopologicalSpace.induced (toWeakSpace 𝕜 E) inferInstance)
        (toWeakSpace 𝕜 E).symm :=
      continuous_induced_rng.mpr continuous_id
    exact @Continuous.comp _ _ _ inferInstance
      (TopologicalSpace.induced (toWeakSpace 𝕜 E) inferInstance) inferInstance _ _ h hi
  · intro h
    have := h
    have hi : @Continuous E (WeakSpace 𝕜 E)
        (TopologicalSpace.induced (toWeakSpace 𝕜 E) (instTopologicalSpaceWeakSpace 𝕜 E))
        (instTopologicalSpaceWeakSpace 𝕜 E) (toWeakSpace 𝕜 E) :=
      continuous_iff_le_induced.mpr le_rfl
    exact @Continuous.comp E (WeakSpace 𝕜 E) F
      (TopologicalSpace.induced (toWeakSpace 𝕜 E) (instTopologicalSpaceWeakSpace 𝕜 E))
      (instTopologicalSpaceWeakSpace 𝕜 E) inferInstance
      _ _ (weak_continuous_of_finiteDimensional_range T) hi

end
end ExpandedFA.Supplements
