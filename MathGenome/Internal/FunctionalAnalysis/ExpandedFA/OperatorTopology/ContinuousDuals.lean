import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OperatorTopology.ContinuousDuals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.OperatorTopology.Definitions
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Batteries.Tactic.OpenPrivate

/-! SOT and WOT are Hausdorff locally convex vector topologies, ordered
below the operator norm topology. Their scalar-linear duals are precisely
finite sums of vector evaluations followed by norm-continuous functionals.

For the nontrivial direction we extend from the evaluation image to the
product F^E using Hahn–Banach under a continuous seminorm. A continuous
product functional depends on finitely many coordinates. Separation by real
parts of scalar-linear functionals then gives the closed real-convex sets.
No completeness or nonzero-space assumptions are used. -/

namespace ExpandedFA.OperatorTopology
open scoped Topology
open Topology
noncomputable section

open private evaluationMap coefficientMap from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.OperatorTopology.Definitions

theorem strong_hausdorff : DualSpec.StrongHausdorff := by
  intro 𝕜 E F _ _ _ _ _
  let : TopologicalSpace (E →L[𝕜] F) := strongTopology 𝕜 E F
  exact (Function.Injective.isEmbedding_induced
    (f := evaluationMap 𝕜 E F) (fun _ _ h => ContinuousLinearMap.ext (congrFun h))).t2Space

theorem weak_hausdorff : DualSpec.WeakHausdorff := by
  intro 𝕜 E F _ _ _ _ _
  let : TopologicalSpace (E →L[𝕜] F) := weakTopology 𝕜 E F
  apply (Function.Injective.isEmbedding_induced (f := coefficientMap 𝕜 E F) ?_).t2Space
  intro T S h
  ext x
  exact (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).mpr fun g => congrFun h (x, g)

theorem strong_vector_topology : DualSpec.StrongVectorTopology := by
  intro 𝕜 E F _ _ _ _ _
  let : TopologicalSpace (E →L[𝕜] F) := strongTopology 𝕜 E F
  exact ⟨(strong_withSeminorms 𝕜 E F).isTopologicalAddGroup,
    (strong_withSeminorms 𝕜 E F).continuousSMul⟩

theorem weak_vector_topology : DualSpec.WeakVectorTopology := by
  intro 𝕜 E F _ _ _ _ _
  let : TopologicalSpace (E →L[𝕜] F) := weakTopology 𝕜 E F
  exact ⟨(weak_withSeminorms 𝕜 E F).isTopologicalAddGroup,
    (weak_withSeminorms 𝕜 E F).continuousSMul⟩

theorem strong_locally_convex : DualSpec.StrongLocallyConvex := by
  intro 𝕜 E F _ _ _ _ _
  let : TopologicalSpace (E →L[𝕜] F) := strongTopology 𝕜 E F
  let : Module ℝ (E →L[𝕜] F) := Module.restrictScalars ℝ 𝕜 (E →L[𝕜] F)
  let : IsScalarTower ℝ 𝕜 (E →L[𝕜] F) := .restrictScalars _ _ _
  exact (strong_withSeminorms 𝕜 E F).toLocallyConvexSpace

theorem weak_locally_convex : DualSpec.WeakLocallyConvex := by
  intro 𝕜 E F _ _ _ _ _
  let : TopologicalSpace (E →L[𝕜] F) := weakTopology 𝕜 E F
  let : Module ℝ (E →L[𝕜] F) := Module.restrictScalars ℝ 𝕜 (E →L[𝕜] F)
  let : IsScalarTower ℝ 𝕜 (E →L[𝕜] F) := .restrictScalars _ _ _
  exact (weak_withSeminorms 𝕜 E F).toLocallyConvexSpace

theorem topology_comparison : DualSpec.TopologyComparison := by
  intro 𝕜 E F _ _ _ _ _
  constructor
  · exact (strong_coarsest 𝕜 E F _).mp fun x => continuous_eval_const x
  · let : TopologicalSpace (E →L[𝕜] F) := strongTopology 𝕜 E F
    apply (weak_coarsest 𝕜 E F _).mp
    intro x g
    apply g.continuous.comp
    exact (continuous_pi_iff.mp continuous_induced_dom) x

/-- A scalar functional on an arbitrary product of normed spaces has finite
coordinate support. This includes the empty support and the zero functional. -/
theorem product_dual_finite_sum {𝕜 I F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (L : (I → F) →L[𝕜] 𝕜) :
    ∃ (s : Finset I) (g : I → F →L[𝕜] 𝕜), ∀ y, L y = ∑ i ∈ s, g i (y i) := by
  classical
  let p : SeminormFamily 𝕜 (I → F) I :=
    fun i => (normSeminorm 𝕜 F).comp (LinearMap.proj i)
  have hp : WithSeminorms p := by
    let e : I ≃ (Σ _ : I, Unit) := .symm <| .sigmaUnique _ _
    exact (withSeminorms_pi (fun _ : I => norm_withSeminorms 𝕜 F)).congr_equiv e
  obtain ⟨s, C, _, hb⟩ := Seminorm.bound_of_continuous hp L.toSeminorm L.continuous.norm
  have hz (y : I → F) (hy : ∀ i ∈ s, y i = 0) : L y = 0 := by
    have hsup : (s.sup p) y ≤ 0 :=
      Seminorm.finset_sup_apply_le le_rfl (fun i hi => by simp [p, hy i hi])
    have hnorm : ‖L y‖ ≤ 0 := (hb y).trans (by
      change (C : ℝ) * (s.sup p) y ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos C.coe_nonneg hsup)
    exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  refine ⟨s, fun i => L.comp (ContinuousLinearMap.single 𝕜 (fun _ : I => F) i), ?_⟩
  intro y
  have h := hz (y - ∑ i ∈ s, Pi.single i (y i)) (by
    intro i hi
    simp [Finset.sum_apply, Finset.sum_pi_single, hi])
  simpa only [map_sub, map_sum, sub_eq_zero, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.single_apply] using h

/-- Extend a continuous scalar functional from an injectively induced linear
subspace. The continuous dominating seminorm is transported before extension. -/
theorem extend_dual_of_induced {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
    [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y] [PolynormableSpace 𝕜 Y]
    (e : X →ₗ[𝕜] Y) (he : IsInducing e) (hi : Function.Injective e)
    (φ : X →ₗ[𝕜] 𝕜) (hφ : Continuous φ) :
    ∃ L : Y →L[𝕜] 𝕜, ∀ x, L (e x) = φ x := by
  let er : X ≃ₗ[𝕜] e.range := LinearEquiv.ofInjective e hi
  let f : e.range →ₗ[𝕜] 𝕜 := φ.comp er.symm.toLinearMap
  obtain ⟨q, hq, hb⟩ := Seminorm.exists_le_comp_of_isInducing
    (p := φ.toSeminorm) hφ.norm he
  obtain ⟨L, hL, _⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm e.range f hq
    (fun y => by
      have h := hb (er.symm y)
      simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.toSeminorm_apply, Seminorm.comp_apply,
        show e (er.symm y) = y.val from congrArg Subtype.val (er.apply_symm_apply y)] using h)
  refine ⟨L, fun x => ?_⟩
  have h := hL (er x)
  change L (e x) = φ (er.symm (er x)) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem strong_dual_finite_sum : DualSpec.StrongDualFiniteSum := by
  intro 𝕜 E F _ _ _ _ _ φ
  constructor
  · intro hφ
    let : TopologicalSpace (E →L[𝕜] F) := strongTopology 𝕜 E F
    obtain ⟨L, hL⟩ := extend_dual_of_induced (evaluationMap 𝕜 E F)
      ⟨rfl⟩ (fun _ _ h => ContinuousLinearMap.ext (congrFun h)) φ hφ
    obtain ⟨s, g, hg⟩ := product_dual_finite_sum L
    exact ⟨s, g, fun T => (hL T).symm.trans (hg _)⟩
  · rintro ⟨s, g, hg⟩
    let : TopologicalSpace (E →L[𝕜] F) := strongTopology 𝕜 E F
    have he (x : E) : Continuous (fun T : E →L[𝕜] F => T x) :=
      (continuous_pi_iff.mp continuous_induced_dom) x
    have h : (fun T => φ T) = (fun T => ∑ x ∈ s, g x (T x)) := funext hg
    rw [show (φ : (E →L[𝕜] F) → 𝕜) = _ from h]
    exact continuous_finsetSum _ (fun x _ => (g x).continuous.comp (he x))


theorem weak_dual_finite_sum : DualSpec.WeakDualFiniteSum := by
  intro 𝕜 E F _ _ _ _ _ φ
  constructor
  · intro hφ
    apply (strong_dual_finite_sum 𝕜 E F φ).mp
    exact continuous_iff_le_induced.mpr
      ((topology_comparison 𝕜 E F).2.trans (continuous_iff_le_induced.mp hφ))
  · rintro ⟨s, g, hg⟩
    let : TopologicalSpace (E →L[𝕜] F) := weakTopology 𝕜 E F
    have he (x : E) (g : F →L[𝕜] 𝕜) :
        Continuous (fun T : E →L[𝕜] F => g (T x)) :=
      (weak_coarsest 𝕜 E F _).mpr le_rfl x g
    rw [show (φ : (E →L[𝕜] F) → 𝕜) = (fun T => ∑ x ∈ s, g x (T x)) from funext hg]
    exact continuous_finsetSum _ (fun x _ => he x (g x))

theorem operator_duals_equal : DualSpec.DualsEqual := by
  intro 𝕜 E F _ _ _ _ _ φ
  exact (strong_dual_finite_sum 𝕜 E F φ).trans (weak_dual_finite_sum 𝕜 E F φ).symm

/-- Closed real-convex sets are intersections of closed half-spaces coming
from scalar-linear functionals. The preceding dual equality preserves them. -/
theorem closed_convex_sets_equal : DualSpec.ClosedConvexSets := by
  intro 𝕜 E F _ _ _ _ _
  let : Module ℝ (E →L[𝕜] F) := Module.restrictScalars ℝ 𝕜 (E →L[𝕜] F)
  let : IsScalarTower ℝ 𝕜 (E →L[𝕜] F) := .restrictScalars _ _ _
  intro C hC
  constructor
  · intro hclosed
    let : TopologicalSpace (E →L[𝕜] F) := strongTopology 𝕜 E F
    let : IsTopologicalAddGroup (E →L[𝕜] F) := (strong_withSeminorms 𝕜 E F).isTopologicalAddGroup
    let : ContinuousSMul 𝕜 (E →L[𝕜] F) := (strong_withSeminorms 𝕜 E F).continuousSMul
    let : LocallyConvexSpace ℝ (E →L[𝕜] F) := strong_locally_convex 𝕜 E F
    have heq := RCLike.iInter_halfSpaces_eq' (𝕜 := 𝕜) hC hclosed
    have hcont (f : (E →L[𝕜] F) →L[𝕜] 𝕜) :
        @Continuous _ _ (weakTopology 𝕜 E F) inferInstance f :=
      (operator_duals_equal 𝕜 E F f.toLinearMap).mp f.continuous
    rw [← heq]
    let : TopologicalSpace (E →L[𝕜] F) := weakTopology 𝕜 E F
    exact isClosed_iInter fun f => isClosed_iInter fun c => isClosed_iInter fun _ =>
      isClosed_le (RCLike.continuous_re.comp (hcont f)) continuous_const
  · intro hclosed
    exact hclosed.mono (topology_comparison 𝕜 E F).2

end
end ExpandedFA.OperatorTopology
