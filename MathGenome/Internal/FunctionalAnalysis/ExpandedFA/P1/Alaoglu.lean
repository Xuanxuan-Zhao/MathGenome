import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.Alaoglu
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13ScalarProductCompactness
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.WeakDual

/-! Alaoglu for neighborhood polars, without a norm on the TVS or local convexity.
The algebraic polar is closed in the product of scalar copies. Absorption bounds
its coordinates, and its neighborhood bound ensures that every member is
continuous. Compact scalar disk products therefore give the result. -/

namespace ExpandedFA.P1.Alaoglu

open Set Filter
open scoped Topology Pointwise
noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- A scalar-linear functional bounded on a zero neighborhood is continuous.
Continuity of its norm seminorm follows by scaling a single seminorm ball. -/
theorem continuous_of_neighborhood_bound (f : E →ₗ[𝕜] 𝕜)
    {U : Set E} (hU : U ∈ 𝓝 (0 : E)) (hf : ∀ x ∈ U, ‖f x‖ ≤ 1) :
    Continuous f := by
  apply WithSeminorms.continuous_of_continuous_comp (norm_withSeminorms 𝕜 𝕜) f
  intro i
  apply Seminorm.continuous' (r := 1)
  apply mem_of_superset hU
  intro x hx
  change ‖f (x - 0)‖ ≤ 1
  simpa only [sub_zero] using hf x hx

/-- The functions representing the polar form a closed subset of the entire
product space: linearity and the inequalities on U are closed conditions. -/
theorem isClosed_image_polar {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    IsClosed ((fun f : E →L[𝕜] 𝕜 => (f : E → 𝕜)) '' Spec.polar 𝕜 U) := by
  have heq : ((fun f : E →L[𝕜] 𝕜 => (f : E → 𝕜)) '' Spec.polar 𝕜 U) =
      range (fun f : E →ₗ[𝕜] 𝕜 => (f : E → 𝕜)) ∩
        {g : E → 𝕜 | ∀ x ∈ U, ‖g x‖ ≤ 1} := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f.toLinearMap, rfl⟩, hf⟩
    · rintro ⟨⟨f, rfl⟩, hf⟩
      exact ⟨⟨f, continuous_of_neighborhood_bound f hU hf⟩, hf, rfl⟩
  rw [heq]
  apply (LinearMap.isClosed_range_coe E 𝕜 (RingHom.id 𝕜)).inter
  simp only [ofPred_forall]
  exact isClosed_biInter fun x _ => isClosed_Iic.preimage (continuous_apply x).norm

/-- The general TVS form of Alaoglu. -/
theorem neighborhood_polar_isCompact : Spec.NeighborhoodPolarCompactness := by
  intro 𝕜 E _ _ _ _ _ _ _ U hU
  classical
  have habs (x : E) : ∃ (c : 𝕜) (u : E), u ∈ U ∧ c • u = x := by
    have hx : x ∈ (univ : Set 𝕜) • U := by
      rw [Set.univ_smul_nhds_zero hU]
      trivial
    simpa only [Set.mem_smul, mem_univ, true_and] using hx
  choose c u hu hcu using habs
  have hbound : (fun f : E →L[𝕜] 𝕜 => (f : E → 𝕜)) '' Spec.polar 𝕜 U ⊆
      {g : E → 𝕜 | ∀ x, ‖g x‖ ≤ ‖c x‖} := by
    rintro g ⟨f, hf, rfl⟩ x
    change ‖f x‖ ≤ ‖c x‖
    calc
      ‖f x‖ = ‖f (c x • u x)‖ := by rw [hcu x]
      _ = ‖c x‖ * ‖f (u x)‖ := by rw [map_smul, norm_smul]
      _ ≤ ‖c x‖ * 1 := mul_le_mul_of_nonneg_left (hf _ (hu x)) (norm_nonneg _)
      _ = ‖c x‖ := mul_one _
  have hc : IsCompact ((fun f : E →L[𝕜] 𝕜 => (f : E → 𝕜)) '' Spec.polar 𝕜 U) :=
    (compact_scalar_disk_products 𝕜 E (fun x => ‖c x‖) (fun _ => norm_nonneg _)).of_isClosed_subset
      (isClosed_image_polar hU) hbound
  let : TopologicalSpace (E →L[𝕜] 𝕜) := Spec.weakStarTopology 𝕜 E
  have he : Topology.IsEmbedding (fun f : E →L[𝕜] 𝕜 => (f : E → 𝕜)) := by
    refine ⟨⟨?_⟩, DFunLike.coe_injective⟩
    change TopologicalSpace.induced id
      (TopologicalSpace.induced (fun f : E →L[𝕜] 𝕜 => (f : E → 𝕜)) _) = _
    exact @induced_id (E →L[𝕜] 𝕜)
      (TopologicalSpace.induced (fun f : E →L[𝕜] 𝕜 => (f : E → 𝕜)) _)
  exact he.isCompact_iff.mpr hc

/-- The same zero neighborhood controls every member of an equicontinuous family. -/
theorem equicontinuous_subset_polar : Spec.EquicontinuousPolarContainment := by
  intro 𝕜 E _ _ _ _ _ _ _ A hA
  have h := (Metric.equicontinuousAt_iff_right.mp (hA 0)) 1 zero_lt_one
  refine ⟨{x : E | ∀ f : A, dist (f.1 0) (f.1 x) < 1}, h, ?_⟩
  intro f hf x hx
  exact le_of_lt (by simpa only [map_zero, dist_zero_left] using hx ⟨f, hf⟩)

/-- The normed corollary needs no completeness of E. -/
theorem dual_unit_ball_isCompact : Spec.UnitBallCompactness := by
  intro 𝕜 E _ _ _
  let : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  let e : (E →L[𝕜] 𝕜) ≃ₗ[𝕜] WeakDual 𝕜 E := StrongDual.toWeakDual
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  have he : Topology.IsInducing e := ⟨rfl⟩
  have hc := WeakDual.isCompact_closedBall (0 : E →L[𝕜] 𝕜) 1
  have hpre := he.isCompact_preimage' hc (by
    intro y _hy
    exact e.surjective y)
  simpa only [Set.preimage, Metric.closedBall, Set.mem_ofPred_eq, e,
    StrongDual.toStrongDual_toWeakDual, dist_zero_right] using hpre

end
end ExpandedFA.P1.Alaoglu
