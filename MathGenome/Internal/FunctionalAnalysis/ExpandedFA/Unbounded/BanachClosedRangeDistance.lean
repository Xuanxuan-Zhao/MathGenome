import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachClosedRangeDistance
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08OpenMapping
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

noncomputable section

namespace ExpandedFA.Unbounded.BanachClosedRangeDistance

open Metric

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The second coordinate on the closed graph, with its inherited product norm. -/
def graphOutput (A : Operator 𝕜 X Y) : A.graph →L[𝕜] Y :=
  (ContinuousLinearMap.snd 𝕜 X Y).comp A.graph.subtypeL

@[simp] theorem graphOutput_apply (A : Operator 𝕜 X Y) (z : A.graph) :
    graphOutput A z = z.val.2 := rfl

theorem graphOutput_range (A : Operator 𝕜 X Y) :
    (graphOutput A).range = A.toFun.range := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, hx, hy⟩ := A.mem_graph_iff.mp z.property
    exact ⟨x, hy⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨((x : X), A x), A.mem_graph x⟩, rfl⟩

/-- Open mapping on the graph supplies the ambient distance bound. -/
theorem distance_bound_of_closed_range [CompleteSpace X] [CompleteSpace Y]
    (A : Operator 𝕜 X Y) (hA : A.IsClosed)
    (hr : _root_.IsClosed (A.toFun.range : Set Y)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : A.domain,
      infDist (x : X) (A.ker : Set X) ≤ C * ‖A x‖ := by
  let : CompleteSpace A.graph := hA.completeSpace_coe
  let T := graphOutput A
  have hTr : _root_.IsClosed (T.range : Set Y) := by
    simpa only [T, graphOutput_range] using hr
  let : CompleteSpace T.range := hTr.completeSpace_coe
  obtain ⟨C, hC, hpre⟩ :=
    ExpandedFA.P1.C08OpenMapping.open_mapping_controlled_preimages
      𝕜 A.graph T.range T.rangeRestrict (by
        rintro ⟨y, z, rfl⟩
        exact ⟨z, rfl⟩)
  refine ⟨C, hC, fun x => ?_⟩
  let gx : A.graph := ⟨((x : X), A x), A.mem_graph x⟩
  obtain ⟨z, hz, hzn⟩ := hpre (T.rangeRestrict gx)
  have hzout : z.val.2 = A x := congrArg Subtype.val hz
  obtain ⟨w, hw, hwout⟩ := A.mem_graph_iff.mp z.property
  have hker : ((x : X) - (w : X)) ∈ A.ker := by
    change ((x - w : A.domain) : X) ∈ A.ker
    rw [A.sub_mem_ker_iff]
    exact (hwout.trans hzout).symm
  calc
    infDist (x : X) (A.ker : Set X) ≤ dist (x : X) ((x : X) - (w : X)) :=
      infDist_le_dist_of_mem hker
    _ = ‖(w : X)‖ := by rw [dist_eq_norm, sub_sub_cancel]
    _ = ‖z.val.1‖ := congrArg norm hw
    _ ≤ ‖z‖ := norm_fst_le z.val
    _ ≤ C * ‖A x‖ := hzn

/-- The graph quotient norm is controlled by ambient distance plus output norm.
This comparison is the bridge from the X-norm estimate to a complete quotient. -/
theorem graphQuotient_norm_le (A : Operator 𝕜 X Y) (z : A.graph) :
    ‖(graphOutput A).ker.mkQ z‖ ≤
      infDist z.val.1 (A.ker : Set X) + ‖z.val.2‖ := by
  have h : ‖(graphOutput A).ker.mkQ z‖ - ‖z.val.2‖ ≤
      infDist z.val.1 (A.ker : Set X) := by
    apply (le_infDist A.ker.nonempty).mpr
    intro k hk
    let x : A.domain := ⟨k, A.ker_le_domain hk⟩
    have hx : A x = 0 := A.coe_mem_ker_iff.mp hk
    let w : A.graph := ⟨(k, 0), by simpa only [hx] using A.mem_graph x⟩
    have hw : w ∈ (graphOutput A).ker := by
      change w.val.2 = 0
      rfl
    have hwq : (graphOutput A).ker.mkQ w = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hw
    have hn : ‖(graphOutput A).ker.mkQ z‖ ≤ dist z.val.1 k + ‖z.val.2‖ := by
      calc
        ‖(graphOutput A).ker.mkQ z‖ =
            ‖(graphOutput A).ker.mkQ (z - w)‖ := by rw [map_sub, hwq, sub_zero]
        _ ≤ ‖z - w‖ := Submodule.Quotient.norm_mk_le _ _
        _ = max ‖z.val.1 - k‖ ‖z.val.2‖ := by
          change ‖(z.val.1 - k, z.val.2 - 0)‖ = _
          rw [sub_zero, Prod.norm_def]
        _ ≤ dist z.val.1 k + ‖z.val.2‖ := by
          rw [dist_eq_norm]
          exact max_le (le_add_of_nonneg_right (norm_nonneg _))
            (le_add_of_nonneg_left (norm_nonneg _))
    linarith
  linarith

set_option maxHeartbeats 800000 in
/-- The ambient distance estimate makes the graph-quotient map bounded below.
The quotient of the closed graph is complete, so its image is closed. -/
theorem closed_range_of_distance_bound [CompleteSpace X] [CompleteSpace Y]
    (A : Operator 𝕜 X Y) (hA : A.IsClosed) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ x : A.domain, infDist (x : X) (A.ker : Set X) ≤ C * ‖A x‖) :
    _root_.IsClosed (A.toFun.range : Set Y) := by
  let : CompleteSpace A.graph := hA.completeSpace_coe
  let T := graphOutput A
  let : _root_.IsClosed (T.ker : Set A.graph) := T.isClosed_ker
  let U : (A.graph ⧸ T.ker) →L[𝕜] Y := T.ker.liftQL T le_rfl
  have hnorm (q : A.graph ⧸ T.ker) : ‖q‖ ≤ (C + 1) * ‖U q‖ := by
    obtain ⟨z, rfl⟩ := T.ker.mkQ_surjective q
    obtain ⟨x, hx, hAx⟩ := A.mem_graph_iff.mp z.property
    have hdist : infDist z.val.1 (A.ker : Set X) ≤ C * ‖z.val.2‖ := by
      rw [← hx, ← hAx]
      exact hbound x
    calc
      ‖T.ker.mkQ z‖ ≤ infDist z.val.1 (A.ker : Set X) + ‖z.val.2‖ :=
        graphQuotient_norm_le A z
      _ ≤ C * ‖z.val.2‖ + ‖z.val.2‖ := add_le_add hdist le_rfl
      _ = (C + 1) * ‖U (T.ker.mkQ z)‖ := by
        change _ = (C + 1) * ‖z.val.2‖
        ring
  have hanti : AntilipschitzWith ⟨C + 1, by linarith⟩ U := by
    apply AntilipschitzWith.of_le_mul_dist
    intro q r
    change dist q r ≤ (C + 1) * dist (U q) (U r)
    simpa only [dist_eq_norm, ← U.map_sub] using hnorm (q - r)
  have hrange : Set.range U = (A.toFun.range : Set Y) := by
    rw [← graphOutput_range A]
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨z, rfl⟩ := T.ker.mkQ_surjective q
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨T.ker.mkQ z, rfl⟩
  rw [← hrange]
  apply hanti.isClosed_range
  exact ContinuousLinearMap.uniformContinuous (R₁ := 𝕜) (R₂ := 𝕜)
    (E₁ := A.graph ⧸ T.ker) (E₂ := Y) U

end ExpandedFA.Unbounded.BanachClosedRangeDistance

namespace ExpandedFA.Unbounded

/-- Closed range is equivalent to a uniform distance estimate in the original
ambient norm, for closed densely defined Banach-space operators. -/
theorem banach_closed_range_distance :
    BanachClosedRangeDistanceSpec.ClosedRangeDistance := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A _hd hA
  exact ⟨BanachClosedRangeDistance.distance_bound_of_closed_range A hA,
    fun ⟨C, hC, hbound⟩ =>
      BanachClosedRangeDistance.closed_range_of_distance_bound A hA C hC hbound⟩

end ExpandedFA.Unbounded
