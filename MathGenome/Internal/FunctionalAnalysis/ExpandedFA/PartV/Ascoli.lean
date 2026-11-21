import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.Ascoli
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
Arzelà–Ascoli on arbitrary compact Hausdorff domains.

For sufficiency, the isometric equivalence between continuous maps on a
compact domain and bounded continuous functions transports Mathlib's
compact-closure theorem. The common scalar bound gives a compact closed ball
in ℝ or ℂ. For necessity, a finite uniform ε/3-net and the continuity of its
finitely many centers give a single neighborhood valid for the whole family.
All covers and bounds below allow empty families and empty domains.
-/

open Set Filter
open scoped Topology

universe u v
namespace ExpandedFA.PartV.Ascoli

/-- A family with compact closure in the supremum norm is equicontinuous,
without a metric or countability assumption on its domain. -/
theorem equicontinuous_of_isCompact_closure
    {X : Type v} {E : Type u} [TopologicalSpace X] [CompactSpace X]
    [PseudoMetricSpace E] {A : Set C(X, E)} (hA : IsCompact (closure A)) :
    Equicontinuous (fun (f : A) (x : X) => (f : C(X, E)) x) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨t, _, ht, hcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hA (div_pos hε (by norm_num : (0 : ℝ) < 3))
  have hcenters : ∀ᶠ y in 𝓝 x, ∀ g ∈ t, dist (g x) (g y) < ε / 3 := by
    apply (eventually_all_finite ht).mpr
    intro g hg
    exact (g.continuous.tendsto x).eventually (Metric.ball_mem_nhds (g x)
      (div_pos hε (by norm_num : (0 : ℝ) < 3))) |>.mono fun y hy => by
        simpa only [Metric.mem_ball, dist_comm] using hy
  filter_upwards [hcenters] with y hy f
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hcover f.property)
  have hdist : dist (f : C(X, E)) g < ε / 3 := hfg
  calc
    dist (f.val x) (f.val y) ≤
        dist (f.val x) (g x) + dist (g x) (g y) + dist (g y) (f.val y) :=
      dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 :=
      add_lt_add (add_lt_add ((ContinuousMap.dist_apply_le_dist x).trans_lt hdist)
        (hy g hg)) (by
          rw [dist_comm]
          exact (ContinuousMap.dist_apply_le_dist y).trans_lt hdist)
    _ = ε := by ring

/-- The full real/complex compact Hausdorff Arzelà–Ascoli equivalence. -/
theorem arzela_ascoli : Spec.ArzelaAscoli.{u, v} := by
  intro 𝕜 X _ _ _ _ A
  constructor
  · intro hA
    obtain ⟨M, hM, hbound⟩ := hA.isBounded.exists_pos_norm_le
    refine ⟨⟨M, hM.le, fun f hf x => (f.norm_coe_le_norm x).trans
      (hbound f (subset_closure hf))⟩, equicontinuous_of_isCompact_closure hA⟩
  · rintro ⟨⟨M, hM, hbound⟩, heq⟩
    let e := ContinuousMap.isometryEquivBoundedOfCompact X 𝕜
    have heq' : Equicontinuous (fun (f : e '' A) (x : X) => f.val x) := by
      let r : (e '' A) → A := fun f =>
        ⟨e.symm f.val, by
          obtain ⟨g, hg, hgf⟩ := f.property
          simpa only [← hgf, e.symm_apply_apply] using hg⟩
      simpa only [Function.comp_def, r, e,
        ContinuousMap.isometryEquivBoundedOfCompact_symm_apply,
        BoundedContinuousFunction.coe_toContinuousMap] using heq.comp r
    have hc : IsCompact (closure (e '' A)) :=
      BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : 𝕜) M)
        (isCompact_closedBall _ _) (e '' A)
        (by
          intro f x hf
          obtain ⟨g, hg, rfl⟩ := hf
          rw [Metric.mem_closedBall, dist_zero_right]
          change ‖g x‖ ≤ M
          exact hbound g hg x)
        heq'
    have hc' : IsCompact (e '' closure A) := by
      change IsCompact (e.toHomeomorph '' closure A)
      rw [e.toHomeomorph.image_closure]
      exact hc
    exact e.toHomeomorph.isCompact_image.mp hc'

end ExpandedFA.PartV.Ascoli
