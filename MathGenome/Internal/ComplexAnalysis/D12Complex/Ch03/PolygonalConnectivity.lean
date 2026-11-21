import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PolygonalConnectivity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathsChains
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.Clopen

open Set
open scoped Topology

namespace D12Complex

/-- Reachability by finitely many segments, proved from local convexity and
preconnectedness. This is the open-and-closed argument of the source lemma. -/
private theorem finite_segment_reachability (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hc : IsPreconnected Ω) (a : ℂ) (ha : a ∈ Ω) (b : ℂ) (hb : b ∈ Ω) :
    Relation.ReflTransGen (fun x y : ℂ => segment ℝ x y ⊆ Ω) a b := by
  apply hc.induction₂' (fun x y =>
    Relation.ReflTransGen (fun u v : ℂ => segment ℝ u v ⊆ Ω) x y) ?_ ?_ ha hb
  · intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    constructor
    · exact Relation.ReflTransGen.single
        (((convex_ball x r).segment_subset (Metric.mem_ball_self hr) hy).trans hball)
    · exact Relation.ReflTransGen.single
        (((convex_ball x r).segment_subset hy (Metric.mem_ball_self hr)).trans hball)
  · intro x y z _ _ _ hxy hyz
    exact hxy.trans hyz

/-- An ordered finite list of vertices, including both endpoints, with every
edge contained in the given open preconnected set. -/
theorem polygonal_connectivity (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (a : ℂ) (ha : a ∈ Ω) (b : ℂ) (hb : b ∈ Ω) :
    ∃ vertices : List ℂ,
      (a :: vertices).IsChain (fun x y => segment ℝ x y ⊆ Ω) ∧
      (a :: vertices).getLast (List.cons_ne_nil _ _) = b :=
  List.exists_isChain_cons_of_relationReflTransGen
    (finite_segment_reachability Ω hΩ hc a ha b hb)

/-- Concatenating the finitely many straight segments gives a continuous path. -/
theorem joinedIn_of_open_isPreconnected (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hc : IsPreconnected Ω) (a : ℂ) (ha : a ∈ Ω) (b : ℂ) (hb : b ∈ Ω) :
    JoinedIn Ω a b := by
  have h := finite_segment_reachability Ω hΩ hc a ha b hb
  induction h with
  | refl => exact JoinedIn.refl ha
  | tail _ hedge ih =>
    exact (ih (hedge (left_mem_segment ℝ _ _))).trans
      (JoinedIn.of_segment_subset hedge)

/-- The resulting path can be expressed using the project's canonical
compact-real-interval path, with its actual endpoints and trace. -/
theorem exists_complexPath_of_open_isPreconnected (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hc : IsPreconnected Ω) (a : ℂ) (ha : a ∈ Ω) (b : ℂ) (hb : b ∈ Ω) :
    ∃ γ : ComplexPath, γ.source = a ∧ γ.target = b ∧ γ.trace ⊆ Ω := by
  obtain ⟨p, hp⟩ := joinedIn_of_open_isPreconnected Ω hΩ hc a ha b hb
  let γ := ComplexPath.ofContinuousMap 0 1 zero_le_one p.toContinuousMap
  refine ⟨γ, ?_, ?_, ?_⟩
  · change γ 0 = a
    exact (ComplexPath.ofContinuousMap_apply 0 1 zero_le_one p.toContinuousMap
      ⟨0, le_rfl, zero_le_one⟩).trans p.source
  · change γ 1 = b
    exact (ComplexPath.ofContinuousMap_apply 0 1 zero_le_one p.toContinuousMap
      ⟨1, zero_le_one, le_rfl⟩).trans p.target
  · rintro z ⟨t, ht, rfl⟩
    change ComplexPath.ofContinuousMap 0 1 zero_le_one p.toContinuousMap t ∈ Ω
    exact (ComplexPath.ofContinuousMap_apply 0 1 zero_le_one p.toContinuousMap
      ⟨t, ht⟩).symm ▸ hp ⟨t, ht⟩

/-- In particular a nonempty open connected plane set is path connected. -/
theorem isPathConnected_of_open_isConnected (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hc : IsConnected Ω) : IsPathConnected Ω := by
  obtain ⟨a, ha⟩ := hc.nonempty
  exact ⟨a, ha, fun b hb => joinedIn_of_open_isPreconnected Ω hΩ hc.isPreconnected a ha b hb⟩

end D12Complex
