import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C08ClosedGraph
import Mathlib.Analysis.Normed.Operator.Banach

/-!
The closed graph theorem, with explicit transport from the maximum product
norm to the manuscript's sum norm. Mathlib's closed graph theorem uses the
closed graph as a complete submodule and applies the Banach inverse theorem
to its first-coordinate projection. Its hypotheses include completeness of
both original spaces and do not require either space to be nonzero.
-/

open Filter Topology

universe u v w

namespace ExpandedFA.P1.C08ClosedGraph

/-- The identity on coordinates identifies sum-norm and native product
closed sets; the displayed norm really is the sum of the two norms. -/
theorem sum_product_geometry : Spec.SumProductGeometry.{v,w} := by
  intro E F _ _
  constructor
  · intro z
    simpa using WithLp.prod_norm_eq_add (p := 1) (by simp) z
  · intro s
    exact (WithLp.homeomorphProd 1 E F).isClosed_preimage

/-- Theorem `fa2:p1:c08:closed-graph`, including the sum-norm graph. -/
theorem closed_graph : Spec.ClosedGraph.{u,v,w} := by
  intro 𝕜 E F _ _ _ _ _ _ _ T
  have htransport :
      IsClosed {z : WithLp 1 (E × F) | (WithLp.ofLp z).2 = T (WithLp.ofLp z).1} ↔
        IsClosed (T.graph : Set (E × F)) :=
    (sum_product_geometry E F).2 (T.graph : Set (E × F))
  rw [htransport]
  constructor
  · rintro ⟨C, _, hC⟩
    have hT : Continuous T := (T.mkContinuous C hC).continuous
    exact isClosed_eq continuous_snd (hT.comp continuous_fst)
  · intro hgraph
    obtain ⟨C, hC, hbound⟩ :=
      SemilinearMapClass.bound_of_continuous T (T.continuous_of_isClosed_graph hgraph)
    exact ⟨C, hC.le, hbound⟩

/-- The sequential characterization of a closed graph. This equivalence
is purely metric and remains true without either completeness assumption. -/
theorem closed_graph_sequential : Spec.ClosedGraphSequential.{u,v,w} := by
  intro 𝕜 E F _ _ _ _ _ T
  have htransport :
      IsClosed {z : WithLp 1 (E × F) | (WithLp.ofLp z).2 = T (WithLp.ofLp z).1} ↔
        IsClosed (T.graph : Set (E × F)) :=
    (sum_product_geometry E F).2 (T.graph : Set (E × F))
  rw [htransport]
  constructor
  · intro hgraph x a b hx hTx
    exact hgraph.mem_of_tendsto (hx.prodMk_nhds hTx)
      (Filter.Eventually.of_forall (fun n => (rfl : T (x n) = T (x n))))
  · intro hseq
    apply IsSeqClosed.isClosed
    intro z p hz hp
    have hfst : Tendsto (fun n => (z n).1) atTop (𝓝 p.1) :=
      (continuous_fst.tendsto p).comp hp
    have hsnd : Tendsto (fun n => T (z n).1) atTop (𝓝 p.2) := by
      have heq : (fun n => T (z n).1) = (fun n => (z n).2) :=
        funext (fun n => (hz n).symm)
      rw [heq]
      exact (continuous_snd.tendsto p).comp hp
    exact hseq (fun n => (z n).1) p.1 p.2 hfst hsnd

end ExpandedFA.P1.C08ClosedGraph
