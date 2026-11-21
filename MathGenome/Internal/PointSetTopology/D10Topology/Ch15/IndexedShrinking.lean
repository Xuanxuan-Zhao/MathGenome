import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.IndexedShrinking
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.ParacompactNormal
import Mathlib.Topology.ShrinkingLemma

/-!
Indexed shrinking for paper.tex, d10:15:shrinking.

First obtain a locally finite precise refinement on the original index type.
It is point finite, so normality allows it to be shrunk, still on that index
type. The final family is locally finite because each of its members lies
inside the corresponding member of the locally finite refinement.
-/

open Set
universe u v

namespace D10Topology.Ch15

/-- Every indexed open cover of a paracompact Hausdorff space has a locally
finite open shrinking on the same indices. Members may be empty. -/
theorem indexed_shrinking {X : Type u} {I : Type v} [TopologicalSpace X]
    (hP : Paracompact X) (hH : Ch07.T2 X) (U : I → Set X)
    (ho : ∀ i, IsOpen (U i)) (hU : (⋃ i, U i) = univ) :
    ∃ V : I → Set X, (∀ i, IsOpen (V i)) ∧ LocallyFiniteFamily V ∧
      (⋃ i, V i) = univ ∧ ∀ i, closure (V i) ⊆ U i := by
  let : NormalSpace X := paracompact_hausdorff_normal X hP hH
  obtain ⟨B, hBo, hBf, hBcover, hBU⟩ := paracompact_precise_refinement hP U ho hU
  obtain ⟨V, hVcover, hVo, hVB⟩ :=
    exists_iUnion_eq_closure_subset hBo hBf.point_finite hBcover.1
  refine ⟨V, hVo, ?_, hVcover, fun i => (hVB i).trans (hBU i)⟩
  exact hBf.subset (fun i => subset_closure.trans (hVB i))

end D10Topology.Ch15
