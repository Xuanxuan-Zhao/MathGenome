import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.ParacompactNormal
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.LocallyFiniteConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions

/-!
Paracompact Hausdorff normality and closed-subspace heredity
(paper.tex, d10:15:normal).

Mathlib's Dieudonné theorem proves normality for paracompact R1 spaces;
Hausdorffness supplies R1 and, separately, T1. The accepted Chapter 7
conventions identify normality and regularity without building in T1.
The closed-embedding paracompactness theorem has no separation hypotheses.
-/

universe u

namespace D10Topology.Ch15

/-- Paracompact Hausdorff spaces are normal, in the convention without T1. -/
theorem paracompact_hausdorff_normal (X : Type u) [TopologicalSpace X]
    (hP : Paracompact X) (hH : Ch07.T2 X) : Ch07.Normal X := by
  let : ParacompactSpace X := hP
  let : T2Space X := hH
  exact NormalSpace.of_paracompactSpace_r1Space

/-- The manuscript's T4 conclusion includes the separately obtained T1 axiom. -/
theorem paracompact_hausdorff_t4 (X : Type u) [TopologicalSpace X]
    (hP : Paracompact X) (hH : Ch07.T2 X) : Ch07.T4 X := by
  let : T2Space X := hH
  exact ⟨paracompact_hausdorff_normal X hP hH, inferInstance⟩

/-- Regularity made explicit for subsequent shrinking and metrization arguments. -/
theorem paracompact_hausdorff_regular (X : Type u) [TopologicalSpace X]
    (hP : Paracompact X) (hH : Ch07.T2 X) : Ch07.Regular X := by
  let : T4Space X := (Ch07.t4_iff_mathlib X).mp (paracompact_hausdorff_t4 X hP hH)
  exact (T4Space.t3Space (X := X)).toRegularSpace

/-- Closed subspaces inherit paracompactness without any separation assumption. -/
theorem closed_subspace_paracompact {X : Type u} [TopologicalSpace X]
    (hP : Paracompact X) (Y : Set X) (hY : IsClosed Y) : Paracompact Y := by
  let : ParacompactSpace X := hP
  exact hY.isClosedEmbedding_subtypeVal.paracompactSpace

end D10Topology.Ch15
