import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.SorgenfreyPlane
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.TychonoffCube

/-!
Independent statements for `paper.tex`, d10:07:normal-scope (subspace failure).
The domain is the real square with the already specified Sorgenfrey product
 topology. The codomain is the product of usual closed real unit intervals.
Normality has no implicit T₁ requirement. The image has the induced topology.
-/

open Set Topology
universe u

namespace Specs.D10Topology.Ch10.NormalSubspaceFailure

/-- All cubes, including the empty-index cube, are compact Hausdorff and normal. -/
def cube_compact_hausdorff_normal : Prop :=
  ∀ (ι : Type u),
    Ch05.Compactness.CoverCompact (TychonoffCube.Cube ι) ∧
      T2Space (TychonoffCube.Cube ι) ∧ NormalSpace (TychonoffCube.Cube ι)

local instance : TopologicalSpace (ℝ × ℝ) := Ch08.SorgenfreyPlane.topology

def sorgenfreyPlane_tychonoff : Prop :=
  Ch07.SeparationConventions.tychonoffValue (ℝ × ℝ)

/-- This is the actual evaluation embedding of the Sorgenfrey plane,
indexed by its continuous maps to the usual unit interval. -/
def sorgenfrey_cube_counterexample : Prop :=
  IsEmbedding (TychonoffCube.evaluationMap (X := ℝ × ℝ)) ∧
    Ch05.Compactness.CoverCompact
      (TychonoffCube.Cube (TychonoffCube.EvaluationIndex (ℝ × ℝ))) ∧
    T2Space (TychonoffCube.Cube (TychonoffCube.EvaluationIndex (ℝ × ℝ))) ∧
    NormalSpace (TychonoffCube.Cube (TychonoffCube.EvaluationIndex (ℝ × ℝ))) ∧
    ¬ NormalSpace (range (TychonoffCube.evaluationMap (X := ℝ × ℝ)))

/-- An explicit existential counterexample to hereditary normality, even
when the ambient space is a compact Hausdorff cube. -/
def normality_not_hereditary : Prop :=
  ∃ (ι : Type) (A : Set (TychonoffCube.Cube ι)),
    Ch05.Compactness.CoverCompact (TychonoffCube.Cube ι) ∧
      T2Space (TychonoffCube.Cube ι) ∧ NormalSpace (TychonoffCube.Cube ι) ∧
      ¬ NormalSpace A

end Specs.D10Topology.Ch10.NormalSubspaceFailure
