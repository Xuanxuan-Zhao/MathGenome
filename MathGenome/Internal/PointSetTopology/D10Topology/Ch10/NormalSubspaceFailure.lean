import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.NormalSubspaceFailure
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.SorgenfreyPlane
import MathGenome.Internal.PointSetTopology.D10Topology.Ch10.TychonoffCube
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Tychonoff
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.RealAndEuclideanCompactness

/-!
Normality fails to pass to arbitrary subspaces (paper.tex, d10:07:normal-scope).
The normal T₁ Sorgenfrey line is Tychonoff, as is its square. Its evaluation
embedding realizes that nonnormal square as a subspace of a cube. Tychonoff
compactness and compact Hausdorff normality give the ambient properties.
Normality of the image would transfer back through the embedding's
homeomorphism onto its range, contradicting the established plane example.
-/

open Set Topology
universe u

namespace D10Topology.Ch10

/-- The topology here is the product of the usual unit-interval topologies. -/
theorem cube_compact_hausdorff_normal (ι : Type u) :
    Ch05.CoverCompact (Cube ι) ∧ T2Space (Cube ι) ∧ Ch07.Normal (Cube ι) := by
  have hI : Ch05.CoverCompact unitInterval := Ch05.real_interval_compact 0 1
  have hC := Ch05.tychonoff_product (fun _ : ι => inferInstance) (fun _ => hI)
  rw [Ch03.productTopology_eq_pi] at hC
  exact ⟨hC, inferInstance, Ch07.compact_hausdorff_normal hC⟩

section SorgenfreyPlane
local instance : TopologicalSpace (ℝ × ℝ) := Ch08.sorgenfreyPlaneTopology

/-- Complete regularity of the square follows from T₄ of each line,
not from the mere regularity of the square. -/
theorem sorgenfreyPlane_tychonoff : Ch07.Tychonoff (ℝ × ℝ) := by
  letI : TopologicalSpace ℝ := Ch01.lowerLimitTopology
  have hS : Ch07.Tychonoff ℝ := Ch07.t4_implies_tychonoff ℝ Ch08.sorgenfrey_t4
  letI : CompletelyRegularSpace ℝ := (Ch07.completelyRegular_iff_mathlib ℝ).mp hS.1
  letI : T2Space ℝ := hS.2
  exact ⟨(Ch07.completelyRegular_iff_mathlib (ℝ × ℝ)).mpr inferInstance, inferInstance⟩

/-- The image of the canonical evaluation embedding is the required
nonnormal subspace of a normal compact Hausdorff cube. -/
theorem sorgenfrey_cube_counterexample :
    IsEmbedding (evaluationMap (X := ℝ × ℝ)) ∧
      Ch05.CoverCompact (Cube (EvaluationIndex (ℝ × ℝ))) ∧
      T2Space (Cube (EvaluationIndex (ℝ × ℝ))) ∧
      Ch07.Normal (Cube (EvaluationIndex (ℝ × ℝ))) ∧
      ¬ Ch07.Normal (range (evaluationMap (X := ℝ × ℝ))) := by
  have he := tychonoff_evaluation_embedding sorgenfreyPlane_tychonoff
  obtain ⟨hC, hH, hN⟩ := cube_compact_hausdorff_normal (EvaluationIndex (ℝ × ℝ))
  refine ⟨he, hC, hH, hN, ?_⟩
  intro hImage
  letI : NormalSpace (range (evaluationMap (X := ℝ × ℝ))) := hImage
  exact Ch08.sorgenfreyPlane_not_normal he.toHomeomorph.symm.normalSpace

/-- Normality is not hereditary, even for compact Hausdorff ambient cubes. -/
theorem normality_not_hereditary :
    ∃ (ι : Type) (A : Set (Cube ι)),
      Ch05.CoverCompact (Cube ι) ∧ T2Space (Cube ι) ∧ Ch07.Normal (Cube ι) ∧
        ¬ Ch07.Normal A := by
  exact ⟨EvaluationIndex (ℝ × ℝ), range (evaluationMap (X := ℝ × ℝ)),
    sorgenfrey_cube_counterexample.2⟩

end SorgenfreyPlane
end D10Topology.Ch10
