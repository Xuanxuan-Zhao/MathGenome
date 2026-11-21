import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.SorgenfreyProductFailure
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.SorgenfreyPlane
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.StandardParacompactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.ParacompactNormal

/-!
The Sorgenfrey plane witnesses failure of product permanence for normality and
paracompactness (paper.tex, Chapter 18, atlas and following paragraph).
Regular Lindelöf paracompactness applies to each canonical line. If their
Hausdorff square were paracompact, Chapter 15 would make it normal, contradicting
the Chapter 8 nonnormality theorem.
-/

namespace D10Topology.Ch18

local instance : TopologicalSpace ℝ := Ch01.lowerLimitTopology
local instance : TopologicalSpace (ℝ × ℝ) := Ch08.sorgenfreyPlaneTopology

theorem sorgenfrey_factor_properties :
    Ch07.Regular ℝ ∧ Ch08.Lindelof Ch01.lowerLimitTopology ∧
      Ch07.Normal ℝ ∧ Ch15.Paracompact ℝ :=
  ⟨Ch08.sorgenfrey_t3.1, Ch08.sorgenfrey_lindelof, Ch08.sorgenfrey_normal,
    Ch15.regular_lindelof_paracompact ℝ Ch08.sorgenfrey_t3.1
      Ch08.sorgenfrey_lindelof⟩

theorem sorgenfrey_plane_properties :
    Ch07.T2 (ℝ × ℝ) ∧ ¬ Ch07.Normal (ℝ × ℝ) ∧
      ¬ Ch15.Paracompact (ℝ × ℝ) := by
  have hH : Ch07.T2 (ℝ × ℝ) := by
    let : T3Space (ℝ × ℝ) :=
      (Ch07.t3_iff_mathlib (ℝ × ℝ)).mp Ch08.sorgenfreyPlane_t3
    infer_instance
  refine ⟨hH, Ch08.sorgenfreyPlane_not_normal, ?_⟩
  intro hP
  exact Ch08.sorgenfreyPlane_not_normal
    (Ch15.paracompact_hausdorff_normal (ℝ × ℝ) hP hH)

theorem sorgenfrey_normal_product_counterexample :
    Ch07.Normal ℝ ∧ Ch07.Normal ℝ ∧ ¬ Ch07.Normal (ℝ × ℝ) :=
  ⟨sorgenfrey_factor_properties.2.2.1, sorgenfrey_factor_properties.2.2.1,
    sorgenfrey_plane_properties.2.1⟩

theorem sorgenfrey_paracompact_product_counterexample :
    Ch15.Paracompact ℝ ∧ Ch15.Paracompact ℝ ∧
      ¬ Ch15.Paracompact (ℝ × ℝ) :=
  ⟨sorgenfrey_factor_properties.2.2.2, sorgenfrey_factor_properties.2.2.2,
    sorgenfrey_plane_properties.2.2⟩

end D10Topology.Ch18
