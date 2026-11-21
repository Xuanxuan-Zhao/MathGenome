import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24ContractionComparison
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Banach
import Mathlib.Topology.MetricSpace.Contracting

/-! The Banach contraction theorem applied to the complete closed-set subtype.
Mathlib's a priori estimate is valid also at contraction constant zero and
iteration index zero; only distance/norm and scalar-factor rewrites are needed.
-/

open Filter
open scoped Topology

namespace ExpandedFA.P1.C24ContractionComparison

universe u v

/-- What contraction adds: uniqueness, convergence from every starting point,
and the geometric a priori error bound, without convexity or compactness. -/
theorem contractionComparison :
    Spec.contractionComparison_type.{u, v} := by
  intro 𝕜 _ E _ _ hE D hD hclosed q hq hq1 T hT
  let : CompleteSpace E := (C01Banach.isBanachSpace_iff_completeSpace E).mp hE
  let : Nonempty D := hD.to_subtype
  let : CompleteSpace D := hclosed.isComplete.completeSpace_coe
  let K : NNReal := NNReal.mk q hq
  have hcontract : ContractingWith K T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
    · exact hq1
    · intro x y
      simpa only [Subtype.dist_eq, dist_eq_norm, K, NNReal.coe_mk] using hT x y
  let xstar : D := hcontract.fixedPoint T
  refine ⟨xstar, hcontract.fixedPoint_isFixedPt,
    (fun y hy => hcontract.fixedPoint_unique hy), ?_, ?_⟩
  · intro x
    exact continuous_subtype_val.continuousAt.tendsto.comp
      (hcontract.tendsto_iterate_fixedPoint x)
  · intro x n
    have h := hcontract.apriori_dist_iterate_fixedPoint_le x n
    change dist (((T^[n]) x : D) : E) (xstar : E) ≤
      dist (x : E) (T x : E) * q ^ n / (1 - q) at h
    rw [dist_comm (x : E) (T x : E), dist_eq_norm, dist_eq_norm] at h
    simpa only [div_mul_eq_mul_div, mul_comm (q ^ n)] using h

end ExpandedFA.P1.C24ContractionComparison
