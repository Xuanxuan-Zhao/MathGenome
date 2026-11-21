import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.SorgenfreyPlane
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.LocallyFiniteConventions

/-!
Independent statements for the Sorgenfrey-plane atlas entry and its explanation
in paper.tex, Chapter 18. The factors are the canonical lower-limit real line;
the square has exactly the product topology from Chapter 8. Normality and
paracompactness do not include Hausdorffness.
-/

namespace Specs.D10Topology.Ch18.SorgenfreyProductFailure

local instance : TopologicalSpace ℝ := Ch01.ElementaryTopologies.lowerLimitTopology
local instance : TopologicalSpace (ℝ × ℝ) := Ch08.SorgenfreyPlane.topology

/-- This one space supplies both factors of the counterexamples. -/
def factor_properties : Prop :=
  RegularSpace ℝ ∧ LindelofSpace ℝ ∧ NormalSpace ℝ ∧
    Ch15.LocallyFiniteConventions.Paracompact ℝ

/-- The actual square is Hausdorff and fails both asserted permanence properties. -/
def plane_properties : Prop :=
  T2Space (ℝ × ℝ) ∧ ¬ NormalSpace (ℝ × ℝ) ∧
    ¬ Ch15.LocallyFiniteConventions.Paracompact (ℝ × ℝ)

/-- Two normal factors whose product is not normal. -/
def normal_product_counterexample : Prop :=
  NormalSpace ℝ ∧ NormalSpace ℝ ∧ ¬ NormalSpace (ℝ × ℝ)

/-- Two paracompact factors whose product is not paracompact. -/
def paracompact_product_counterexample : Prop :=
  Ch15.LocallyFiniteConventions.Paracompact ℝ ∧
    Ch15.LocallyFiniteConventions.Paracompact ℝ ∧
    ¬ Ch15.LocallyFiniteConventions.Paracompact (ℝ × ℝ)

end Specs.D10Topology.Ch18.SorgenfreyProductFailure
