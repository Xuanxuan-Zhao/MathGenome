import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.FtcSecond
import Mathlib.Analysis.Real.Sqrt

/-! K03.09.area_length, graph-length clause (paper.tex:2701–2734).
The derivative is supplied as a continuous extension `g` on the closed interval.
Only interior derivatives are used, so no derivative of the arbitrary ambient
extension of `f` is required at an endpoint. This includes every C¹ function
with the manuscript's one-sided endpoint convention, and singleton intervals.
The length is the real supremum of exactly the finite strict-partition sums;
boundedness of this family is a separate conclusion, not a default of `sSup`.
-/
namespace Specs.SingleVariableAnalysis.Ch09.GraphLength
open Set
open Specs.SingleVariableAnalysis.Ch08
open _root_.SingleVariableAnalysis.Riemann
open scoped BigOperators

abbrev polygonalLengthType := (ℝ → ℝ) → {a b : ℝ} → PartitionData a b → ℝ
noncomputable def polygonalLengthValue : polygonalLengthType := fun f _ _ P =>
  ∑ i : Fin P.n, Real.sqrt ((P.point i.succ - P.point i.castSucc)^2 +
    (f (P.point i.succ) - f (P.point i.castSucc))^2)

abbrev graphLengthType := (ℝ → ℝ) → ℝ → ℝ → ℝ
noncomputable def graphLengthValue : graphLengthType := fun f a b =>
  sSup (Set.range (fun P : PartitionData a b => polygonalLengthValue f P))

/-- Finiteness and the proper Darboux integral formula, without an extra
integrability assumption. The `IsLUB` conclusion also characterizes the length. -/
def graphLengthFormula : Prop :=
  ∀ (f g : ℝ → ℝ) (a b : ℝ), a ≤ b →
    ContinuousOn f (Icc a b) → ContinuousOn g (Icc a b) →
    (∀ x ∈ Ioo a b, HasDerivAt f (g x) x) →
    ∃ h : Integral.realIntegrableValue (fun x => Real.sqrt (1 + (g x)^2)) a b,
      BddAbove (Set.range (fun P : PartitionData a b => polygonalLengthValue f P)) ∧
      IsLUB (Set.range (fun P : PartitionData a b => polygonalLengthValue f P))
        (Integral.realIntegralValue _ h) ∧
      graphLengthValue f a b = Integral.realIntegralValue _ h

def graphLengthDegenerate : Prop :=
  ∀ (f : ℝ → ℝ) (a : ℝ), graphLengthValue f a a = 0 ∧
    ∀ P : PartitionData a a, polygonalLengthValue f P = 0

end Specs.SingleVariableAnalysis.Ch09.GraphLength
