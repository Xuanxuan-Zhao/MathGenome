import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Primitive
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.LogConstruction

/-! K03.10.endpoint_counterexample, paper.tex:3223–3235.
Proper values are Darboux values, and both improper conditions use independent
one-sided truncations. The shared inverse-series logarithm is used only on
positive arguments. Ambient function values outside (0,1) carry no claims. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch10.EndpointCounterexample
open _root_.SingleVariableAnalysis
namespace I
export Ch08.Integral (realIntegrableValue realIntegralValue)
end I
namespace E
export Ch10.OneEndpoint
  (leftDivergesNegValue rightDivergesPosValue leftConvergesValue rightConvergesValue)
end E

abbrev integrandType := ℝ → ℝ
def integrandValue : integrandType := fun x => 1 / (1 - x) - 1 / x
abbrev primitiveType := ℝ → ℝ
def primitiveValue : primitiveType := fun x =>
  -Ch07.LogConstruction.seriesLogValue (1 - x) - Ch07.LogConstruction.seriesLogValue x

def primitiveDerivative : Prop :=
  ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt primitiveValue (integrandValue x) x

def properEvaluation : Prop := ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
  ∃ h : I.realIntegrableValue integrandValue a b,
    I.realIntegralValue integrandValue h = primitiveValue b - primitiveValue a

def primitiveSymmetry : Prop := ∀ x : ℝ, 0 < x → x < 1 →
  primitiveValue (1 - x) = primitiveValue x

def linkedZero : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
  ∃ h : I.realIntegrableValue integrandValue ε (1 - ε),
    I.realIntegralValue integrandValue h = 0

def linkedLimit : Prop :=
  ∃ h : (ε : {ε : ℝ // 0 < ε ∧ ε < 1 / 2}) →
      I.realIntegrableValue integrandValue ε.val (1 - ε.val),
    Filter.Tendsto (fun ε => I.realIntegralValue integrandValue (h ε))
      (Filter.comap Subtype.val (nhdsWithin (0 : ℝ) (Set.Ioi 0))) (nhds (0 : ℝ))

def leftDivergence : Prop := E.leftDivergesNegValue integrandValue (0 : WithBot ℝ) (1 / 2)
def rightDivergence : Prop := E.rightDivergesPosValue integrandValue (1 / 2) (1 : WithTop ℝ)

/-- The two divergent integrals in exactly the paper's ε parameterization. -/
def cutoffLimits : Prop :=
  ∃ hl : (ε : {ε : ℝ // 0 < ε ∧ ε < 1 / 2}) →
      I.realIntegrableValue integrandValue ε.val (1 / 2),
  ∃ hr : (ε : {ε : ℝ // 0 < ε ∧ ε < 1 / 2}) →
      I.realIntegrableValue integrandValue (1 / 2) (1 - ε.val),
    Filter.Tendsto (fun ε => I.realIntegralValue integrandValue (hl ε))
      (Filter.comap Subtype.val (nhdsWithin (0 : ℝ) (Set.Ioi 0))) Filter.atBot ∧
    Filter.Tendsto (fun ε => I.realIntegralValue integrandValue (hr ε))
      (Filter.comap Subtype.val (nhdsWithin (0 : ℝ) (Set.Ioi 0))) Filter.atTop

/-- Both independent finite conditions fail, so the ordinary improper integral
does not exist, despite the linked values being identically zero. -/
def endpointFailure : Prop :=
  ¬ E.leftConvergesValue .real integrandValue (0 : WithBot ℝ) (1 / 2) ∧
  ¬ E.rightConvergesValue .real integrandValue (1 / 2) (1 : WithTop ℝ) ∧
  ¬ Ch10.SeveralEndpoints.convergesValue .real integrandValue
    (0 : WithBot ℝ) (1 : WithTop ℝ)

end Specs.SingleVariableAnalysis.Ch10.EndpointCounterexample
