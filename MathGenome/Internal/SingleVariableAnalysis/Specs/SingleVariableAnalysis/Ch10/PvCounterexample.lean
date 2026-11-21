import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.PrincipalValue
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.LogConstruction

/-! K03.10.pv_counterexample, paper.tex:3172–3183.
The integrand is the ambient extension `1 / x`; none of the proper
truncations includes zero. Integral values are the existing Darboux values.
The ordinary integral is tested by the independent finite-singularity API,
for every permitted choice of regular splits.
-/
namespace Specs.SingleVariableAnalysis.Ch10.PvCounterexample
open _root_.SingleVariableAnalysis
namespace E
export Ch10.OneEndpoint
  (rightRegularValue leftRegularValue rightTruncationValue leftTruncationValue
   rightConvergesValue leftConvergesValue rightDivergesNegValue leftDivergesPosValue)
end E
namespace I
export Ch08.Integral (realIntegrableValue realIntegralValue)
end I
namespace V
export Ch10.SeveralEndpoints (splitFamilyValue finiteConvergesValue)
end V
namespace P
export Ch10.PrincipalValue (interiorHasIntegralValue interiorRegularValue
  interiorIndexValue interiorTruncationValue)
end P

def truncationFormulas : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 →
  (∃ h : I.realIntegrableValue (fun x => 1 / x) (-1) (-ε),
    I.realIntegralValue _ h = Ch07.LogConstruction.seriesLogValue ε) ∧
  (∃ h : I.realIntegrableValue (fun x => 1 / x) ε 1,
    I.realIntegralValue _ h = -Ch07.LogConstruction.seriesLogValue ε)

def regular : Prop := P.interiorRegularValue .real (fun x => 1 / x) (-1) 1 0

def symmetricTruncation : Prop := ∀
  (h : P.interiorRegularValue .real (fun x => 1 / x) (-1) 1 0)
  (t : P.interiorIndexValue (-1) 1 0),
  P.interiorTruncationValue .real (fun x => 1 / x) (-1) 1 0 h t = 0

def principalValueZero : Prop :=
  P.interiorHasIntegralValue .real (fun x => 1 / x) (-1) 1 0 0

def oneSidedDivergence : Prop :=
  E.rightDivergesNegValue (fun x => 1 / x) (-1) (0 : WithTop ℝ) ∧
  E.leftDivergesPosValue (fun x => 1 / x) (0 : WithBot ℝ) 1

def oneSidedNonconvergence : Prop :=
  (¬ E.rightConvergesValue .real (fun x => 1 / x) (-1) (0 : WithTop ℝ)) ∧
  (¬ E.leftConvergesValue .real (fun x => 1 / x) (0 : WithBot ℝ) 1)

def independentNonconvergence : Prop := ∀
  (c : V.splitFamilyValue 1 (-1 : ℝ) (1 : ℝ) (fun _ => 0)),
  ¬ V.finiteConvergesValue .real (fun x => 1 / x) 1 (-1 : ℝ) (1 : ℝ) (fun _ => 0) c

end Specs.SingleVariableAnalysis.Ch10.PvCounterexample
