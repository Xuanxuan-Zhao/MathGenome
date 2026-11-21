import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.SupNorm
import Mathlib.Topology.Instances.Real.Lemmas

/-!
Independent specification for K03.12.pointwise_discontinuous (paper.tex:1322–1327)
and its use in K03.12.dini (paper.tex:1230–1239).
The domain is exactly the real closed unit interval with its induced topology.
Lean index n represents the positive manuscript index n+1. Supremum errors use
upstream's extended nonnegative real supremum, so equality to 1 also asserts
finiteness. The limit is specified at every point, including both endpoints.
-/
namespace Specs.SingleVariableAnalysis.Ch12.PointwiseDiscontinuous

abbrev Domain := Set.Icc (0 : ℝ) 1

def powerSequenceType : Type := ℕ → Domain → ℝ

def powerSequenceValue : powerSequenceType := fun n x => (x : ℝ) ^ (n + 1)

def powerLimitType : Type := Domain → ℝ

noncomputable def powerLimitValue : powerLimitType := fun x => if (x : ℝ) = 1 then 1 else 0

def limitBelowOne : Prop :=
  ∀ (x : Domain), (x : ℝ) < 1 →
    Ch01.SequenceLimit.realSequenceConvergesValue (fun n => powerSequenceValue n x) 0

def valuesAtOne : Prop :=
  (∀ n, powerSequenceValue n ⟨1, ⟨zero_le_one, le_rfl⟩⟩ = 1) ∧
    powerLimitValue ⟨1, ⟨zero_le_one, le_rfl⟩⟩ = 1

def pointwiseLimit : Prop :=
  Pointwise.realPointwiseConvergesValue powerSequenceValue powerLimitValue

def continuousTerms : Prop := ∀ n, Continuous (powerSequenceValue n)

def discontinuousAtOne : Prop :=
  ¬ ContinuousAt powerLimitValue ⟨1, ⟨zero_le_one, le_rfl⟩⟩

def supremumError : Prop :=
  ∀ n, SupNorm.realSupErrorValue powerSequenceValue powerLimitValue n = 1

def notUniform : Prop :=
  ¬ Uniform.realUniformConvergesValue powerSequenceValue powerLimitValue

def noUniformLimit : Prop :=
  ¬ ∃ g : Domain → ℝ, Uniform.realUniformConvergesValue powerSequenceValue g

def decreasingTerms : Prop :=
  ∀ x : Domain, Antitone (fun n => powerSequenceValue n x)

/-- All hypotheses of decreasing Dini except continuity of the limit hold. -/
def diniCounterexample : Prop :=
  IsCompact (Set.Icc (0 : ℝ) 1) ∧
    (∀ n, Continuous (powerSequenceValue n)) ∧
    (∀ x : Domain, Antitone (fun n => powerSequenceValue n x)) ∧
    Pointwise.realPointwiseConvergesValue powerSequenceValue powerLimitValue ∧
    ¬ Continuous powerLimitValue ∧
    ¬ Uniform.realUniformConvergesValue powerSequenceValue powerLimitValue

end Specs.SingleVariableAnalysis.Ch12.PointwiseDiscontinuous
