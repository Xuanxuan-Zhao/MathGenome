import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.ClosedPreimage
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.CompactInterval
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SupInf

/-!
Independent specification for K03.03.extreme_values, paper.tex:539–548.
Continuity is the upstream unpunctured epsilon–delta predicate, tested only
on E. Compactness is finite-open-subcover compactness in the induced metric.
The arbitrary metric domain includes intrinsic domains and metric subspaces.
Only real-valued extrema are ordered. Scalar boundedness is specified for
each of ℝ and ℂ, including empty compact domains; attainment requires E.Nonempty.
The last statements record the identity-function counterexamples in the proof.
-/
namespace Specs.SingleVariableAnalysis.Ch03.ExtremeValues

open Specs.SingleVariableAnalysis.Ch03.Continuity
universe u v

def compactRelativeContinuousImage : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X),
    IsCompact E → relativeContinuousValue f E → IsCompact (f '' E)

def realCompactMaximum : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X),
    IsCompact E → E.Nonempty → relativeContinuousValue f E →
      ∃ a ∈ E, ∀ x ∈ E, f x ≤ f a

def realCompactMinimum : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X),
    IsCompact E → E.Nonempty → relativeContinuousValue f E →
      ∃ a ∈ E, ∀ x ∈ E, f a ≤ f x

def realCompactBounded : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X),
    IsCompact E → relativeContinuousValue f E →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ E, |f x| ≤ M

def complexCompactBounded : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X),
    IsCompact E → relativeContinuousValue f E →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ E, ‖f x‖ ≤ M

def openUnitIdentityBounds : Prop :=
  relativeContinuousValue (fun x : ℝ => x) (Set.Ioo 0 1) ∧
    IsGLB ((fun x : ℝ => x) '' Set.Ioo 0 1) 0 ∧
    IsLUB ((fun x : ℝ => x) '' Set.Ioo 0 1) 1

def openUnitIdentityNoExtrema : Prop :=
  (¬ ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ≤ a) ∧
  (¬ ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∀ x ∈ Set.Ioo (0 : ℝ) 1, a ≤ x)

def realIdentityUnbounded : Prop :=
  relativeContinuousValue (fun x : ℝ => x) Set.univ ∧
    ¬ (∃ M : ℝ, ∀ x : ℝ, |(fun y : ℝ => y) x| ≤ M)

end Specs.SingleVariableAnalysis.Ch03.ExtremeValues
