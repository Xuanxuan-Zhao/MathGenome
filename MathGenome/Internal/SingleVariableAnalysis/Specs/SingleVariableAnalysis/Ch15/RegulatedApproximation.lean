import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Partitions
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided
import Mathlib.Analysis.Normed.Group.Basic

/-! Independent specification for the approximation and boundedness portion of
K03.15.regulated, paper.tex:3610–3618. The later Riemann-integrability consequence
is assigned to Ch15.Regulated. Ambient functions are tested only on `[a,b]`.
One-sided limits use the existing nontrivial relative-limit interface. -/

namespace SingleVariableAnalysis

/-- Finite limits on both available sides; the actual values at the points
are unrestricted. In particular this definition has no BV hypothesis. -/
def RegulatedOn {E : Type*} [MetricSpace E] (f : ℝ → E) (a b : ℝ) : Prop :=
  (∀ c ∈ Set.Ioc a b, ∃ L : E,
    Specs.SingleVariableAnalysis.Ch02.OneSided.leftRelativeLimitValue
      f (Set.Icc a b) c L) ∧
  (∀ c ∈ Set.Ico a b, ∃ L : E,
    Specs.SingleVariableAnalysis.Ch02.OneSided.rightRelativeLimitValue
      f (Set.Icc a b) c L)

namespace Riemann

/-- Constancy is required on open cells only. All node values, including both
endpoints, are independent of the neighboring cell constants. -/
def IsStepOn {E : Type*} {a b : ℝ} (P : PartitionData a b) (s : ℝ → E) : Prop :=
  ∀ i : Fin P.n, ∃ v : E,
    ∀ x ∈ Set.Ioo (P.point i.castSucc) (P.point i.succ), s x = v

end Riemann
end SingleVariableAnalysis

namespace Specs.SingleVariableAnalysis.Ch15.RegulatedApproximation
open _root_.SingleVariableAnalysis

/-- A finite strict partition, a step approximant equal to f at every node,
an explicitly bounded error set, and a strict supremum error estimate.
The bound on the error set prevents use of a default real supremum. -/
def stepApproximation (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ f : ℝ → E, RegulatedOn f a b →
    ∀ ε : ℝ, 0 < ε → ∃ P : Riemann.PartitionData a b, ∃ s : ℝ → E,
      Riemann.IsStepOn P s ∧
      (∀ j : Fin (P.n + 1), s (P.point j) = f (P.point j)) ∧
      BddAbove ((fun x => ‖f x - s x‖) '' Set.Icc a b) ∧
      sSup ((fun x => ‖f x - s x‖) '' Set.Icc a b) < ε

def realStepApproximation : Prop := stepApproximation ℝ

def complexStepApproximation : Prop := stepApproximation ℂ

def realBoundedness : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ f : ℝ → ℝ, RegulatedOn f a b →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc a b, |f x| ≤ M

def complexBoundedness : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ f : ℝ → ℂ, RegulatedOn f a b →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M

end Specs.SingleVariableAnalysis.Ch15.RegulatedApproximation
