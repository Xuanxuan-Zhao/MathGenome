import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.BohrMollerupSqueeze
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! K03.18.bohr_mollerup, paper.tex:4142–4171.
All assertions concerning Gamma or competing functions are on positive inputs.
The auxiliary extension by zero only makes the dependent integral value into a
real function; it places no extra condition on the characterization's domain.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.BohrMollerup

abbrev admissible := BohrMollerupSqueeze.admissible

def gammaExtension (x : ℝ) : ℝ :=
  if hx : 0 < x then GammaDefinition.gammaIntegralValue x hx else 0

def uniqueness : Prop := ∀ F : ℝ → ℝ, admissible F →
  ∀ (x : ℝ) (hx : 0 < x), F x = GammaDefinition.gammaIntegralValue x hx

def gammaSatisfies : Prop := admissible gammaExtension

abbrev multiplierType := ℝ → ℝ
def multiplierValue : multiplierType := fun x => 2 - Real.cos (2 * Real.pi * x)

def multiplierProperties : Prop :=
  (∀ x : ℝ, 0 < multiplierValue x) ∧
  Function.Periodic multiplierValue 1 ∧ multiplierValue 1 = 1 ∧
  ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ multiplierValue x ≠ multiplierValue y

/-- The exhibited competitor has normalization and recurrence, yet differs
from the same independently convergent improper Gamma integral. -/
def recurrenceNotUnique : Prop :=
  let F : ℝ → ℝ := fun x => gammaExtension x * multiplierValue x
  (∀ x : ℝ, 0 < x → 0 < F x) ∧ F 1 = 1 ∧
  (∀ x : ℝ, 0 < x → F (x + 1) = x * F x) ∧
  ∃ (x : ℝ) (hx : 0 < x), F x ≠ GammaDefinition.gammaIntegralValue x hx

end Specs.SingleVariableAnalysis.Ch18.BohrMollerup
