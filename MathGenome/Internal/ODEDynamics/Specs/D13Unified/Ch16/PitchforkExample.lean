import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.Pitchfork

/-! Independent specification of paper.tex, Chapter 16, the example
“The symmetry is a genuine hypothesis”. The parameter ranges over all real
numbers; attraction of the two nonzero branches holds for every μ > 0.
The shared maximal flow is used in coordinates y = x - p. -/
noncomputable section
open Set
namespace Specs.D13Unified.Ch16.PitchforkExample
open Ch01.AutonomousParameters
open Ch12.StabilityDefinitions

/-- The original polynomial family, in the shared (parameter,state) order. -/
def normalField (z : ℝ × ℝ) : ℝ := z.1 * z.2 - z.2 ^ 3

/-- An equilibrium attracting a neighborhood in its actual scalar equation.
The equation for y = x-p is specified everywhere on ℝ, so the existential ODE
cannot change the field or restrict the neighborhood to an artificial domain.
Both stability predicates include forward existence for nearby initial data. -/
def AttractingEquilibrium (μ p : ℝ) : Prop :=
  normalField (μ,p) = 0 ∧
  ∃ F : _root_.D13Unified.AutonomousODE ℝ,
    F.domain = univ ∧
    (∀ y : ℝ, autonomousEvalValue F y = normalField (μ,p+y)) ∧
    ∃ (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
      (h0 : (0 : ℝ) ∈ F.domain)
      (heq : autonomousEvalValue F 0 = 0),
      locallyExponentiallyStableValue F hF h0 heq ∧
      locallyAsymptoticallyStableValue F hF h0 heq

/-- Odd symmetry and the persistent zero equilibrium, for every parameter. -/
def persistentSymmetryBranch : Prop :=
  ∀ μ : ℝ, Function.Odd (fun x => normalField (μ,x)) ∧ normalField (μ,0) = 0

/-- Both square-root branches are equilibria and locally asymptotically
stable, with the stronger exponential conclusion, for every positive μ. -/
def stableBranches : Prop :=
  ∀ μ : ℝ, 0 < μ →
    AttractingEquilibrium μ (Real.sqrt μ) ∧ AttractingEquilibrium μ (-Real.sqrt μ)

/-- A nonzero constant perturbation removes odd symmetry and the equilibrium
at zero for every μ. Its equilibrium equation is the displayed perturbed
cubic, without any additional claim about a generic bifurcation type. -/
def constantPerturbation : Prop :=
  ∀ ε : ℝ, ε ≠ 0 → ∀ μ : ℝ,
    ¬ Function.Odd (fun x => normalField (μ,x) + ε) ∧
    normalField (μ,0) + ε ≠ 0 ∧
    ∀ x : ℝ, normalField (μ,x) + ε = 0 ↔ μ*x - x^3 + ε = 0

end Specs.D13Unified.Ch16.PitchforkExample
