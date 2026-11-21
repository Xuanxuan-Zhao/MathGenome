import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.UniformImproper

/-! K03.18.dirichlet_integral, paper.tex:4251–4291.
All integrals below are limits of proper Darboux integrals; no absolute
integrability at damping zero is imposed. The tail estimates include a = 0.
The function is the canonical continuous sinc, with its value at zero explicit.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.DirichletIntegral
open Set Filter
open scoped Topology
open Ch10.OneEndpoint Ch14.UniformImproper
abbrev damped := DampedSineIntegral.integrandValue

def sincRepresentation : Prop :=
  Real.sinc 0 = 1 ∧ Continuous Real.sinc ∧
    ∀ x : ℝ, x ≠ 0 → Real.sinc x = Real.sin x / x

def finiteTailBound : Prop := ∀ a : ℝ, 0 ≤ a → ∀ R : ℝ, 0 < R →
  ∀ S : ℝ, R ≤ S → ∃ h : Ch08.Integral.realIntegrableValue (damped a) R S,
    |Ch08.Integral.realIntegralValue (damped a) h| ≤ 2 / R

def infiniteTailBound : Prop := ∀ a : ℝ, 0 ≤ a → ∀ R : ℝ, 0 < R →
  ∃ L : ℝ, rightHasIntegralValue .real (damped a) R ⊤ L ∧ |L| ≤ 2 / R

/-- Uniform convergence on each compact initial interval as damping decreases to zero. -/
def compactUniform : Prop := ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε →
  ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 ≤ a → a < δ →
    ∀ x ∈ Icc 0 R, |damped a x - Real.sinc x| < ε

/-- One truncation threshold works for every nonnegative damping parameter. -/
def uniformTruncations : Prop :=
  rightUniformConvergesValue .real (Ici (0 : ℝ))
    (fun x a => damped a.val x) 0 ⊤

/-- Removal of damping identifies the ordinary undamped limit with the
right-hand parameter limit of the already defined damped integrals. -/
def removalOfDamping : Prop := ∃ L : ℝ,
  rightHasIntegralValue .real Real.sinc 0 ⊤ L ∧
  Tendsto DampedSineIntegral.integralValue (𝓝[>] (0 : ℝ)) (𝓝 L)

def evaluation : Prop := rightHasIntegralValue .real Real.sinc 0 ⊤ (Real.pi / 2)

end Specs.SingleVariableAnalysis.Ch18.DirichletIntegral
