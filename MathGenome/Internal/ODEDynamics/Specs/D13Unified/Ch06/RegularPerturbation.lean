import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.CkDependence
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.LinearVolterra

/-! Independent statements of paper.tex, d13:06:perturbation-expansion.
The open domain is an arbitrary neighborhood of the reference graph; it need
not be a product or all of space. The reference is given only on the compact
interval, with within derivatives at included endpoints. -/
noncomputable section
open Set
namespace D13Unified.Ch06.RegularPerturbation
open C1Dependence
open Specs.D13Unified.Ch01.AutonomousParameters
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def trajectory (F : ParameterODE E ℝ) (s : ℝ) (ξ : ℝ → E) (ε t : ℝ) : E :=
  solution F (t,((s,ξ ε),ε))

def variation (F : ParameterODE E ℝ) (s : ℝ) (ξ : ℝ → E) (t : ℝ) : E :=
  stateVariation F s (ξ 0) 0 t (deriv ξ 0) + parameterVariation F s (ξ 0) 0 t 1

def referenceCoefficient (F : ParameterODE E ℝ) (x₀ : ℝ → E) (t : ℝ) : E →L[ℝ] E :=
  fderiv ℝ (fun x => parameterEvalValue F t x 0) (x₀ t)

def referenceForcing (F : ParameterODE E ℝ) (x₀ : ℝ → E) (t : ℝ) : E :=
  deriv (fun ε => parameterEvalValue F t (x₀ t) ε) 0

end D13Unified.Ch06.RegularPerturbation

namespace Specs.D13Unified.Ch06.RegularPerturbation
open _root_.D13Unified _root_.D13Unified.Ch06.C1Dependence
open _root_.D13Unified.Ch06.RegularPerturbation
open Ch01.AutonomousParameters Ch01.SolutionConcepts Ch04.MaximalSolutionMap
universe u

def FirstOrder : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ParameterODE E ℝ), ContDiffOn ℝ 1 (field F) F.domain →
    ∀ (ξ : ℝ → E), ContDiffAt ℝ 1 ξ 0 →
    ∀ (a b s : ℝ) (x₀ : ℝ → E), s ∈ Icc a b →
    compactSolutionOnValue (atParameterValue F 0) a b x₀ → ξ 0 = x₀ s →
      (∃ r > (0 : ℝ), ∀ ε, |ε| < r →
        ((s,ξ ε),ε) ∈ F.domain ∧
        Icc a b ⊆ (parameterMaximalIntervalValue F s (ξ ε) ε).carrier ∧
        compactSolutionOnValue (atParameterValue F ε) a b (trajectory F s ξ ε) ∧
        trajectory F s ξ ε s = ξ ε) ∧
      EqOn (trajectory F s ξ 0) x₀ (Icc a b) ∧
      HasDerivAt ξ (deriv ξ 0) 0 ∧
      _root_.D13Unified.Ch06.LinearVolterra.IsDifferentialSolution a b s (referenceCoefficient F x₀)
        (referenceForcing F x₀) (deriv ξ 0) (variation F s ξ) ∧
      (∀ z : ℝ → E,
        _root_.D13Unified.Ch06.LinearVolterra.IsDifferentialSolution a b s (referenceCoefficient F x₀)
          (referenceForcing F x₀) (deriv ξ 0) z → EqOn z (variation F s ξ) (Icc a b)) ∧
      ∀ η > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ε, |ε| < δ → ∀ t ∈ Icc a b,
        ‖trajectory F s ξ ε t - x₀ t - ε • variation F s ξ t‖ ≤ η * |ε|

def SecondOrder : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ParameterODE E ℝ), ContDiffOn ℝ 2 (field F) F.domain →
    ∀ (ξ : ℝ → E), ContDiffAt ℝ 2 ξ 0 →
    ∀ (a b s : ℝ) (x₀ : ℝ → E), s ∈ Icc a b →
    compactSolutionOnValue (atParameterValue F 0) a b x₀ → ξ 0 = x₀ s →
      ∃ C ≥ (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ε, |ε| < δ →
        (((s,ξ ε),ε) ∈ F.domain ∧
          Icc a b ⊆ (parameterMaximalIntervalValue F s (ξ ε) ε).carrier) ∧
        ∀ t ∈ Icc a b,
          ‖trajectory F s ξ ε t - x₀ t - ε • variation F s ξ t‖ ≤ C * ε^2

end Specs.D13Unified.Ch06.RegularPerturbation
