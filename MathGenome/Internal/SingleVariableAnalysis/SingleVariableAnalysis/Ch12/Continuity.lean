import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Uniform
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.Continuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Continuity
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
Continuity of uniform limits (`K03.12.continuity`, paper.tex:1220–1227).

Mathlib's uniform approximation theorem uses the three-error argument
in uniform-space form. We apply it through the upstream epsilon bridges.
For locally uniform convergence, the upstream bridge on open real domains
uses compact neighborhoods to turn compact-subset convergence into local
uniform approximation. Thus this case requires neither global uniform
convergence nor compactness of the whole domain.
-/

namespace SingleVariableAnalysis

universe u

theorem realUniformLimit_continuous {E : Type u} [MetricSpace E]
    (F : ℕ → E → ℝ) (f : E → ℝ) (hF : ∀ n, Continuous (F n))
    (h : RealUniformConverges F f) : Continuous f :=
  ((realUniformConverges_iff F f).mp h).continuous
    (Filter.Eventually.of_forall hF).frequently

theorem complexUniformLimit_continuous {E : Type u} [MetricSpace E]
    (F : ℕ → E → ℂ) (f : E → ℂ) (hF : ∀ n, Continuous (F n))
    (h : ComplexUniformConverges F f) : Continuous f :=
  ((complexUniformConverges_iff F f).mp h).continuous
    (Filter.Eventually.of_forall hF).frequently

theorem realLocallyUniformLimit_continuous {U : Set ℝ} (hU : IsOpen U)
    (F : ℕ → U → ℝ) (f : U → ℝ) (hF : ∀ n, Continuous (F n))
    (h : RealLocallyUniformConverges F f) : Continuous f :=
  ((realLocallyUniformConverges_iff hU F f).mp h).continuous
    (Filter.Eventually.of_forall hF).frequently

theorem complexLocallyUniformLimit_continuous {U : Set ℝ} (hU : IsOpen U)
    (F : ℕ → U → ℂ) (f : U → ℂ) (hF : ∀ n, Continuous (F n))
    (h : ComplexLocallyUniformConverges F f) : Continuous f :=
  ((complexLocallyUniformConverges_iff hU F f).mp h).continuous
    (Filter.Eventually.of_forall hF).frequently

end SingleVariableAnalysis
