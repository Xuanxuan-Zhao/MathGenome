import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Continuity

/-!
Independent specification of `K03.12.continuity`, paper.tex:1220–1227.
The uniform-limit statements allow any metric domain, including a subtype
with its induced metric and the empty domain. Scalar targets are exactly
the canonical real and complex fields. No continuity of the limit is assumed.

For an open real domain `U`, functions are defined on the subtype `U`.
The convergence hypothesis is the upstream compact-subset definition of
locally uniform convergence, not global uniform convergence on `U`.
Indices use the upstream convention: `F n` is manuscript term `n + 1`.
-/

namespace Specs.SingleVariableAnalysis.Ch12.Continuity

universe u

def realUniformLimitContinuous : Prop :=
  ∀ {E : Type u} [MetricSpace E] (F : ℕ → E → ℝ) (f : E → ℝ),
    (∀ n, Continuous (F n)) → Uniform.realUniformConvergesValue F f → Continuous f

def complexUniformLimitContinuous : Prop :=
  ∀ {E : Type u} [MetricSpace E] (F : ℕ → E → ℂ) (f : E → ℂ),
    (∀ n, Continuous (F n)) → Uniform.complexUniformConvergesValue F f → Continuous f

def realLocallyUniformLimitContinuous : Prop :=
  ∀ {U : Set ℝ}, IsOpen U → ∀ (F : ℕ → U → ℝ) (f : U → ℝ),
    (∀ n, Continuous (F n)) → Uniform.realLocallyUniformConvergesValue F f → Continuous f

def complexLocallyUniformLimitContinuous : Prop :=
  ∀ {U : Set ℝ}, IsOpen U → ∀ (F : ℕ → U → ℂ) (f : U → ℂ),
    (∀ n, Continuous (F n)) → Uniform.complexLocallyUniformConvergesValue F f → Continuous f

end Specs.SingleVariableAnalysis.Ch12.Continuity
