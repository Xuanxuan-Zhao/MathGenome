import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.DerivativeUniformCauchy

/-!
Independent specification of K03.12.differentiation, paper.tex:1257–1277.
Functions on [a,b] are represented by ambient real-variable functions. No
conditions are imposed outside [a,b]. The resulting ambient function represents
the uniform limit on [a,b]; its derivative is asserted only in (a,b).
HasDerivAt includes existence of the finite derivative and its equality with g.
In particular no continuity or endpoint extension of the derivatives is assumed.
As upstream, index n represents manuscript index n+1.
-/

namespace Specs.SingleVariableAnalysis.Ch12.Differentiation

open Set

def realUniformConvergenceOfDerivatives : Prop :=
  ∀ (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a b x₀ : ℝ),
    a < b → x₀ ∈ Icc a b →
    (∀ n, ContinuousOn (F n) (Icc a b)) →
    (∀ n, ∀ x ∈ Ioo a b, DifferentiableAt ℝ (F n) x) →
    (∃ L : ℝ, Ch01.SequenceLimit.realSequenceConvergesValue (fun n => F n x₀) L) →
    Uniform.realUniformConvergesValue
      (fun n (x : Ioo a b) => deriv (F n) x) (fun x => g x) →
    ∃ f : ℝ → ℝ,
      Uniform.realUniformConvergesValue (fun n (x : Icc a b) => F n x) (fun x => f x) ∧
      ContinuousOn f (Icc a b) ∧
      ∀ x ∈ Ioo a b, HasDerivAt f (g x) x

def complexUniformConvergenceOfDerivatives : Prop :=
  ∀ (F : ℕ → ℝ → ℂ) (g : ℝ → ℂ) (a b x₀ : ℝ),
    a < b → x₀ ∈ Icc a b →
    (∀ n, ContinuousOn (F n) (Icc a b)) →
    (∀ n, ∀ x ∈ Ioo a b, DifferentiableAt ℝ (F n) x) →
    (∃ L : ℂ, Ch01.SequenceLimit.complexSequenceConvergesValue (fun n => F n x₀) L) →
    Uniform.complexUniformConvergesValue
      (fun n (x : Ioo a b) => deriv (F n) x) (fun x => g x) →
    ∃ f : ℝ → ℂ,
      Uniform.complexUniformConvergesValue (fun n (x : Icc a b) => F n x) (fun x => f x) ∧
      ContinuousOn f (Icc a b) ∧
      ∀ x ∈ Ioo a b, HasDerivAt f (g x) x

end Specs.SingleVariableAnalysis.Ch12.Differentiation
