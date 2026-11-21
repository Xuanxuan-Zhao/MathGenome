import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.Weierstrass
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Higher
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform

/-!
Independent specification of K03.16.smooth_density (paper.tex:3938–3945).
The scalar cases are exactly ℝ and ℂ, and all derivatives have base field ℝ.
The approximants are actual scalar polynomials, evaluated on the real line,
with all orders of continuous derivatives there. The open set ℝ is in
particular a neighborhood of the compact interval. Uniform convergence uses
the shared epsilon definition on the interval subtype, including endpoints
and singleton intervals. No continuity of a putative limit is assumed in
the obstruction statements. Smooth approximants in those statements may
have different open neighborhoods for different indices.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch16.SmoothDensity

def realPolynomialDensity : Prop :=
  ∀ (a b : ℝ), a ≤ b → ∀ f : C(Set.Icc a b, ℝ),
    ∃ p : ℕ → Polynomial ℝ,
      (∀ n, Ch04.Higher.smoothOnValue (fun x : ℝ => (p n).eval x) Set.univ) ∧
      Ch12.Uniform.realUniformConvergesValue
        (fun n (x : Set.Icc a b) => (p n).eval (x : ℝ)) f

def complexPolynomialDensity : Prop :=
  ∀ (a b : ℝ), a ≤ b → ∀ f : C(Set.Icc a b, ℂ),
    ∃ p : ℕ → Polynomial ℂ,
      (∀ n, Ch04.Higher.smoothOnValue (fun x : ℝ => (p n).eval (x : ℂ)) Set.univ) ∧
      Ch12.Uniform.complexUniformConvergesValue
        (fun n (x : Set.Icc a b) => (p n).eval ((x : ℝ) : ℂ)) f

def realDiscontinuousNoContinuousLimit : Prop :=
  ∀ (a b : ℝ) (f : Set.Icc a b → ℝ), ¬ Continuous f →
    ¬ ∃ F : ℕ → Set.Icc a b → ℝ,
      (∀ n, Continuous (F n)) ∧ Ch12.Uniform.realUniformConvergesValue F f

def complexDiscontinuousNoContinuousLimit : Prop :=
  ∀ (a b : ℝ) (f : Set.Icc a b → ℂ), ¬ Continuous f →
    ¬ ∃ F : ℕ → Set.Icc a b → ℂ,
      (∀ n, Continuous (F n)) ∧ Ch12.Uniform.complexUniformConvergesValue F f

def realDiscontinuousNoSmoothLimit : Prop :=
  ∀ (a b : ℝ) (f : Set.Icc a b → ℝ), ¬ Continuous f →
    ¬ ∃ F : ℕ → ℝ → ℝ,
      (∀ n, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc a b ⊆ U ∧
        Ch04.Higher.smoothOnValue (F n) U) ∧
      Ch12.Uniform.realUniformConvergesValue (fun n (x : Set.Icc a b) => F n x) f

def complexDiscontinuousNoSmoothLimit : Prop :=
  ∀ (a b : ℝ) (f : Set.Icc a b → ℂ), ¬ Continuous f →
    ¬ ∃ F : ℕ → ℝ → ℂ,
      (∀ n, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc a b ⊆ U ∧
        Ch04.Higher.smoothOnValue (F n) U) ∧
      Ch12.Uniform.complexUniformConvergesValue (fun n (x : Set.Icc a b) => F n x) f

end Specs.SingleVariableAnalysis.Ch16.SmoothDensity
