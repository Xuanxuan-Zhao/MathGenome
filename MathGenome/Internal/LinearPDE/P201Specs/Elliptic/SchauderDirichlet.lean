import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.SchauderRegularity

/-!
Independent scope of `pde:elliptic-schauder-solvability`, paper.tex:2129–2145.
The bounded open set may be empty or disconnected. Writing the dimension as
m + 1 includes every positive dimension, in particular intervals when m = 0.
Boundary regularity and derivatives are the canonical one-sided graph-chart
and within-derivative objects from VariableSchauder and ConstantSchauder.
No solution or existence certificate is included in the data.
-/
noncomputable section
open Set Metric
open scoped ContDiff

namespace P201Specs.Elliptic.SchauderDirichlet
open NewtonHessian PoissonSchauder ConstantSchauder VariableSchauder

/-- A classical solution with the full C²,α class on the closed domain.
Ambient representatives need only agree with the prescribed lift on ∂Ω. -/
def IsDirichletSolution {n : ℕ} (α : ℝ) (Ω : Domain n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c f G u : Space n → ℝ) : Prop :=
  IsC2HolderUpToOn α u (closure (Ω : Set (Space n))) ∧
    (∀ x ∈ Ω, nondivergenceOperator a b c u x = f x) ∧
    ∀ x ∈ frontier (Ω : Set (Space n)), u x = G x

/-- Arbitrary-domain existence, uniqueness on Ω̄, and the estimate without
‖u‖C⁰. The constant is chosen before the coefficients, source and boundary
lift, with dependence only on the dimension, domain, exponent, ellipticity
and a bound for the coefficient norms. No connectedness hypothesis is used. -/
def SolvabilityStatement : Prop :=
  ∀ m : ℕ, ∀ α : ℝ, 0 < α → α < 1 → ∀ Ω : Domain (m + 1),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasC2HolderBoundary α Ω →
    ∀ ell K : ℝ, 0 < ell → 0 ≤ K →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
          (b : Space (m + 1) → Space (m + 1)) (c : Space (m + 1) → ℝ),
          UniformlyEllipticOn ell a (closure (Ω : Set (Space (m + 1)))) →
          CoefficientsHolderOn α a b c (closure (Ω : Set (Space (m + 1)))) →
          coefficientNormOn α a b c (closure (Ω : Set (Space (m + 1)))) ≤ K →
          (∀ x ∈ closure (Ω : Set (Space (m + 1))), c x ≤ 0) →
          ∀ f G : Space (m + 1) → ℝ,
            IsHolderOn α f (closure (Ω : Set (Space (m + 1)))) →
            IsC2HolderUpToOn α G (closure (Ω : Set (Space (m + 1)))) →
            ∃ u : Space (m + 1) → ℝ,
              IsDirichletSolution α Ω a b c f G u ∧
              c2HolderUpToNormOn α u (closure (Ω : Set (Space (m + 1)))) ≤
                C * (holderNormOn α f (closure (Ω : Set (Space (m + 1)))) +
                  c2HolderUpToNormOn α G (closure (Ω : Set (Space (m + 1))))) ∧
              ∀ v : Space (m + 1) → ℝ,
                IsDirichletSolution α Ω a b c f G v →
                  EqOn v u (closure (Ω : Set (Space (m + 1))))

/-- Full initially C² local assertion, with only local coefficient regularity
and local ellipticity, and no sign condition on c. -/
def LocalRegularityStatement : Prop :=
  SchauderRegularity.LocalRegularityStatement

/-- The original nested-domain estimate for initially C² solutions, with
constants and finiteness hypotheses unchanged from SchauderRegularity. -/
def InteriorEstimateStatement : Prop :=
  SchauderRegularity.InteriorEstimateStatement

end P201Specs.Elliptic.SchauderDirichlet
