import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.VariableSchauder
import Mathlib.Topology.ContinuousMap.Basic

/-!
Independent statements for the ball stages of classical Dirichlet solvability,
paper.tex:2147–2222. The sign is L = a:D² + b·D + c, with c ≤ 0.
Every positive dimension, including the interval with its two endpoints, is
quantified explicitly. Functions are ambient representatives; uniqueness means
equality on the closed ball, never equality outside it.

The continuous datum is a continuous map on the sphere itself. Its existence
statement assumes neither a Hölder extension nor global boundary regularity
of the solution. Local boundary regularity is a separate conclusion, not a
hypothesis of that existence statement. No solvability certificate is data.
-/
noncomputable section
open Set Metric
open scoped ContDiff

namespace P201Specs.Elliptic.BallSchauderSolvability
open NewtonHessian PoissonSchauder ConstantSchauder VariableSchauder

/-- The open ball, as the common open-domain object. -/
def ballDomain {n : ℕ} (z : Space n) (r : ℝ) : Domain n :=
  ⟨ball z r, isOpen_ball⟩

/-- A classical interior solution continuous on the closed ball, with its
actual continuous sphere datum. No derivatives on the sphere are assumed. -/
def IsBallSolution {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c f : Space n → ℝ)
    (z : Space n) (r : ℝ) (g : C(sphere z r, ℝ))
    (u : Space n → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (ball z r) ∧ ContinuousOn u (closedBall z r) ∧
    (∀ x ∈ ball z r, nondivergenceOperator a b c u x = f x) ∧
    ∀ ζ : sphere z r, u ζ = g ζ

/-- The global Hölder class with boundary values of an ambient lift G.
Derivatives on the boundary are the shared one-sided within derivatives. -/
def IsLiftedBallSolution {n : ℕ} (α : ℝ)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c f G : Space n → ℝ)
    (z : Space n) (r : ℝ) (u : Space n → ℝ) : Prop :=
  IsC2HolderUpToOn α u (closedBall z r) ∧
    (∀ x ∈ ball z r, nondivergenceOperator a b c u x = f x) ∧
    ∀ x ∈ sphere z r, u x = G x

/-- Lifted Hölder Dirichlet solvability and the estimate without a solution
C⁰ term. Constants are chosen before the coefficient fields, source and lift;
their allowed dependence is n, α, the ball, ellipticity and coefficient bounds.
Uniqueness is among all solutions in the stated global Hölder class. -/
def HolderSolvabilityStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ (z : Space n) (r : ℝ), 0 < r →
      ∀ ell K : ℝ, 0 < ell → 0 ≤ K →
        ∃ C : ℝ, 0 < C ∧
          ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
            (b : Space n → Space n) (c : Space n → ℝ),
            UniformlyEllipticOn ell a (closedBall z r) →
            CoefficientsHolderOn α a b c (closedBall z r) →
            coefficientNormOn α a b c (closedBall z r) ≤ K →
            (∀ x ∈ closedBall z r, c x ≤ 0) →
            ∀ f G : Space n → ℝ,
              IsHolderOn α f (closedBall z r) →
              IsC2HolderUpToOn α G (closedBall z r) →
              ∃ u : Space n → ℝ,
                IsLiftedBallSolution α a b c f G z r u ∧
                c2HolderUpToNormOn α u (closedBall z r) ≤
                  C * (holderNormOn α f (closedBall z r) +
                    c2HolderUpToNormOn α G (closedBall z r)) ∧
                ∀ v : Space n → ℝ,
                  IsLiftedBallSolution α a b c f G z r v →
                    EqOn v u (closedBall z r)

/-- Continuous sphere data, with no Hölder lift hypothesis. Uniqueness holds
even among initially only C² interior solutions continuous on the closed ball. -/
def ContinuousSolvabilityStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ (z : Space n) (r : ℝ), 0 < r →
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c : Space n → ℝ),
        (∃ ell : ℝ, 0 < ell ∧ UniformlyEllipticOn ell a (closedBall z r)) →
        CoefficientsHolderOn α a b c (closedBall z r) →
        (∀ x ∈ closedBall z r, c x ≤ 0) →
        ∀ f : Space n → ℝ, IsHolderOn α f (closedBall z r) →
          ∀ g : C(sphere z r, ℝ), ∃ u : Space n → ℝ,
            IsBallSolution a b c f z r g u ∧
            IsC2HolderLocOn α u (ballDomain z r) ∧
            ∀ v : Space n → ℝ, IsBallSolution a b c f z r g v →
              EqOn v u (closedBall z r)

/-- A continuous-data ball solution has C²,α regularity up to every smaller
spherical portion where the datum has a local C²,α lift. V̄ ⊆ U means that
the smaller portion stays away from the ends of U. There is no global norm
or lift hypothesis on g, and no assumed boundary regularity of u.
Local regularity of the lift suffices; its norm need not be finite on all U. -/
def LocalBoundaryRegularityStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ (z : Space n) (r : ℝ), 0 < r →
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c : Space n → ℝ),
        (∃ ell : ℝ, 0 < ell ∧ UniformlyEllipticOn ell a (closedBall z r)) →
        CoefficientsHolderOn α a b c (closedBall z r) →
        (∀ x ∈ closedBall z r, c x ≤ 0) →
        ∀ f : Space n → ℝ, IsHolderOn α f (closedBall z r) →
          ∀ (g : C(sphere z r, ℝ)) (u : Space n → ℝ),
            IsBallSolution a b c f z r g u →
            IsC2HolderLocOn α u (ballDomain z r) →
            ∀ (U : Domain n) (G : Space n → ℝ),
              IsC2HolderLocUpToOn α G (ballDomain z r) U →
              (∀ ζ : sphere z r, (ζ : Space n) ∈ (U : Set (Space n)) → g ζ = G ζ) →
              ∀ V : Domain n, Bornology.IsBounded (V : Set (Space n)) →
                closure (V : Set (Space n)) ⊆ (U : Set (Space n)) →
                IsC2HolderUpToOn α u (closedBall z r ∩ (V : Set (Space n)))

end P201Specs.Elliptic.BallSchauderSolvability
