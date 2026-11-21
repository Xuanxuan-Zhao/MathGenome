import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.PoissonSchauder
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.HalfSpaceLift
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.StrongMaximum

/-! Independent statements for `pde:elliptic-flat-schauder`, paper.tex:1912–2010.
The half-ball contains its flat face but excludes its curved boundary. Derivatives
there are derivatives within this set; no regularity of an arbitrary ambient
representative below the plane is required. All seminorms use all pairs.
The constant is uniform over matrices with the displayed ellipticity bounds.
-/
noncomputable section
open Set Metric
open scoped ContDiff

namespace P201Specs.Elliptic.ConstantSchauder
open PoissonSchauder NewtonHessian HalfSpaceLift

/-- An open upper half-ball in dimension `m + 1`, including dimension one. -/
def halfBall (m : ℕ) (r : ℝ) : Set (Space (m + 1)) :=
  ball 0 r ∩ openHalfSpace m

/-- Only the flat face is added; points on the curved sphere are excluded. -/
def halfBallWithFace (m : ℕ) (r : ℝ) : Set (Space (m + 1)) :=
  ball 0 r ∩ closedHalfSpace m

def flatFace (m : ℕ) (r : ℝ) : Set (Space (m + 1)) :=
  {p | p ∈ ball 0 r ∧ height p = 0}

/-- Actual one-sided first coordinate derivatives. -/
def firstPartialWithin {n : ℕ} (u : Space n → ℝ) (s : Set (Space n))
    (i : Fin n) (x : Space n) : ℝ :=
  fderivWithin ℝ u s x (coordinate n i)

/-- Actual one-sided second coordinate derivatives. -/
def secondPartialWithin {n : ℕ} (u : Space n → ℝ) (s : Set (Space n))
    (i j : Fin n) (x : Space n) : ℝ :=
  fderivWithin ℝ (firstPartialWithin u s j) s x (coordinate n i)

/-- Finiteness and classical C²,α regularity up to the flat face. On this
convex set with nonempty interior the within derivatives are unique, and agree
with the ordinary classical derivatives at every interior point. -/
def IsC2HolderUpToOn {n : ℕ} (α : ℝ) (u : Space n → ℝ)
    (s : Set (Space n)) : Prop :=
  ContDiffOn ℝ 2 u s ∧ IsBoundedOn u s ∧
    (∀ i : Fin n, IsBoundedOn (firstPartialWithin u s i) s) ∧
    ∀ i j : Fin n, IsHolderOn α (secondPartialWithin u s i j) s

/-- The same coordinate-sum norm choice as the interior Poisson specification,
using the genuine one-sided jets when the flat face is present. -/
def scaledWithinSolutionNorm {n : ℕ} (α r : ℝ) (u : Space n → ℝ)
    (s : Set (Space n)) : ℝ :=
  supNormOn u s + r * (∑ i : Fin n, supNormOn (firstPartialWithin u s i) s) +
    r ^ 2 * (∑ i : Fin n, ∑ j : Fin n, supNormOn (secondPartialWithin u s i j) s) +
    r ^ (2 + α) * (∑ i : Fin n, ∑ j : Fin n,
      PoissonSchauder.holderSeminormOn α (secondPartialWithin u s i j) s)

/-- Constant principal operator in the shared classical coordinate derivatives. -/
def constantOperator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, A i j * secondPartial u i j x

/-- Lower and upper quadratic-form bounds on the actual symmetric matrix.
The positive parameters are quantified separately in the estimate statements. -/
def MatrixBounds {n : ℕ} (ell upper : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, A i j = A j i) ∧ ∀ ξ : Space n,
    ell * ‖ξ‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, A i j * ξ i * ξ j ∧
    (∑ i : Fin n, ∑ j : Fin n, A i j * ξ i * ξ j) ≤ upper * ‖ξ‖ ^ 2

/-- Half-ball Schauder regularity and the complete scaled estimate. The source
may take arbitrary values on the plane; only u has zero trace. No derivatives
of u at the plane are hypotheses. `m = 0` is the one-dimensional case. -/
def HalfBallEstimateStatement : Prop :=
  ∀ m : ℕ, ∀ α : ℝ, 0 < α → α < 1 →
    ∀ ell upper : ℝ, 0 < ell → 0 < upper →
      ∃ C : ℝ, 0 < C ∧ ∀ A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
        MatrixBounds ell upper A → ∀ r : ℝ, 0 < r →
          ∀ u f : Space (m + 1) → ℝ,
            ContDiffOn ℝ 2 u (halfBall m (2 * r)) →
            ContinuousOn u (halfBallWithFace m (2 * r)) →
            (∀ x ∈ flatFace m (2 * r), u x = 0) →
            IsBoundedOn u (halfBallWithFace m (2 * r)) →
            IsHolderOn α f (halfBallWithFace m (2 * r)) →
            (∀ x ∈ halfBall m (2 * r), constantOperator A u x = f x) →
            IsC2HolderUpToOn α u (halfBallWithFace m r) ∧
            scaledWithinSolutionNorm α r u (halfBallWithFace m r) ≤
              C * scaledDataNorm α r u f (halfBallWithFace m (2 * r))

/-- Interior balls for every constant symmetric positive matrix, with a
constant depending only on dimension, exponent, and the two matrix bounds. -/
def InteriorBallEstimateStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ ell upper : ℝ, 0 < ell → 0 < upper →
      ∃ C : ℝ, 0 < C ∧ ∀ A : Matrix (Fin n) (Fin n) ℝ,
        MatrixBounds ell upper A → ∀ (a : Space n) (r : ℝ), 0 < r →
          ∀ u f : Space n → ℝ, ContDiffOn ℝ 2 u (ball a (2 * r)) →
            IsBoundedOn u (ball a (2 * r)) → IsHolderOn α f (ball a (2 * r)) →
            (∀ x ∈ ball a (2 * r), constantOperator A u x = f x) →
            IsC2HolderOn α u (ball a r) ∧
            scaledSolutionNorm α r u (ball a r) ≤
              C * scaledDataNorm α r u f (ball a (2 * r))

end P201Specs.Elliptic.ConstantSchauder
