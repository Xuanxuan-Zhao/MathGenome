import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.ConstantSchauder

/-! Weighted interpolation for the spherical-distance weight, including the
flat face of a half-ball. All jets below are the canonical within jets. -/
noncomputable section
open Set Metric
open scoped ContDiff

namespace P201Specs.Elliptic.WeightedInterpolation
open ConstantSchauder PoissonSchauder NewtonHessian

/-- Distance to the curved sphere, not to the flat face. -/
def radialWeight {n : ℕ} (a : Space n) (R : ℝ) (x : Space n) : ℝ := R - dist x a

def weightedValueSet {n : ℕ} (j : ℕ) (a : Space n) (R : ℝ)
    (g : Space n → ℝ) (s : Set (Space n)) : Set ℝ :=
  {q | ∃ x ∈ s, q = radialWeight a R x ^ j * ‖g x‖}

def weightedPairSet {n : ℕ} (j : ℕ) (α : ℝ) (a : Space n) (R : ℝ)
    (g : Space n → ℝ) (s : Set (Space n)) : Set ℝ :=
  {q | ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ q =
    min (radialWeight a R x) (radialWeight a R y) ^ ((j : ℝ) + α) *
      ‖g x - g y‖ / dist x y ^ α}

def weightedSupOn {n : ℕ} (j : ℕ) (a : Space n) (R : ℝ)
    (g : Space n → ℝ) (s : Set (Space n)) : ℝ :=
  sSup (weightedValueSet j a R g s)

def weightedSeminormOn {n : ℕ} (j : ℕ) (α : ℝ) (a : Space n) (R : ℝ)
    (g : Space n → ℝ) (s : Set (Space n)) : ℝ :=
  sSup (weightedPairSet j α a R g s)

def M0 {n : ℕ} (u : Space n → ℝ) (s : Set (Space n)) : ℝ := supNormOn u s

def M1 {n : ℕ} (a : Space n) (R : ℝ) (u : Space n → ℝ) (s : Set (Space n)) : ℝ :=
  ∑ i, weightedSupOn 1 a R (firstPartialWithin u s i) s

def M2 {n : ℕ} (a : Space n) (R : ℝ) (u : Space n → ℝ) (s : Set (Space n)) : ℝ :=
  ∑ i, ∑ j, weightedSupOn 2 a R (secondPartialWithin u s i j) s

def N0 {n : ℕ} (α : ℝ) (a : Space n) (R : ℝ)
    (u : Space n → ℝ) (s : Set (Space n)) : ℝ := weightedSeminormOn 0 α a R u s

def N1 {n : ℕ} (α : ℝ) (a : Space n) (R : ℝ)
    (u : Space n → ℝ) (s : Set (Space n)) : ℝ :=
  ∑ i, weightedSeminormOn 1 α a R (firstPartialWithin u s i) s

def N2 {n : ℕ} (α : ℝ) (a : Space n) (R : ℝ)
    (u : Space n → ℝ) (s : Set (Space n)) : ℝ :=
  ∑ i, ∑ j, weightedSeminormOn 2 α a R (secondPartialWithin u s i j) s

/-- Finiteness is stated for the actual defining sets, before using real suprema.
The pair sets may be empty. -/
def FiniteWeightedNorms {n : ℕ} (α : ℝ) (a : Space n) (R : ℝ)
    (u : Space n → ℝ) (s : Set (Space n)) : Prop :=
  BddAbove (weightedValueSet 0 a R u s) ∧
  (∀ i, BddAbove (weightedValueSet 1 a R (firstPartialWithin u s i) s)) ∧
  (∀ i j, BddAbove (weightedValueSet 2 a R (secondPartialWithin u s i j) s)) ∧
  BddAbove (weightedPairSet 0 α a R u s) ∧
  (∀ i, BddAbove (weightedPairSet 1 α a R (firstPartialWithin u s i) s)) ∧
  ∀ i j, BddAbove (weightedPairSet 2 α a R (secondPartialWithin u s i j) s)

def InterpolationBound {n : ℕ} (α ε C : ℝ) (a : Space n) (R : ℝ)
    (u : Space n → ℝ) (s : Set (Space n)) : Prop :=
  M1 a R u s + M2 a R u s + N0 α a R u s + N1 α a R u s ≤
    ε * N2 α a R u s + C * M0 u s

/-- A stronger finiteness assertion for arbitrary convex subsets with unique
within derivatives. No PDE or boundary value assumption occurs. -/
def BoundednessStatement : Prop :=
  ∀ {n : ℕ} {α R : ℝ} {a : Space n} {s : Set (Space n)} {u : Space n → ℝ},
    0 ≤ α → α ≤ 1 → 0 < R → Convex ℝ s → UniqueDiffOn ℝ s →
    s ⊆ ball a R → IsC2HolderUpToOn α u s → FiniteWeightedNorms α a R u s

def BallInterpolationStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space n) (R : ℝ), 0 < R → ∀ u : Space n → ℝ,
        IsC2HolderUpToOn α u (ball a R) →
        FiniteWeightedNorms α a R u (ball a R) ∧
        InterpolationBound α ε C a R u (ball a R)

def HalfBallInterpolationStatement : Prop :=
  ∀ m : ℕ, ∀ α : ℝ, 0 < α → α < 1 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ R : ℝ, 0 < R → ∀ u : Space (m + 1) → ℝ,
        IsC2HolderUpToOn α u (halfBallWithFace m R) →
        FiniteWeightedNorms α 0 R u (halfBallWithFace m R) ∧
        InterpolationBound α ε C 0 R u (halfBallWithFace m R)

/-- Local one-sided regularity does not require an extension below the plane. -/
def IsLocC2HolderWithinOn {n : ℕ} (α : ℝ) (u : Space n → ℝ)
    (s : Set (Space n)) : Prop :=
  ContDiffOn ℝ 2 u s ∧ ∀ x ∈ s, ∃ δ : ℝ, 0 < δ ∧
    IsC2HolderUpToOn α u (s ∩ ball x δ)

/-- Finite inner-radius norms under the local hypotheses of the application. -/
def RestrictionStatement : Prop :=
  (∀ {n : ℕ} {α R : ℝ} {a : Space n} {u : Space n → ℝ},
    0 < α → α < 1 → 0 < R →
    IsC2HolderLocOn α u ⟨ball a R, isOpen_ball⟩ →
    ∀ r : ℝ, 0 < r → r < R →
      IsC2HolderUpToOn α u (ball a r) ∧ FiniteWeightedNorms α a r u (ball a r)) ∧
  (∀ {m : ℕ} {α R : ℝ} {u : Space (m + 1) → ℝ},
    0 < α → α < 1 → 0 < R →
    IsLocC2HolderWithinOn α u (halfBallWithFace m R) →
    ∀ r : ℝ, 0 < r → r < R →
      IsC2HolderUpToOn α u (halfBallWithFace m r) ∧
      FiniteWeightedNorms α 0 r u (halfBallWithFace m r))

/-- The exhaustion conclusion is pointwise/all-pairs: it needs no finite outer
supremum and therefore can be used before proving finiteness of N₂. -/
def JetBounds {n : ℕ} (α : ℝ) (a : Space n) (R : ℝ) (s : Set (Space n))
    (u : Space n → ℝ) (A B H : ℝ) : Prop :=
  (∀ i, ∀ x ∈ s, radialWeight a R x * ‖firstPartialWithin u s i x‖ ≤ A) ∧
  (∀ i j, ∀ x ∈ s, radialWeight a R x ^ 2 * ‖secondPartialWithin u s i j x‖ ≤ B) ∧
  ∀ i j, ∀ x ∈ s, ∀ y ∈ s,
    min (radialWeight a R x) (radialWeight a R y) ^ (2 + α) *
      ‖secondPartialWithin u s i j x - secondPartialWithin u s i j y‖ ≤ H * dist x y ^ α

def ExhaustionStatement : Prop :=
  (∀ {n : ℕ} {α R A B H : ℝ} {a : Space n} {u : Space n → ℝ},
    0 < α → 0 < R →
    (∀ r : ℝ, R / 2 < r → r < R → JetBounds α a r (ball a r) u A B H) →
    JetBounds α a R (ball a R) u A B H) ∧
  (∀ {m : ℕ} {α R A B H : ℝ} {u : Space (m + 1) → ℝ},
    0 < α → 0 < R →
    (∀ r : ℝ, R / 2 < r → r < R →
      JetBounds α 0 r (halfBallWithFace m r) u A B H) →
    JetBounds α 0 R (halfBallWithFace m R) u A B H)

end P201Specs.Elliptic.WeightedInterpolation
