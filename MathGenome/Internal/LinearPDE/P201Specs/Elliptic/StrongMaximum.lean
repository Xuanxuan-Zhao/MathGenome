import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Connected.Basic

/-! Independent statements for the strong part of `pde:elliptic-max`.
The coefficients are continuous only on the open domain. No boundary regularity,
coefficient bounds on the whole domain, or solvability certificate is included.
-/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace P201Specs.Elliptic

/-- Coordinate first derivative in the shared Euclidean coordinates. -/
def firstPartial {n : ℕ} (u : Space n → ℝ) (i : Fin n) (x : Space n) : ℝ :=
  fderiv ℝ u x (coordinate n i)

/-- The actual iterated classical coordinate derivative ∂ᵢ∂ⱼu. -/
def secondPartial {n : ℕ} (u : Space n → ℝ) (i j : Fin n) (x : Space n) : ℝ :=
  firstPartial (firstPartial u j) i x

/-- The positive-principal-part NONdivergence operator from the source. -/
def nondivergenceOperator {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ)
    (u : Space n → ℝ) (x : Space n) : ℝ :=
  (∑ i, ∑ j, a x i j * secondPartial u i j x) +
    (∑ i, b x i * firstPartial u i x) + c x * u x

/-- Symmetry, interior continuity, and the source's uniform lower ellipticity
bound. There is no global upper bound on the coefficients. -/
def EllipticCoefficients {n : ℕ} (Ω : Domain n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ) : Prop :=
  ContinuousOn a (Ω : Set (Space n)) ∧
  ContinuousOn b (Ω : Set (Space n)) ∧
  ContinuousOn c (Ω : Set (Space n)) ∧
  (∀ x ∈ (Ω : Set (Space n)), ∀ i j, a x i j = a x j i) ∧
  ∃ ell : ℝ, 0 < ell ∧ ∀ x ∈ (Ω : Set (Space n)), ∀ ξ : Space n,
    ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j

/-- Nonnegative attained global maximum, with c ≤ 0. -/
def strongMaximumStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Domain n),
  Bornology.IsBounded (Ω : Set (Space n)) → IsConnected (Ω : Set (Space n)) →
  ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u : Space n → ℝ),
  EllipticCoefficients Ω a b c →
  (∀ x ∈ (Ω : Set (Space n)), c x ≤ 0) →
  ContDiffOn ℝ 2 u (Ω : Set (Space n)) →
  ContinuousOn u (closure (Ω : Set (Space n))) →
  (∀ x ∈ (Ω : Set (Space n)), 0 ≤ nondivergenceOperator a b c u x) →
  ∀ x₀ ∈ (Ω : Set (Space n)), 0 ≤ u x₀ →
  (∀ x ∈ (Ω : Set (Space n)), u x ≤ u x₀) →
  ∀ x ∈ (Ω : Set (Space n)), u x = u x₀

/-- For c = 0 the attained maximum may have either sign. -/
def strongMaximumZeroOrderFreeStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Domain n),
  Bornology.IsBounded (Ω : Set (Space n)) → IsConnected (Ω : Set (Space n)) →
  ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u : Space n → ℝ),
  EllipticCoefficients Ω a b c →
  (∀ x ∈ (Ω : Set (Space n)), c x = 0) →
  ContDiffOn ℝ 2 u (Ω : Set (Space n)) →
  ContinuousOn u (closure (Ω : Set (Space n))) →
  (∀ x ∈ (Ω : Set (Space n)), 0 ≤ nondivergenceOperator a b c u x) →
  ∀ x₀ ∈ (Ω : Set (Space n)),
  (∀ x ∈ (Ω : Set (Space n)), u x ≤ u x₀) →
  ∀ x ∈ (Ω : Set (Space n)), u x = u x₀

end P201Specs.Elliptic
