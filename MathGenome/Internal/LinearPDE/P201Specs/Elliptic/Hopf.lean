import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.MaximumComparison
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Independent statements for `paper.tex:1423–1444`. The local hypotheses
refer only to the interior tangent ball near its contact point. No derivative
of the solution at the boundary is assumed. Extended-real liminf permits an
infinite positive slope (for example a square-root boundary profile). -/
noncomputable section
open Set TopologicalSpace Metric Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace P201Specs.Elliptic

/-- Outward radial UNIT vector at the contact point of a radius-R ball. -/
def outwardRadial {n : ℕ} (y z : Space n) (R : ℝ) : Space n := R⁻¹ • (z-y)

def boundaryQuotient {n : ℕ} (u : Space n → ℝ) (z ν : Space n) (h : ℝ) : ℝ :=
  (u z - u (z-h • ν)) / h

def boundaryLowerSlope {n : ℕ} (u : Space n → ℝ) (z ν : Space n) : EReal :=
  liminf (fun h : ℝ => (boundaryQuotient u z ν h : EReal)) (𝓝[>] 0)

/-- Continuity of all coefficients in Ω; symmetry, ellipticity, and upper
bounds are only needed in the part of the tangent ball near z. -/
def LocalHopfCoefficients {n : ℕ} (Ω : Domain n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ) (y z : Space n) (R : ℝ) : Prop :=
  ContinuousOn a (Ω : Set _) ∧ ContinuousOn b (Ω : Set _) ∧
  ContinuousOn c (Ω : Set _) ∧
  ∃ δ C ell : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 < ell ∧
    ∀ x ∈ ball y R ∩ ball z δ,
      (∀ i j, a x i j = a x j i) ∧
      (∀ ξ : Space n, ell * ‖ξ‖^2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j) ∧
      (∀ i j, |a x i j| ≤ C) ∧ (∀ i, |b x i| ≤ C) ∧ |c x| ≤ C

/-- Exact geometric and classical analytic data, without a sign restriction
on the boundary value. The ambient open set need not have a smooth boundary. -/
structure HopfHypotheses {n : ℕ} (Ω : Domain n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u : Space n → ℝ)
    (y z : Space n) (R : ℝ) : Prop where
  radius_pos : 0 < R
  ball_subset : ball y R ⊆ (Ω : Set _)
  contact_boundary : z ∈ frontier (Ω : Set _)
  contact_sphere : z ∈ sphere y R
  coefficients : LocalHopfCoefficients Ω a b c y z R
  nonpositive : ∀ x ∈ (Ω : Set _), c x ≤ 0
  smooth : ContDiffOn ℝ 2 u (Ω : Set _)
  continuous : ContinuousOn u (closure (Ω : Set _))
  subsolution : ∀ x ∈ (Ω : Set _), 0 ≤ nondivergenceOperator a b c u x
  strict : ∀ x ∈ ball y R, u x < u z

/-- Positive lower slope and the consequence for every existing finite
one-sided outward directional derivative. -/
def HopfConclusion {n : ℕ} (u : Space n → ℝ) (z ν : Space n) : Prop :=
  0 < boundaryLowerSlope u z ν ∧
  ∀ d : ℝ, Tendsto (boundaryQuotient u z ν) (𝓝[>] 0) (𝓝 d) → 0 < d

def hopfStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Domain n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u : Space n → ℝ) (y z : Space n) (R : ℝ),
    HopfHypotheses Ω a b c u y z R → 0 ≤ u z →
    HopfConclusion u z (outwardRadial y z R)

def hopfZeroOrderFreeStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Domain n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u : Space n → ℝ) (y z : Space n) (R : ℝ),
    HopfHypotheses Ω a b c u y z R → (∀ x ∈ (Ω : Set _), c x = 0) →
    HopfConclusion u z (outwardRadial y z R)

/-- A normalized differentiable local defining function is negative on the
interior side and has derivative inner product with the outward unit normal.
This is a pointwise boundary hypothesis, with no global C¹ assumption. -/
def IsDifferentiableBoundaryNormal {n : ℕ} (Ω : Domain n) (z N : Space n) : Prop :=
  ‖N‖ = 1 ∧ ∃ ρ : Space n → ℝ, ρ z = 0 ∧ HasFDerivAt ρ (innerSL ℝ N) z ∧
    ∃ V : Set (Space n), V ∈ 𝓝 z ∧
      ∀ x ∈ V, (x ∈ (Ω : Set _) ↔ ρ x < 0)

def tangentBallNormalStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Domain n) (y z N : Space n) (R : ℝ),
    0 < R → ball y R ⊆ (Ω : Set _) → z ∈ sphere y R →
    IsDifferentiableBoundaryNormal Ω z N → outwardRadial y z R = N

end P201Specs.Elliptic
