import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Independent specification of chapters/04.tex, d04:04:constant-rank.
The rank is the dimension of the range of the shared total derivative.
Both coordinate maps are genuine local homeomorphisms with C^r inverses.
The maps-to condition makes the entire normal-form composition defined.
No dimension is required to be positive. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace Specs.D04.C04.ConstantRank
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

/-- The first k input coordinates, followed by zero output coordinates.
The second test only makes this definition total even for k > n; the theorem
proves k ≤ min n m, so it is redundant in every theorem application. -/
def normalProjection (n m k : ℕ) (u : E n) : E m :=
  WithLp.toLp 2 (fun j => if h : j.val < k ∧ j.val < n then u ⟨j.val, h.2⟩ else 0)

/-- Compatible source and target coordinate neighborhoods, centered at zero,
with all four C^r regularity statements and the full normal-form identity. -/
def RankNormalForm {n m : ℕ} (r : ℕ∞ω) (U : Set (E n))
    (f : E n → E m) (a : E n) (k : ℕ) : Prop :=
  ∃ Φ : OpenPartialHomeomorph (E n) (E n),
  ∃ Ψ : OpenPartialHomeomorph (E m) (E m),
    a ∈ Φ.source ∧ Φ.source ⊆ U ∧ Φ a = 0 ∧
    f a ∈ Ψ.source ∧ Ψ (f a) = 0 ∧
    ContDiffOn ℝ r Φ Φ.source ∧ ContDiffOn ℝ r Φ.symm Φ.target ∧
    ContDiffOn ℝ r Ψ Ψ.source ∧ ContDiffOn ℝ r Ψ.symm Ψ.target ∧
    MapsTo f Φ.source Ψ.source ∧
    ∀ u ∈ Φ.target, Ψ (f (Φ.symm u)) = normalProjection n m k u

/-- Rank is constant on some neighborhood, rather than merely at a. -/
def NeighborhoodRank {n m : ℕ} (f : E n → E m) (a : E n) (k : ℕ) : Prop :=
  ∀ᶠ x in 𝓝 a, Module.finrank ℝ (LinearMap.range (totalDerivative f x).toLinearMap) = k

def constant_rank_finiteType : Prop :=
  ∀ {n m : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → E m) (a : E n) (k : ℕ),
    1 ≤ r → IsOpen U → CrOn r U f → a ∈ U → NeighborhoodRank f a k →
    0 ≤ k ∧ k ≤ min n m ∧ RankNormalForm (r : ℕ∞ω) U f a k

def constant_rank_smoothType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a : E n) (k : ℕ),
    IsOpen U → SmoothOn U f → a ∈ U → NeighborhoodRank f a k →
    0 ≤ k ∧ k ≤ min n m ∧ RankNormalForm ∞ U f a k

/-- Separately checkable completed portions of the main obligation. -/
def constant_rank_boundsType : Prop :=
  ∀ {n m : ℕ} (f : E n → E m) (a : E n) (k : ℕ),
    NeighborhoodRank f a k → 0 ≤ k ∧ k ≤ min n m

def constant_rank_zero_finiteType : Prop :=
  ∀ {n m : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → E m) (a : E n),
    1 ≤ r → IsOpen U → CrOn r U f → a ∈ U → NeighborhoodRank f a 0 →
    RankNormalForm (r : ℕ∞ω) U f a 0

def constant_rank_zero_smoothType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a : E n),
    IsOpen U → SmoothOn U f → a ∈ U → NeighborhoodRank f a 0 →
    RankNormalForm ∞ U f a 0

def constant_rank_square_finiteType : Prop :=
  ∀ {n : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → E n) (a : E n),
    1 ≤ r → IsOpen U → CrOn r U f → a ∈ U → NeighborhoodRank f a n →
    RankNormalForm (r : ℕ∞ω) U f a n

def constant_rank_square_smoothType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → E n) (a : E n),
    IsOpen U → SmoothOn U f → a ∈ U → NeighborhoodRank f a n →
    RankNormalForm ∞ U f a n
end Specs.D04.C04.ConstantRank
