import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.MeanValueStrongPrinciple
import Mathlib.Topology.MetricSpace.Bounded

/-! The boundary assertions in paper.tex:2550–2555. The epsilon-delta
conditions below express the upper/lower extended-real limits, including
infinite limits. They impose no values or continuity on the boundary. -/
noncomputable section
open Set Metric

namespace D12Complex

/-- `limsup` through `U` is at most `M` at every boundary point. -/
def BoundaryLimsupLE (U : Set ℂ) (u : ℂ → ℝ) (M : ℝ) : Prop :=
  ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ z ∈ U, dist z ξ < δ → u z ≤ M + ε

/-- `liminf` through `U` is at least `m` at every boundary point. -/
def BoundaryLiminfGE (U : Set ℂ) (u : ℂ → ℝ) (m : ℝ) : Prop :=
  ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ z ∈ U, dist z ξ < δ → m - ε ≤ u z

end D12Complex

namespace Specs.D12Complex.Ch13.BoundaryMaximum
open _root_.D12Complex

def BoundaryLimsupLE_type := Set ℂ → (ℂ → ℝ) → ℝ → Prop
def BoundaryLimsupLE_value : BoundaryLimsupLE_type :=
  fun U u M => ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ z ∈ U, dist z ξ < δ → u z ≤ M + ε

def BoundaryLiminfGE_type := Set ℂ → (ℂ → ℝ) → ℝ → Prop
def BoundaryLiminfGE_value : BoundaryLiminfGE_type :=
  fun U u m => ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ z ∈ U, dist z ξ < δ → m - ε ≤ u z

def continuous_mean_boundary_maximum_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ) (M : ℝ), IsOpen U → Bornology.IsBounded U →
    ContinuousOn u U → LocalCircleMeanProperty U u → BoundaryLimsupLE U u M →
    ∀ z ∈ U, u z ≤ M

def continuous_mean_boundary_minimum_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ) (m : ℝ), IsOpen U → Bornology.IsBounded U →
    ContinuousOn u U → LocalCircleMeanProperty U u → BoundaryLiminfGE U u m →
    ∀ z ∈ U, m ≤ u z

def harmonic_boundary_maximum_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ) (M : ℝ), Bornology.IsBounded U → HarmonicOn U u →
    BoundaryLimsupLE U u M → ∀ z ∈ U, u z ≤ M

def harmonic_boundary_minimum_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ) (m : ℝ), Bornology.IsBounded U → HarmonicOn U u →
    BoundaryLiminfGE U u m → ∀ z ∈ U, m ≤ u z

end Specs.D12Complex.Ch13.BoundaryMaximum
