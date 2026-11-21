import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.DiskCauchyDerivatives
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Divided differences for weakly holomorphic functions, paper.tex:1089–1124.
The domain is an arbitrary open set; no regularity of f' is assumed.
All derivatives below are actual complex derivatives, and uniform convergence
also ranges over base points in a fixed neighborhood of the selected point. -/
noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex.DividedDifferenceRegularity

def dividedDifference (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  if z = w then deriv f z else (f w - f z) / (w - z)

def partialZ (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  deriv (fun t => dividedDifference f t w) z

end D12Complex.DividedDifferenceRegularity

namespace Specs.D12Complex.Ch04.DividedDifferenceRegularity
open _root_.D12Complex
open _root_.D12Complex.DividedDifferenceRegularity

def dividedDifference_type := (ℂ → ℂ) → ℂ → ℂ → ℂ
def dividedDifference_value : dividedDifference_type :=
  fun f z w => if z = w then deriv f z else (f w - f z) / (w - z)
def partialZ_type := (ℂ → ℂ) → ℂ → ℂ → ℂ
def partialZ_value : partialZ_type :=
  fun f z w => deriv (fun t => dividedDifference f t w) z

def continuousOn_dividedDifference_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f →
    ContinuousOn (fun p : ℂ × ℂ => dividedDifference f p.1 p.2) (U ×ˢ U)

def holomorphicOn_slice_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f →
    ∀ w ∈ U, HolomorphicOn U (fun z => dividedDifference f z w)

def hasDerivAt_slice_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f →
    ∀ z ∈ U, ∀ w ∈ U,
      HasDerivAt (fun t => dividedDifference f t w) (partialZ f z w) z

def continuousOn_partialZ_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f →
    ContinuousOn (fun p : ℂ × ℂ => partialZ f p.1 p.2) (U ×ˢ U)

/-- A single common local circle gives the formula, including the diagonal. -/
def common_circle_formula_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f →
    ∀ (a : ℂ) (r : ℝ), 0 < r → closedBall a r ⊆ U →
      ∀ z ∈ ball a r, ∀ w ∈ ball a r,
        dividedDifference f z w = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (Specs.D12Complex.Ch04.DiskCauchyFormula.circlePath_value a r).integral
            (fun ζ => f ζ / ((ζ - z) * (ζ - w)))

/-- Such a circle can be chosen about every point of U. -/
def local_common_circle_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f →
    ∀ a ∈ U, ∃ r > 0, closedBall a r ⊆ U ∧
      ∀ z ∈ ball a r, ∀ w ∈ ball a r,
        dividedDifference f z w = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (Specs.D12Complex.Ch04.DiskCauchyFormula.circlePath_value a r).integral
            (fun ζ => f ζ / ((ζ - z) * (ζ - w)))

/-- Uniform in w on every fixed compact subset, and in z on a neighborhood
of any prescribed base point. The increment tends to zero puncturedly. -/
def uniform_differenceQuotients_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f →
    ∀ z₀ ∈ U, ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ r > 0, closedBall z₀ r ⊆ U ∧
        TendstoUniformlyOn
          (fun h : ℂ => fun p : ℂ × ℂ =>
            (dividedDifference f (p.1 + h) p.2 - dividedDifference f p.1 p.2) / h)
          (fun p => partialZ f p.1 p.2) (𝓝[≠] 0) (closedBall z₀ r ×ˢ K)

end Specs.D12Complex.Ch04.DividedDifferenceRegularity
