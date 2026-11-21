import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.LocalExtr

/-! Independent statements of paper.tex, Theorem `thm:v03-03-02`.
Finite-dimensional real inner product spaces include Euclidean ℝ^d for
all natural dimensions, including zero. Strong convexity is expressed
exactly by convexity after subtracting the stated quadratic. -/
noncomputable section
open Set
universe u
namespace VariationalNotes.Existence.Specs

/-- The quadratic supporting inequality underlying both estimates. -/
def strongConvexity_support : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → ℝ) (μ : ℝ), 0 < μ →
    Differentiable ℝ J →
    ConvexOn ℝ univ (fun z => J z - μ * ‖z‖ ^ 2 / 2) →
    ∀ x y : E,
      J x + inner ℝ (gradient J x) (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ J y

/-- Both exact strong-convexity bounds, with a given global minimizer. -/
def strongConvexity_bounds : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → ℝ) (μ : ℝ), 0 < μ →
    Differentiable ℝ J →
    ConvexOn ℝ univ (fun z => J z - μ * ‖z‖ ^ 2 / 2) →
    ∀ xstar : E, (∀ y : E, J xstar ≤ J y) → ∀ x : E,
      μ / 2 * ‖x - xstar‖ ^ 2 ≤ J x - J xstar ∧
      J x - J xstar ≤ ‖gradient J x‖ ^ 2 / (2 * μ)

end VariationalNotes.Existence.Specs
