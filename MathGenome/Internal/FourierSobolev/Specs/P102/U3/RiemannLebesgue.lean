import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation

/-! Independent proposition types for Proposition 3.1 and its dimension-zero convention.
`cocompact` expresses escape to infinity in a finite-dimensional Euclidean space;
`cofinite` on the integers expresses |n| → ∞ (both signs).
The real inner-product-space volume is the orthonormally normalized Lebesgue measure. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform Topology RealInnerProductSpace

namespace P102.U3.RiemannLebesgue.Expected

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Explicit check of the native Fourier sign and scale. -/
def formula : Prop := ∀ (f : V → ℂ) (ξ : V),
  𝓕 f ξ = ∫ x, Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x ξ : ℂ))) * f x

/-- No positive-dimensional assumption on continuity or the L¹ bound. -/
def euclidean : Prop := ∀ (f : V → ℂ), Integrable f →
  Continuous (𝓕 f) ∧ (∀ ξ, ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖) ∧
    (0 < Module.finrank ℝ V → Tendsto (𝓕 f) (cocompact V) (𝓝 0))

/-- The same result for genuine L¹ classes, with their L¹ norm. -/
def euclideanL1 : Prop := ∀ (f : Lp (α := V) ℂ 1),
  Continuous (𝓕 (f : V → ℂ)) ∧ (∀ ξ, ‖𝓕 (f : V → ℂ) ξ‖ ≤ ‖f‖) ∧
    (0 < Module.finrank ℝ V → Tendsto (𝓕 (f : V → ℂ)) (cocompact V) (𝓝 0))

/-- Standard volume has mass one in dimension zero and the transform is the identity. -/
def zeroDimension : Prop := Module.finrank ℝ V = 0 →
  (volume (Set.univ : Set V) = 1 ∧ ∀ (f : V → ℂ), 𝓕 f = f)

-- Each binding below includes all ambient-space hypotheses, not an assumed result.
def formulaStatement : Prop := ∀ (V : Type*) [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V], formula V

def euclideanStatement : Prop := ∀ (V : Type*) [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V], euclidean V

def euclideanL1Statement : Prop := ∀ (V : Type*) [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V], euclideanL1 V

def zeroDimensionStatement : Prop := ∀ (V : Type*) [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V], zeroDimension V

/-- Periodic L¹ representatives; uses the shared, independently specified coefficient. -/
def periodicStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (f : Periodic.Expected.Circle T → ℂ), Integrable f (Periodic.Expected.haar T) →
    Tendsto (Periodic.Expected.coefficient T f) cofinite (𝓝 0)

def periodicL1Statement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (f : Periodic.Expected.L1 T),
    Tendsto (Periodic.Expected.coefficientL1 T f) cofinite (𝓝 0)

end P102.U3.RiemannLebesgue.Expected
