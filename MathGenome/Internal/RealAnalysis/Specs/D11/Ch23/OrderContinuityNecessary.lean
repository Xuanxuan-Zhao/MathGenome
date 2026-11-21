import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.ElementaryIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-!
Independent statement of paper.tex:6296–6303,
`d11:23:order-continuity-necessary`.

The input `L` is an arbitrary map. Its representing integral is evaluated
only after actual measurability and finite absolute integral are supplied
on the specified measurable space. The conclusion bundles this same map as
a real-linear map and asserts the shared elementary-integral predicate,
which includes positivity and continuity for everywhere decreasing sequences
with everywhere limit zero. No unit, mass, or nonemptiness condition is added.
-/

universe u

namespace Specs.D11.Ch23.OrderContinuityNecessary

open MeasureTheory
open Specs.D11.Ch06.ScalarIntegral

/-- Every integral representation on all of the original lattice forces
linearity, positivity, and pointwise order continuity of the original map. -/
def order_continuity_necessary : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (V : Submodule ℝ (X → ℝ)),
    D11.Ch23.Specs.IsVectorLattice V →
    ∀ (μ : Measure X) (L : V → ℝ)
      (hint : ∀ f : V, scalarIntegrable_value μ (f : X → ℝ)),
      (∀ f : V, L f = scalarIntegral_value μ (f : X → ℝ) (hint f)) →
      ∃ A : V →ₗ[ℝ] ℝ,
        (∀ f : V, A f = L f) ∧ D11.Ch23.Specs.IsElementaryIntegral V A

end Specs.D11.Ch23.OrderContinuityNecessary
