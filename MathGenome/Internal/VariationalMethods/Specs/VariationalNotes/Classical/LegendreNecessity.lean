import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.SecondVariation

noncomputable section
open Set
open scoped ContDiff

namespace Specs.VariationalNotes.Classical.LegendreNecessity
open _root_.VariationalNotes.Classical

/-- Pointwise Legendre condition, including every vector and every interior time. -/
def classicalLegendreNecessity : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (xₐ xᵦ : State m)
    (u : C1Curve I m),
    weakLocalMinimum L xₐ xᵦ u → regularNearGraph L u 2 →
    ∀ (t : I.Points), (t : ℝ) ∈ Ioo I.a I.b → ∀ e : State m,
      0 ≤ secondVariationVV L (graphPoint u t) e e

/-- The complete one-dimensional necessity theorem: exact second derivative,
nonnegative displayed second variation, and pointwise positive semidefiniteness. -/
def classicalLegendreTheorem : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (xₐ xᵦ : State m)
    (u : C1Curve I m),
    weakLocalMinimum L xₐ xᵦ u → regularNearGraph L u 2 →
    (∀ η : C1Curve I m, η ∈ endpointZero I m →
      HasDerivAt (deriv (fun s : ℝ => action L (u + s • η)))
        (secondVariationForm L u η) 0 ∧ 0 ≤ secondVariationForm L u η) ∧
    (∀ (t : I.Points), (t : ℝ) ∈ Ioo I.a I.b → ∀ e : State m,
      0 ≤ secondVariationVV L (graphPoint u t) e e)

end Specs.VariationalNotes.Classical.LegendreNecessity
