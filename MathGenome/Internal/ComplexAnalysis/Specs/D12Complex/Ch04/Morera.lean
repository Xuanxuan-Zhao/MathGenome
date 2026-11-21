import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.TrianglePrimitiveCriterion

/-! Independent statements for the Morera and exceptional-point portions of
paper.tex:1196–1213, D12.04.08. The closed triangles in
`ZeroTriangleIntegrals` are finite real convex hulls, hence compact; containment
in the open set is precisely compact containment here. The integral is the
canonical sum of the three directed segment contour integrals.

No connectedness or nonemptiness is imposed on the open set. In the second
statement the exceptional point is arbitrary, including points outside Ω.
The rectifiable-arc assertion is allocated to the separate arc-gluing goal. -/

namespace Specs.D12Complex.Ch04.Morera
open Set
open _root_.D12Complex

/-- Continuity and vanishing triangle integrals imply weak holomorphy. -/
def morera_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsOpen Ω → ContinuousOn f Ω →
    ZeroTriangleIntegrals Ω f → HolomorphicOn Ω f

/-- Continuity removes a single possible failure of holomorphy, with the
original function value at that point. -/
def continuous_point_gluing_type : Prop :=
  ∀ (Ω : Set ℂ) (p : ℂ) (f : ℂ → ℂ), IsOpen Ω → ContinuousOn f Ω →
    HolomorphicOn (Ω \ {p}) f → HolomorphicOn Ω f

end Specs.D12Complex.Ch04.Morera
