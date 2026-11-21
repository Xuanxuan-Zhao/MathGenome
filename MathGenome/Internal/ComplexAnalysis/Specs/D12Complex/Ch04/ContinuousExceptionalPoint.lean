import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.WeakGoursat

/-! Independent statement of paper.tex:859–873, `d12:04:exceptional-point`.
The triangle and its boundary integral reuse the preceding Goursat interface.
All vertices and the exceptional point are unrestricted; in particular the
triangle can be degenerate and the point can lie on its boundary or outside it.
-/

namespace Specs.D12Complex.Ch04.ContinuousExceptionalPoint

open Set
open _root_.D12Complex

def goursat_triangle_type : Prop :=
  ∀ (a b c p : ℂ) (U : Set ℂ) (f : ℂ → ℂ),
    IsOpen U → ContinuousOn f U → HolomorphicOn (U \ {p}) f →
    WeakGoursat.closedTriangle_value a b c ⊆ U →
    WeakGoursat.triangleBoundaryIntegral_value a b c f = 0

end Specs.D12Complex.Ch04.ContinuousExceptionalPoint
