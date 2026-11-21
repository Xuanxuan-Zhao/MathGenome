import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.MapsMultiplicity

/-! Independent statement of paper.tex:3448–3457 (D12.20.06).
The codomain is the scalar field ℂ; holomorphic sphere-valued maps are
not subject to this conclusion. Connectedness and nonemptiness are part
of the canonical `RiemannSurface` structure. -/

namespace Specs.D12Complex.Ch20.CompactMaximum

open _root_.D12Complex.Surfaces
universe u

/-- Every scalar holomorphic function on a compact Riemann surface is constant. -/
def scalarHolomorphic_constant_of_compact_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (S : RiemannSurface X) (f : X → ℂ),
    ScalarHolomorphic S f → ∃ c : ℂ, ∀ x : X, f x = c

end Specs.D12Complex.Ch20.CompactMaximum
