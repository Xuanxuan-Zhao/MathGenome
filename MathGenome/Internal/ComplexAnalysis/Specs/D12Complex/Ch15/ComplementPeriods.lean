import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.PolygonRepresentation
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SphereTopology

/-! Independent statements for the complement/period implications in
paper.tex:2757–2765 (D12.15.07). All paths, integrals, cycles, indices,
holomorphy, and sphere objects are the shared canonical objects.
No simple-connectivity or Jordan separation assumption is made. -/

noncomputable section
open Set

namespace Specs.D12Complex.Ch15.ComplementPeriods
open _root_.D12Complex _root_.D12Complex.PolygonRepresentation

/-- A disconnected spherical complement produces a genuine finite polygonal
cycle in the open set, with index one about a finite complementary point. -/
def disconnected_complement_cycle_type : Prop :=
  ∀ Ω : Set ℂ, IsOpen Ω → ¬ IsConnected (sphereFinite '' Ω)ᶜ →
    ∃ (a : ℂ) (Γ : IntegralCycle), a ∉ Ω ∧ IsPolygonalCycle Γ ∧
      Γ.trace ⊆ Ω ∧ a ∉ Γ.trace ∧ Γ.index a = 1 ∧
      Γ.integral (fun z => 1 / (z - a)) = 2 * (Real.pi : ℂ) * Complex.I

/-- The source's full equivalence for a plane domain: every holomorphic
function and every closed piecewise C1 path in that domain are quantified. -/
def connected_complement_iff_zero_periods_type : Prop :=
  ∀ Ω : Set ℂ, IsDomain Ω →
    (IsConnected (sphereFinite '' Ω)ᶜ ↔
      ∀ f : ℂ → ℂ, HolomorphicOn Ω f →
        ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.IsClosed → γ.integral f = 0)

end Specs.D12Complex.Ch15.ComplementPeriods
