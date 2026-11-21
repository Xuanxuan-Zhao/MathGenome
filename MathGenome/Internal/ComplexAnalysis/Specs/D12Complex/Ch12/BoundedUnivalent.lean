import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.MetricSpace.Basic

/-! The bounded univalent class of paper.tex:2467–2473 (D12.12.02).
The square-root property is quantified over the actual weakly holomorphic
functions on Ω. No simple-connectivity assumption or analytic certificate
is included. Functions are represented by total extensions, with all mapping
and injectivity requirements restricted to Ω. -/

namespace Specs.D12Complex.Ch12.BoundedUnivalent
open _root_.D12Complex

/-- A proper plane domain with the universal square-root property admits a
normalized injective holomorphic map into the open unit disk. The derivative
is explicitly a strictly positive real complex number. -/
def bounded_univalent_type : Prop :=
  ∀ (Ω : Set ℂ), IsDomain Ω → Ω ≠ Set.univ →
    (∀ g : ℂ → ℂ, HolomorphicOn Ω g → (∀ z ∈ Ω, g z ≠ 0) →
      ∃ s : ℂ → ℂ, HolomorphicOn Ω s ∧ ∀ z ∈ Ω, (s z) ^ 2 = g z) →
    ∀ z₀ ∈ Ω, ∃ h : ℂ → ℂ,
      HolomorphicOn Ω h ∧ Set.InjOn h Ω ∧
      Set.MapsTo h Ω (Metric.ball 0 1) ∧ h z₀ = 0 ∧
      ∃ t : ℝ, 0 < t ∧ deriv h z₀ = (t : ℂ)

end Specs.D12Complex.Ch12.BoundedUnivalent
