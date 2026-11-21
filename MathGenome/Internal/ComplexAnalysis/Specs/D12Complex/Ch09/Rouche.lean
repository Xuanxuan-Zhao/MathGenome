import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch09.ArgumentPrinciple

/-! Independent statements of Rouché's theorem, paper.tex:2287–2292.
`analyticOrderNatAt` is the ordinary local analytic multiplicity. The assertions
of finite local factorization below ensure that its zero-germ default is never
used at a point with nonzero index. Unrelated zero components are permitted.
The geometric region specialization records that the cycle covers the full
boundary, in addition to the supplied positive Green geometry.
-/
noncomputable section
open Set
open scoped BigOperators

namespace Specs.D12Complex.Ch09.Rouche
open _root_.D12Complex

/-- The common open set is an arbitrary neighborhood of the trace and of every
nonzero-index point. No global connectedness or nonzero-component assumption
is imposed on the two holomorphic functions. -/
def cycle_type : Prop :=
  ∀ (Ω : Set ℂ) (Γ : IntegralCycle) (f g : ℂ → ℂ),
    HolomorphicOn Ω f → HolomorphicOn Ω g → Γ.trace ⊆ Ω →
    (∀ a, Γ.index a ≠ 0 → a ∈ Ω) →
    (∀ z ∈ Γ.trace, ‖g z - f z‖ < ‖f z‖) →
    (∀ a, Γ.index a ≠ 0 →
      Ch05.LocalZeroFactorization.HasFiniteOrder_value f a (analyticOrderNatAt f a) ∧
      Ch05.LocalZeroFactorization.HasFiniteOrder_value g a (analyticOrderNatAt g a)) ∧
    (Function.support (fun a => Γ.index a * (analyticOrderNatAt f a : ℂ))).Finite ∧
    (Function.support (fun a => Γ.index a * (analyticOrderNatAt g a : ℂ))).Finite ∧
    (∑ᶠ a, Γ.index a * (analyticOrderNatAt f a : ℂ)) =
      ∑ᶠ a, Γ.index a * (analyticOrderNatAt g a : ℂ)

/-- Ordinary counts on the supplied full positive Green boundary. The finite
sets contain exactly the zeros in D, each counted with its analytic order. -/
def region_type : Prop :=
  ∀ (D Ω : Set ℂ) (Γ : IntegralCycle) (f g : ℂ → ℂ),
    GreenRegionIndex.SpecifiedGreenRegularRegion D Γ → frontier D ⊆ Γ.trace →
    HolomorphicOn Ω f → HolomorphicOn Ω g → Γ.trace ⊆ Ω →
    (∀ a, Γ.index a ≠ 0 → a ∈ Ω) →
    (∀ z ∈ Γ.trace, ‖g z - f z‖ < ‖f z‖) →
    (∀ a ∈ D,
      Ch05.LocalZeroFactorization.HasFiniteOrder_value f a (analyticOrderNatAt f a) ∧
      Ch05.LocalZeroFactorization.HasFiniteOrder_value g a (analyticOrderNatAt g a)) ∧
    ∃ s t : Finset ℂ,
      (∀ a, a ∈ s ↔ a ∈ D ∧ f a = 0) ∧
      (∀ a, a ∈ t ↔ a ∈ D ∧ g a = 0) ∧
      (∑ a ∈ s, analyticOrderNatAt f a) = ∑ a ∈ t, analyticOrderNatAt g a

/-- The positive circle case, on any open neighborhood of its closed disk. -/
def circle_type : Prop :=
  ∀ (Ω : Set ℂ) (c : ℂ) (r : ℝ) (f g : ℂ → ℂ), 0 < r →
    HolomorphicOn Ω f → HolomorphicOn Ω g → Metric.closedBall c r ⊆ Ω →
    (∀ z ∈ Metric.sphere c r, ‖g z - f z‖ < ‖f z‖) →
    (∀ a ∈ Metric.ball c r,
      Ch05.LocalZeroFactorization.HasFiniteOrder_value f a (analyticOrderNatAt f a) ∧
      Ch05.LocalZeroFactorization.HasFiniteOrder_value g a (analyticOrderNatAt g a)) ∧
    ∃ s t : Finset ℂ,
      (∀ a, a ∈ s ↔ a ∈ Metric.ball c r ∧ f a = 0) ∧
      (∀ a, a ∈ t ↔ a ∈ Metric.ball c r ∧ g a = 0) ∧
      (∑ a ∈ s, analyticOrderNatAt f a) = ∑ a ∈ t, analyticOrderNatAt g a

end Specs.D12Complex.Ch09.Rouche
