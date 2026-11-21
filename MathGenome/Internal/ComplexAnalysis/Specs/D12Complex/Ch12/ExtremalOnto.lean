import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch12.ExtremalUnivalent

/-! The full conclusion of paper.tex:2476–2483 (D12.12.03).
The premise is the universal square-root property on the given proper
plane domain; simple connectivity is not assumed. The extremal class is
exactly the upstream class of injective holomorphic disk maps fixing z₀.
Both statements include a holomorphic inverse on the entire open disk. -/

noncomputable section

namespace Specs.D12Complex.Ch12.ExtremalOnto
open _root_.D12Complex

/-- Every member attaining the derivative-norm supremum fills the disk
and has a holomorphic inverse. No phase normalization of this member is
required. -/
def extremal_onto_type : Prop :=
  ∀ (Ω : Set ℂ), IsDomain Ω → Ω ≠ Set.univ →
    (∀ g : ℂ → ℂ, HolomorphicOn Ω g → (∀ z ∈ Ω, g z ≠ 0) →
      ∃ s : ℂ → ℂ, HolomorphicOn Ω s ∧ ∀ z ∈ Ω, (s z) ^ 2 = g z) →
    ∀ z₀ ∈ Ω, ∀ F : ℂ → ℂ,
      F ∈ ExtremalUnivalent.normalizedFamily_value Ω z₀ →
      ‖deriv F z₀‖ = ExtremalUnivalent.derivativeSupremum_value Ω z₀ →
      F '' Ω = Metric.ball 0 1 ∧ IsBiholomorphism Ω (Metric.ball 0 1) F

/-- A normalized biholomorphism exists, including a holomorphic inverse,
with derivative a strictly positive real complex number. -/
def normalized_biholomorphism_type : Prop :=
  ∀ (Ω : Set ℂ), IsDomain Ω → Ω ≠ Set.univ →
    (∀ g : ℂ → ℂ, HolomorphicOn Ω g → (∀ z ∈ Ω, g z ≠ 0) →
      ∃ s : ℂ → ℂ, HolomorphicOn Ω s ∧ ∀ z ∈ Ω, (s z) ^ 2 = g z) →
    ∀ z₀ ∈ Ω, ∃ F G : ℂ → ℂ,
      BiholomorphicPair Ω (Metric.ball 0 1) F G ∧ F z₀ = 0 ∧
      ∃ t : ℝ, 0 < t ∧ deriv F z₀ = (t : ℂ)

end Specs.D12Complex.Ch12.ExtremalOnto
