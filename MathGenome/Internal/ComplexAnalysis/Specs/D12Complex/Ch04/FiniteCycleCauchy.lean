import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.DividedDifferenceRegularity
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.IndexProperties

/-! The full finite-cycle Cauchy theorem (paper.tex:1071–1142).
The cycles, active traces, integrals and indices are the canonical Ch03/Ch04
objects. The open set may be empty or disconnected, and cycle coefficients
are arbitrary integers. No simplicity or homotopy hypothesis is imposed. -/
noncomputable section
open Set

namespace Specs.D12Complex.Ch04.FiniteCycleCauchy
open _root_.D12Complex

def cycle_cauchy_theorem_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ) (Γ : IntegralCycle),
    HolomorphicOn U f → Γ.trace ⊆ U →
    (∀ w, w ∉ U → Γ.index w = 0) → Γ.integral f = 0

def cycle_cauchy_formula_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ) (Γ : IntegralCycle),
    HolomorphicOn U f → Γ.trace ⊆ U →
    (∀ w, w ∉ U → Γ.index w = 0) →
    ∀ a ∈ U, a ∉ Γ.trace →
      Γ.index a * f a = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        Γ.integral (fun z => f z / (z - a))

def cycle_cauchy_derivatives_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ) (Γ : IntegralCycle),
    HolomorphicOn U f → Γ.trace ⊆ U →
    (∀ w, w ∉ U → Γ.index w = 0) →
    ∀ a ∈ U, a ∉ Γ.trace → ∀ n : ℕ,
      Γ.index a * iteratedDeriv n f a =
        (n.factorial : ℂ) / (2 * Real.pi * Complex.I) *
          Γ.integral (fun z => f z / (z - a) ^ (n + 1))

end Specs.D12Complex.Ch04.FiniteCycleCauchy
