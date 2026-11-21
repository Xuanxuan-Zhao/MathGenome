import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.WeierstrassSeries

/-! Independent specification for paper.tex:3876–3893, D12.22.05.
All equalities are equalities of meromorphic germs: at every center they hold
on a punctured neighborhood. In particular no value assigned at a pole is
part of the meaning of parity or of a period. The derivative is the actual
complex derivative of the canonical regularized series. -/
noncomputable section
open Filter
open scoped Topology

namespace Specs.D12Complex.Ch22.WeierstrassPeriods

open WeierstrassSeries (weierstrassP lattice)

def even_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ a : ℂ,
    (fun z => weierstrassP ω₁ ω₂ (-z)) =ᶠ[𝓝[≠] a] weierstrassP ω₁ ω₂

def derivative_odd_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ a : ℂ,
    (fun z => deriv (weierstrassP ω₁ ω₂) (-z)) =ᶠ[𝓝[≠] a]
      (fun z => -deriv (weierstrassP ω₁ ω₂) z)

def periodic_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ τ ∈ lattice ω₁ ω₂, ∀ a : ℂ,
      (fun z => weierstrassP ω₁ ω₂ (z + τ)) =ᶠ[𝓝[≠] a] weierstrassP ω₁ ω₂

def derivative_periodic_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ τ ∈ lattice ω₁ ω₂, ∀ a : ℂ,
      (fun z => deriv (weierstrassP ω₁ ω₂) (z + τ)) =ᶠ[𝓝[≠] a]
        deriv (weierstrassP ω₁ ω₂)

/-- The full set of complex periods, including zero, is exactly the lattice. -/
def period_iff_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ τ : ℂ,
    (∀ a : ℂ, (fun z => weierstrassP ω₁ ω₂ (z + τ)) =ᶠ[𝓝[≠] a]
      weierstrassP ω₁ ω₂) ↔ τ ∈ lattice ω₁ ω₂

end Specs.D12Complex.Ch22.WeierstrassPeriods
