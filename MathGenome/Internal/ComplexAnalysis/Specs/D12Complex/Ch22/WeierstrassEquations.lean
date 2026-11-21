import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.WeierstrassSeries

/-! Independent specification of the differential-equation portion of
paper.tex:3895–3922, D12.22.06. The canonical regularized series and integer
lattice are reused. The invariants use the nonzero lattice vectors, with the
source's factors 60 and 140. At a pole, an identity means equality on a
punctured neighborhood, independently of the assigned values at that pole. -/
noncomputable section
open Filter
open scoped Topology

namespace Specs.D12Complex.Ch22.WeierstrassEquations

open WeierstrassSeries (lattice weierstrassP)

def g₂ (ω₁ ω₂ : ℂ) : ℂ :=
  60 * ∑' l : {l : lattice ω₁ ω₂ // l ≠ 0}, 1 / (l.1 : ℂ) ^ 4

def g₃ (ω₁ ω₂ : ℂ) : ℂ :=
  140 * ∑' l : {l : lattice ω₁ ω₂ // l ≠ 0}, 1 / (l.1 : ℂ) ^ 6

def invariant_type := ℂ → ℂ → ℂ

def absolute_convergence_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    Summable (fun l : {l : lattice ω₁ ω₂ // l ≠ 0} => ‖1 / (l.1 : ℂ) ^ 4‖) ∧
    Summable (fun l : {l : lattice ω₁ ω₂ // l ≠ 0} => ‖1 / (l.1 : ℂ) ^ 6‖)

/-- These are actual meromorphic derivatives of the canonical series. -/
def meromorphic_derivatives_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    Meromorphic (deriv (weierstrassP ω₁ ω₂)) ∧
      Meromorphic (deriv (deriv (weierstrassP ω₁ ω₂)))

def first_equation_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ z ∉ lattice ω₁ ω₂,
    deriv (weierstrassP ω₁ ω₂) z ^ 2 =
      4 * weierstrassP ω₁ ω₂ z ^ 3 - g₂ ω₁ ω₂ * weierstrassP ω₁ ω₂ z - g₃ ω₁ ω₂

def second_equation_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ z ∉ lattice ω₁ ω₂,
    deriv (deriv (weierstrassP ω₁ ω₂)) z =
      6 * weierstrassP ω₁ ω₂ z ^ 2 - g₂ ω₁ ω₂ / 2

def first_equation_germ_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ a : ℂ,
    (fun z => deriv (weierstrassP ω₁ ω₂) z ^ 2) =ᶠ[𝓝[≠] a]
      (fun z => 4 * weierstrassP ω₁ ω₂ z ^ 3 -
        g₂ ω₁ ω₂ * weierstrassP ω₁ ω₂ z - g₃ ω₁ ω₂)

def second_equation_germ_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ a : ℂ,
    deriv (deriv (weierstrassP ω₁ ω₂)) =ᶠ[𝓝[≠] a]
      (fun z => 6 * weierstrassP ω₁ ω₂ z ^ 2 - g₂ ω₁ ω₂ / 2)

end Specs.D12Complex.Ch22.WeierstrassEquations
