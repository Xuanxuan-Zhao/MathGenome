import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.CompatibleExhaustion

/-! The Runge corrections used in the proof of d12:16-07 (paper.tex:2832).
The conclusions concern actual complex-valued weakly holomorphic functions.
No connectedness or nonemptiness is required. -/
noncomputable section
open Set

namespace Specs.D12Complex.Ch16.RungeHolomorphicCorrections
open _root_.D12Complex _root_.D12Complex.Ch15

/-- Approximate a holomorphic germ near a relatively hole-free compact set
by a function holomorphic on the whole prescribed open set. -/
def holomorphic_correction_type : Prop :=
  ∀ (Ω K U : Set ℂ) (q : ℂ → ℂ),
    IsOpen Ω → IsCompact K → K ⊆ Ω → HasRelativeHoleProperty Ω K →
    IsOpen U → K ⊆ U → HolomorphicOn U q →
    ∀ ε : ℝ, 0 < ε → ∃ r : ℂ → ℂ,
      HolomorphicOn Ω r ∧ ∀ z ∈ K, ‖q z - r z‖ < ε

/-- Simultaneous selection of corrections on a compatible exhaustion.
The neighborhoods on which the functions q n are holomorphic may vary with n. -/
def holomorphic_corrections_type : Prop :=
  ∀ (Ω : Set ℂ) (K : ℕ → Set ℂ) (q : ℕ → ℂ → ℂ) (ε : ℕ → ℝ),
    IsOpen Ω → IsCompatibleExhaustion Ω K →
    (∀ n, ∃ U : Set ℂ, IsOpen U ∧ K n ⊆ U ∧ HolomorphicOn U (q n)) →
    (∀ n, 0 < ε n) → ∃ r : ℕ → ℂ → ℂ,
      (∀ n, HolomorphicOn Ω (r n)) ∧
      ∀ n, ∀ z ∈ K n, ‖q n z - r n z‖ < ε n

end Specs.D12Complex.Ch16.RungeHolomorphicCorrections
