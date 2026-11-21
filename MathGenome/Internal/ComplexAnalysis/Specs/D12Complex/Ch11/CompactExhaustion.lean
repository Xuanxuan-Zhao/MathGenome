import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! The explicit compact exhaustion in paper.tex, d12:11-01.
`infEDist` is an extended nonnegative real distance, hence is infinity for the
empty complement. Indices are natural numbers, with all assertions restricted
to the positive integers. No connectedness or nonemptiness of Ω is required. -/

open Set

namespace D12Complex.Ch11

/-- The stage `{z ∈ Ω | ‖z‖ ≤ j ∧ dist(z, Ωᶜ) ≥ 1/j}`. -/
def compactExhaustionStage (Ω : Set ℂ) (j : ℕ) : Set ℂ :=
  {z | z ∈ Ω ∧ ‖z‖ ≤ (j : ℝ) ∧
    ENNReal.ofReal (1 / (j : ℝ)) ≤ Metric.infEDist z Ωᶜ}

end D12Complex.Ch11

namespace Specs.D12Complex.Ch11.CompactExhaustion

open _root_.D12Complex.Ch11

def compact_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → ∀ j : ℕ, 1 ≤ j → IsCompact (compactExhaustionStage Ω j)

def nesting_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → ∀ j : ℕ, 1 ≤ j →
    compactExhaustionStage Ω j ⊆ interior (compactExhaustionStage Ω (j + 1))

def union_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω →
    (⋃ (j : ℕ) (_ : 1 ≤ j), compactExhaustionStage Ω j) = Ω

def cofinal_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → ∀ L : Set ℂ, IsCompact L → L ⊆ Ω →
    ∃ j : ℕ, 1 ≤ j ∧ L ⊆ compactExhaustionStage Ω j

def empty_type : Prop :=
  ∀ j : ℕ, compactExhaustionStage ∅ j = ∅

def univ_type : Prop :=
  ∀ j : ℕ, compactExhaustionStage univ j = Metric.closedBall 0 (j : ℝ)

end Specs.D12Complex.Ch11.CompactExhaustion
