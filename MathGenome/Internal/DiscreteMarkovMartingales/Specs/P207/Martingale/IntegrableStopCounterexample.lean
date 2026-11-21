import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.DoublingExample
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.Stopping

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory

noncomputable section
namespace P207.DoublingStop
open P207.Doubling

/-- The first tail is numbered starting at one; an all-heads path has time infinity. -/
def firstTail (ω : Ω) : WithTop ℕ := by
  classical
  exact if h : ∃ k : ℕ, toss k ω = false then (Nat.find h + 1 : ℕ) else ⊤

/-- Real representative of the duration, set to zero on the infinite layer. -/
def duration (ω : Ω) : ℝ := ((firstTail ω).untopD 0 : ℕ)

/-- The stopped value uses the explicitly specified zero on the infinite layer. -/
def stoppedValue : Ω → ℝ := P207.fullStoppedValue M firstTail (fun _ => 0)

end P207.DoublingStop

namespace P207.DoublingStopSpec
open P207.Doubling P207.DoublingStop

def firstTailType := Ω → WithTop ℕ
noncomputable def firstTailValue : firstTailType := by
  classical
  exact fun ω => if h : ∃ k : ℕ, toss k ω = false then (Nat.find h + 1 : ℕ) else ⊤
def durationType := Ω → ℝ
noncomputable def durationValue : durationType := fun ω => ((firstTail ω).untopD 0 : ℕ)
def stoppedValueType := Ω → ℝ
noncomputable def stoppedValueValue : stoppedValueType :=
  P207.fullStoppedValue M firstTail (fun _ => 0)

def firstTail_gt_iff : Prop := ∀ (k : ℕ) (ω : Ω), (k : WithTop ℕ) < firstTail ω ↔ ω ∈ allHeads k

def stoppingTime : Prop := P207.IsDiscreteStoppingTime filtration firstTail

def tail_probability : Prop := ∀ k : ℕ,
  μ {ω | (k : WithTop ℕ) < firstTail ω} = ((2 : ℝ≥0∞)⁻¹) ^ k

def finite_ae : Prop := ∀ᵐ ω ∂μ, firstTail ω < ⊤

def integrable_duration : Prop := Integrable duration μ

def expected_duration : Prop := (∫ ω, duration ω ∂μ) = 2

def stoppedValue_zero : Prop := ∀ ω, stoppedValue ω = 0

def expectation_failure : Prop :=
  Integrable stoppedValue μ ∧ (∫ ω, stoppedValue ω ∂μ) = 0 ∧
  (∀ ω, M 0 ω = 1) ∧ (∫ ω, stoppedValue ω ∂μ) ≠ ∫ ω, M 0 ω ∂μ

def conditional_abs_increment : Prop := ∀ k : ℕ,
  μ[fun ω => |M (k + 1) ω - M k ω| | filtration k] =ᵐ[μ] M k

def conditional_abs_increment_on_heads : Prop := ∀ k : ℕ,
  μ (allHeads k) > 0 ∧ ∀ᵐ ω ∂μ, ω ∈ allHeads k →
    μ[fun ω => |M (k + 1) ω - M k ω| | filtration k] ω = (2 : ℝ) ^ k

def no_uniform_increment_bound : Prop := ¬ ∃ C : ℝ, ∀ k : ℕ,
  μ[fun ω => |M (k + 1) ω - M k ω| | filtration k] ≤ᵐ[μ] fun _ => C

end P207.DoublingStopSpec
