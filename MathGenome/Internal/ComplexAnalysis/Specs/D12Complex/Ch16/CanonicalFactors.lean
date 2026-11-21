import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Independent specification of paper.tex:2778–2788, canonical factors.
The logarithm is the negative tail series, not a principal log of the factor.
Its values outside the unit disk carry no branch assertion. -/
noncomputable section
namespace Specs.D12Complex.Ch16.CanonicalFactors
open _root_.D12Complex

def factor_type := ℕ → ℂ → ℂ
def factor_value : factor_type := fun p w =>
  (1 - w) * Complex.exp (∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1 : ℂ))

def logFactor_type := ℕ → ℂ → ℂ
def logFactor_value : logFactor_type := fun p w =>
  -(∑' n : ℕ, w ^ (n + p + 1) / (n + p + 1 : ℂ))

def factor_zero_index_type : Prop := ∀ w : ℂ, factor_value 0 w = 1 - w

def factor_entire_type : Prop := ∀ p : ℕ, HolomorphicOn Set.univ (factor_value p)

def factor_eq_zero_iff_type : Prop :=
  ∀ (p : ℕ) (w : ℂ), factor_value p w = 0 ↔ w = 1

def factor_simple_zero_type : Prop :=
  ∀ p : ℕ, analyticOrderAt (factor_value p) 1 = 1

def logFactor_hasSum_type : Prop := ∀ (p : ℕ) (w : ℂ), ‖w‖ < 1 →
  HasSum (fun n : ℕ => -(w ^ (n + p + 1) / (n + p + 1 : ℂ))) (logFactor_value p w)

def logFactor_eq_log_add_type : Prop := ∀ (p : ℕ) (w : ℂ), ‖w‖ < 1 →
  logFactor_value p w = Complex.log (1 - w) +
    ∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1 : ℂ)

def logFactor_holomorphic_type : Prop :=
  ∀ p : ℕ, HolomorphicOn (Metric.ball 0 1) (logFactor_value p)

def logFactor_zero_type : Prop := ∀ p : ℕ, logFactor_value p 0 = 0

def exp_logFactor_type : Prop := ∀ (p : ℕ) (w : ℂ), ‖w‖ < 1 →
  Complex.exp (logFactor_value p w) = factor_value p w

def norm_logFactor_le_type : Prop := ∀ (p : ℕ) (w : ℂ), ‖w‖ ≤ 1 / 2 →
  ‖logFactor_value p w‖ ≤ 2 * ‖w‖ ^ (p + 1)

def norm_factor_sub_one_le_type : Prop := ∀ (p : ℕ) (w : ℂ), ‖w‖ ≤ 1 / 2 →
  ‖factor_value p w - 1‖ ≤ 6 * ‖w‖ ^ (p + 1)

end Specs.D12Complex.Ch16.CanonicalFactors
