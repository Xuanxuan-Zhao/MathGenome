import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.CantorFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent statements for the digit and exponent part of
`paper.tex:6129–6134`. The sharp Hölder estimate is allocated separately.
The zero-based digit `n` below is the paper's digit `n+1`.
`Bool` encodes exactly the allowed digits 0 and 1. -/
noncomputable section
open Set

namespace Specs.D11.Ch22.CantorDigitSurjection

abbrev alpha_type := ℝ
def alpha_value : ℝ := Real.log 2 / Real.log 3

def alpha_bounds : Prop := 0 < alpha_value ∧ alpha_value < 1
def three_rpow_alpha : Prop := (3 : ℝ) ^ alpha_value = 2

/-- Restriction of the existing canonical staircase to the existing Cantor set. -/
abbrev F_type := ↥Specs.D11.Ch03.CantorSet.C_value → ℝ
def F_value : F_type := fun x => Specs.D11.Ch03.CantorFunction.Gamma_value x

def unique_digits : Prop := ∀ x ∈ Specs.D11.Ch03.CantorSet.C_value,
  ∃! a : ℕ → Bool, (∑' n, (if a n then (2 : ℝ) else 0) / 3 ^ (n + 1)) = x

-- The series predicate is written independently, rather than assuming an encoding certificate.
def F_digit_formula : Prop := ∀ (x : ↥Specs.D11.Ch03.CantorSet.C_value) (a : ℕ → Bool),
  (∑' n, (if a n then (2 : ℝ) else 0) / 3 ^ (n + 1)) = (x : ℝ) →
  F_value x = ∑' n, (if a n then (1 : ℝ) else 0) / 2 ^ (n + 1)

def allowed_series_mem : Prop := ∀ a : ℕ → Bool,
  (∑' n, (if a n then (2 : ℝ) else 0) / 3 ^ (n + 1)) ∈
    Specs.D11.Ch03.CantorSet.C_value

def F_range : Prop := range F_value = Icc (0 : ℝ) 1

def endpoints : Prop :=
  (0 : ℝ) ∈ Specs.D11.Ch03.CantorSet.C_value ∧
  (1 : ℝ) ∈ Specs.D11.Ch03.CantorSet.C_value ∧
  (∑' n, (if (false : Bool) then (2 : ℝ) else 0) / 3 ^ (n + 1)) = 0 ∧
  (∑' n, (if (true : Bool) then (2 : ℝ) else 0) / 3 ^ (n + 1)) = 1 ∧
  Specs.D11.Ch03.CantorFunction.Gamma_value 0 = 0 ∧
  Specs.D11.Ch03.CantorFunction.Gamma_value 1 = 1

/-- Binary ambiguity really occurs: the two ends of the first deleted gap
have different unique allowed ternary expansions, but the same binary value. -/
def binary_ambiguity : Prop :=
  (1 / 3 : ℝ) ∈ Specs.D11.Ch03.CantorSet.C_value ∧
  (2 / 3 : ℝ) ∈ Specs.D11.Ch03.CantorSet.C_value ∧
  (1 / 3 : ℝ) ≠ 2 / 3 ∧
  Specs.D11.Ch03.CantorFunction.Gamma_value (1 / 3) = 1 / 2 ∧
  Specs.D11.Ch03.CantorFunction.Gamma_value (2 / 3) = 1 / 2

end Specs.D11.Ch22.CantorDigitSurjection
