import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.PositiveRoots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Order.LiminfLimsup

/-!
Independent interface for K03.13.power_series, paper.tex:1353–1357.
Coefficients are formal sequences, truncations are canonical finite polynomials,
and values exist only on the domain of ordinary numerical convergence.
Real coefficients and complex coefficients are treated separately, with a
real center in both cases. Complex coefficients allow complex arguments;
real arguments are included by the usual embedding. Real coefficients can
also be embedded for complex estimates.

The radius is an extended nonnegative real, defined by reciprocal root limsup
using positive integer roots. Index n+1 omits only the unused degree-zero root.
This definition makes no assertion of convergence or divergence at an argument;
those assertions, and boundary examples, belong to the later radius goals.
-/
namespace Specs.SingleVariableAnalysis.Ch13.PowerSeries

open Specs.SingleVariableAnalysis.Ch11.PartialSums
open Specs.SingleVariableAnalysis.Ch01.PositiveRoots
open scoped BigOperators ENNReal

def RealPowerSeriesCoefficientsType : Type 1 := Type

def RealPowerSeriesCoefficientsValue : RealPowerSeriesCoefficientsType :=
  ℕ → ℝ

def realPowerSeriesTermType : Type := (ℕ → ℝ) → ℝ → ℝ → ℕ → ℝ

noncomputable def realPowerSeriesTermValue : realPowerSeriesTermType :=
  fun a c x n => a n * (x - c) ^ n

def realPowerSeriesPartialSumType : Type := (ℕ → ℝ) → ℝ → ℝ → ℕ → ℝ

noncomputable def realPowerSeriesPartialSumValue : realPowerSeriesPartialSumType :=
  fun a c x => realPartialSumValue (realPowerSeriesTermValue a c x)

def RealPowerSeriesHasSumType : Type := (ℕ → ℝ) → ℝ → ℝ → ℝ → Prop

noncomputable def RealPowerSeriesHasSumValue : RealPowerSeriesHasSumType :=
  fun a c x S => realSeriesHasSumValue (realPowerSeriesTermValue a c x) S

def RealPowerSeriesConvergesType : Type := (ℕ → ℝ) → ℝ → ℝ → Prop

noncomputable def RealPowerSeriesConvergesValue : RealPowerSeriesConvergesType :=
  fun a c x => ∃ S : ℝ, RealPowerSeriesHasSumValue a c x S

def RealPowerSeriesAbsolutelyConvergesType : Type := (ℕ → ℝ) → ℝ → ℝ → Prop

noncomputable def RealPowerSeriesAbsolutelyConvergesValue : RealPowerSeriesAbsolutelyConvergesType :=
  fun a c x => realSeriesConvergesValue (fun n => |realPowerSeriesTermValue a c x n|)

def realPowerPolynomialType : Type := (ℕ → ℝ) → ℝ → ℕ → Polynomial ℝ

noncomputable def realPowerPolynomialValue : realPowerPolynomialType :=
  fun a c N => ∑ n ∈ Finset.range (N + 1),
    Polynomial.C (a n) * (Polynomial.X - Polynomial.C c) ^ n

def realPowerSeriesDomainType : Type := (ℕ → ℝ) → ℝ → Set ℝ

noncomputable def realPowerSeriesDomainValue : realPowerSeriesDomainType :=
  fun a c => {x | RealPowerSeriesConvergesValue a c x}

def realPowerSeriesSumType : Type := (a : ℕ → ℝ) → (c : ℝ) → { x // x ∈ realPowerSeriesDomainValue a c } → ℝ

noncomputable def realPowerSeriesSumValue : realPowerSeriesSumType :=
  fun _ _ x => Classical.choose x.property

def realPowerSeriesRootGrowthType : Type := (ℕ → ℝ) → ℝ≥0∞

noncomputable def realPowerSeriesRootGrowthValue : realPowerSeriesRootGrowthType :=
  fun a => Filter.limsup (fun n : ℕ =>
    ENNReal.ofReal (nonnegativeRootValue (n + 1) (|a (n + 1)|))) Filter.atTop

def realPowerSeriesRadiusType : Type := (ℕ → ℝ) → ℝ≥0∞

noncomputable def realPowerSeriesRadiusValue : realPowerSeriesRadiusType :=
  fun a => (realPowerSeriesRootGrowthValue a)⁻¹

def real_powerSeries_hasSum_iff : Prop :=
  ∀ (a : ℕ → ℝ) (c : ℝ) (x S : ℝ),
    RealPowerSeriesHasSumValue a c x S ↔
      ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N ≥ M,
        |realPowerSeriesPartialSumValue a c x N - S| < ε

def real_powerPolynomial_eval : Prop :=
  ∀ (a : ℕ → ℝ) (c : ℝ) (N : ℕ) (x : ℝ),
    (realPowerPolynomialValue a c N).eval x = realPowerSeriesPartialSumValue a c x N

def real_powerSeries_term_magnitude : Prop :=
  ∀ (a : ℕ → ℝ) (c : ℝ) (x : ℝ) (n : ℕ),
    |realPowerSeriesTermValue a c x n| = |a n| * |x - c| ^ n

def real_powerSeries_sum_unique : Prop :=
  ∀ (a : ℕ → ℝ) (c : ℝ) (x S T : ℝ),
    RealPowerSeriesHasSumValue a c x S → RealPowerSeriesHasSumValue a c x T → S = T

def real_powerSeriesSum_hasSum : Prop :=
  ∀ (a : ℕ → ℝ) (c : ℝ) (x : { x // x ∈ realPowerSeriesDomainValue a c }),
    RealPowerSeriesHasSumValue a c x.val (realPowerSeriesSumValue a c x)

def real_powerSeriesSum_eq_iff : Prop :=
  ∀ (a : ℕ → ℝ) (c : ℝ) (x : { x // x ∈ realPowerSeriesDomainValue a c }) (S : ℝ),
    realPowerSeriesSumValue a c x = S ↔ RealPowerSeriesHasSumValue a c x.val S

def real_powerSeries_radius_zero_growth : Prop :=
  ∀ a : ℕ → ℝ, realPowerSeriesRootGrowthValue a = 0 →
    realPowerSeriesRadiusValue a = ⊤

def real_powerSeries_radius_infinite_growth : Prop :=
  ∀ a : ℕ → ℝ, realPowerSeriesRootGrowthValue a = ⊤ →
    realPowerSeriesRadiusValue a = 0

def ComplexPowerSeriesCoefficientsType : Type 1 := Type

def ComplexPowerSeriesCoefficientsValue : ComplexPowerSeriesCoefficientsType :=
  ℕ → ℂ

def complexPowerSeriesTermType : Type := (ℕ → ℂ) → ℝ → ℂ → ℕ → ℂ

noncomputable def complexPowerSeriesTermValue : complexPowerSeriesTermType :=
  fun a c z n => a n * (z - (c : ℂ)) ^ n

def complexPowerSeriesPartialSumType : Type := (ℕ → ℂ) → ℝ → ℂ → ℕ → ℂ

noncomputable def complexPowerSeriesPartialSumValue : complexPowerSeriesPartialSumType :=
  fun a c z => complexPartialSumValue (complexPowerSeriesTermValue a c z)

def ComplexPowerSeriesHasSumType : Type := (ℕ → ℂ) → ℝ → ℂ → ℂ → Prop

noncomputable def ComplexPowerSeriesHasSumValue : ComplexPowerSeriesHasSumType :=
  fun a c z S => complexSeriesHasSumValue (complexPowerSeriesTermValue a c z) S

def ComplexPowerSeriesConvergesType : Type := (ℕ → ℂ) → ℝ → ℂ → Prop

noncomputable def ComplexPowerSeriesConvergesValue : ComplexPowerSeriesConvergesType :=
  fun a c z => ∃ S : ℂ, ComplexPowerSeriesHasSumValue a c z S

def ComplexPowerSeriesAbsolutelyConvergesType : Type := (ℕ → ℂ) → ℝ → ℂ → Prop

noncomputable def ComplexPowerSeriesAbsolutelyConvergesValue : ComplexPowerSeriesAbsolutelyConvergesType :=
  fun a c z => realSeriesConvergesValue (fun n => ‖complexPowerSeriesTermValue a c z n‖)

def complexPowerPolynomialType : Type := (ℕ → ℂ) → ℝ → ℕ → Polynomial ℂ

noncomputable def complexPowerPolynomialValue : complexPowerPolynomialType :=
  fun a c N => ∑ n ∈ Finset.range (N + 1),
    Polynomial.C (a n) * (Polynomial.X - Polynomial.C (c : ℂ)) ^ n

def complexPowerSeriesDomainType : Type := (ℕ → ℂ) → ℝ → Set ℂ

noncomputable def complexPowerSeriesDomainValue : complexPowerSeriesDomainType :=
  fun a c => {z | ComplexPowerSeriesConvergesValue a c z}

def complexPowerSeriesSumType : Type := (a : ℕ → ℂ) → (c : ℝ) → { z // z ∈ complexPowerSeriesDomainValue a c } → ℂ

noncomputable def complexPowerSeriesSumValue : complexPowerSeriesSumType :=
  fun _ _ x => Classical.choose x.property

def complexPowerSeriesRootGrowthType : Type := (ℕ → ℂ) → ℝ≥0∞

noncomputable def complexPowerSeriesRootGrowthValue : complexPowerSeriesRootGrowthType :=
  fun a => Filter.limsup (fun n : ℕ =>
    ENNReal.ofReal (nonnegativeRootValue (n + 1) (‖a (n + 1)‖))) Filter.atTop

def complexPowerSeriesRadiusType : Type := (ℕ → ℂ) → ℝ≥0∞

noncomputable def complexPowerSeriesRadiusValue : complexPowerSeriesRadiusType :=
  fun a => (complexPowerSeriesRootGrowthValue a)⁻¹

def complex_powerSeries_hasSum_iff : Prop :=
  ∀ (a : ℕ → ℂ) (c : ℝ) (z S : ℂ),
    ComplexPowerSeriesHasSumValue a c z S ↔
      ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N ≥ M,
        ‖complexPowerSeriesPartialSumValue a c z N - S‖ < ε

def complex_powerPolynomial_eval : Prop :=
  ∀ (a : ℕ → ℂ) (c : ℝ) (N : ℕ) (z : ℂ),
    (complexPowerPolynomialValue a c N).eval z = complexPowerSeriesPartialSumValue a c z N

def complex_powerSeries_term_magnitude : Prop :=
  ∀ (a : ℕ → ℂ) (c : ℝ) (z : ℂ) (n : ℕ),
    ‖complexPowerSeriesTermValue a c z n‖ = ‖a n‖ * ‖z - (c : ℂ)‖ ^ n

def complex_powerSeries_sum_unique : Prop :=
  ∀ (a : ℕ → ℂ) (c : ℝ) (z S T : ℂ),
    ComplexPowerSeriesHasSumValue a c z S → ComplexPowerSeriesHasSumValue a c z T → S = T

def complex_powerSeriesSum_hasSum : Prop :=
  ∀ (a : ℕ → ℂ) (c : ℝ) (z : { z // z ∈ complexPowerSeriesDomainValue a c }),
    ComplexPowerSeriesHasSumValue a c z.val (complexPowerSeriesSumValue a c z)

def complex_powerSeriesSum_eq_iff : Prop :=
  ∀ (a : ℕ → ℂ) (c : ℝ) (z : { z // z ∈ complexPowerSeriesDomainValue a c }) (S : ℂ),
    complexPowerSeriesSumValue a c z = S ↔ ComplexPowerSeriesHasSumValue a c z.val S

def complex_powerSeries_radius_zero_growth : Prop :=
  ∀ a : ℕ → ℂ, complexPowerSeriesRootGrowthValue a = 0 →
    complexPowerSeriesRadiusValue a = ⊤

def complex_powerSeries_radius_infinite_growth : Prop :=
  ∀ a : ℕ → ℂ, complexPowerSeriesRootGrowthValue a = ⊤ →
    complexPowerSeriesRadiusValue a = 0

def real_powerSeries_term_complex : Prop :=
  ∀ (a : ℕ → ℝ) (c x : ℝ) (n : ℕ),
    complexPowerSeriesTermValue (fun n => (a n : ℂ)) c (x : ℂ) n =
      (realPowerSeriesTermValue a c x n : ℂ)

def real_powerSeries_partialSum_complex : Prop :=
  ∀ (a : ℕ → ℝ) (c x : ℝ) (N : ℕ),
    complexPowerSeriesPartialSumValue (fun n => (a n : ℂ)) c (x : ℂ) N =
      (realPowerSeriesPartialSumValue a c x N : ℂ)

def real_powerSeries_hasSum_complex_iff : Prop :=
  ∀ (a : ℕ → ℝ) (c x S : ℝ),
    ComplexPowerSeriesHasSumValue (fun n => (a n : ℂ)) c (x : ℂ) (S : ℂ) ↔
      RealPowerSeriesHasSumValue a c x S

end Specs.SingleVariableAnalysis.Ch13.PowerSeries
