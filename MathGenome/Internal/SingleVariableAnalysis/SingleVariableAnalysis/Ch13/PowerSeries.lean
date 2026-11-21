import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.PartialSums
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.PositiveRoots
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.PowerSeries

/-!
# Power series: formal data, finite polynomials and ordinary values

K03.13.power_series, paper.tex:1353–1357. The only scalar fields are the
canonical real and complex numbers, and centers are real. All truncations
include indices 0 through N. `HasSum` below is the upstream ordinary-series
predicate, so it allows conditional convergence. Absolute convergence is a
separate predicate. No unconditional infinite sum is used to define a value.

The sum functions take an argument in their actual convergence domain.
Their defining choice is proved to be the unique finite limit of the
ordered partial sums. In particular, no default scalar is assigned to a
divergent series. Complex arguments are available for norm estimates, and
real coefficients embed compatibly in the complex expression.

The extended radius is the reciprocal of the limsup of positive integer
roots of coefficient magnitudes. The Cauchy–Hadamard convergence conclusions
are a separate obligation; this module assumes none of them.
-/
namespace SingleVariableAnalysis

open scoped BigOperators ENNReal

def RealPowerSeriesCoefficients : Type :=
  ℕ → ℝ

noncomputable def realPowerSeriesTerm : (ℕ → ℝ) → ℝ → ℝ → ℕ → ℝ :=
  fun a c x n => a n * (x - c) ^ n

noncomputable def realPowerSeriesPartialSum : (ℕ → ℝ) → ℝ → ℝ → ℕ → ℝ :=
  fun a c x => realPartialSum (realPowerSeriesTerm a c x)

noncomputable def RealPowerSeriesHasSum : (ℕ → ℝ) → ℝ → ℝ → ℝ → Prop :=
  fun a c x S => RealSeriesHasSum (realPowerSeriesTerm a c x) S

noncomputable def RealPowerSeriesConverges : (ℕ → ℝ) → ℝ → ℝ → Prop :=
  fun a c x => ∃ S : ℝ, RealPowerSeriesHasSum a c x S

noncomputable def RealPowerSeriesAbsolutelyConverges : (ℕ → ℝ) → ℝ → ℝ → Prop :=
  fun a c x => RealSeriesConverges (fun n => |realPowerSeriesTerm a c x n|)

noncomputable def realPowerPolynomial : (ℕ → ℝ) → ℝ → ℕ → Polynomial ℝ :=
  fun a c N => ∑ n ∈ Finset.range (N + 1),
    Polynomial.C (a n) * (Polynomial.X - Polynomial.C c) ^ n

noncomputable def realPowerSeriesDomain : (ℕ → ℝ) → ℝ → Set ℝ :=
  fun a c => {x | RealPowerSeriesConverges a c x}

noncomputable def realPowerSeriesSum : (a : ℕ → ℝ) → (c : ℝ) → { x // x ∈ realPowerSeriesDomain a c } → ℝ :=
  fun _ _ x => Classical.choose x.property

noncomputable def realPowerSeriesRootGrowth : (ℕ → ℝ) → ℝ≥0∞ :=
  fun a => Filter.limsup (fun n : ℕ =>
    ENNReal.ofReal (nonnegativeRoot (n + 1) (|a (n + 1)|))) Filter.atTop

noncomputable def realPowerSeriesRadius : (ℕ → ℝ) → ℝ≥0∞ :=
  fun a => (realPowerSeriesRootGrowth a)⁻¹

theorem real_powerSeries_hasSum_iff :
  ∀ (a : ℕ → ℝ) (c : ℝ) (x S : ℝ),
    RealPowerSeriesHasSum a c x S ↔
      ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N ≥ M,
        |realPowerSeriesPartialSum a c x N - S| < ε := by
  intros
  rfl

theorem real_powerPolynomial_eval :
  ∀ (a : ℕ → ℝ) (c : ℝ) (N : ℕ) (x : ℝ),
    (realPowerPolynomial a c N).eval x = realPowerSeriesPartialSum a c x N := by
  intros
  simp [realPowerPolynomial, realPowerSeriesPartialSum,
    realPartialSum, realPowerSeriesTerm, Polynomial.eval_finsetSum]

theorem real_powerSeries_term_magnitude :
  ∀ (a : ℕ → ℝ) (c : ℝ) (x : ℝ) (n : ℕ),
    |realPowerSeriesTerm a c x n| = |a n| * |x - c| ^ n := by
  intros
  simp only [realPowerSeriesTerm, abs_mul, abs_pow]

theorem real_powerSeries_sum_unique :
  ∀ (a : ℕ → ℝ) (c : ℝ) (x S T : ℝ),
    RealPowerSeriesHasSum a c x S → RealPowerSeriesHasSum a c x T → S = T := by
  intro a c x S T hS hT
  exact real_series_sum_unique (realPowerSeriesTerm a c x) S T hS hT

theorem real_powerSeriesSum_hasSum :
  ∀ (a : ℕ → ℝ) (c : ℝ) (x : { x // x ∈ realPowerSeriesDomain a c }),
    RealPowerSeriesHasSum a c x.val (realPowerSeriesSum a c x) := by
  intro a c x
  exact Classical.choose_spec x.property

theorem real_powerSeriesSum_eq_iff :
  ∀ (a : ℕ → ℝ) (c : ℝ) (x : { x // x ∈ realPowerSeriesDomain a c }) (S : ℝ),
    realPowerSeriesSum a c x = S ↔ RealPowerSeriesHasSum a c x.val S := by
  intro a c x S
  constructor
  · intro h
    rw [← h]
    exact real_powerSeriesSum_hasSum a c x
  · intro h
    exact real_powerSeries_sum_unique a c x.val _ S
      (real_powerSeriesSum_hasSum a c x) h

theorem real_powerSeries_radius_zero_growth :
  ∀ a : ℕ → ℝ, realPowerSeriesRootGrowth a = 0 →
    realPowerSeriesRadius a = ⊤ := by
  intro a h
  simp only [realPowerSeriesRadius, h, ENNReal.inv_zero]

theorem real_powerSeries_radius_infinite_growth :
  ∀ a : ℕ → ℝ, realPowerSeriesRootGrowth a = ⊤ →
    realPowerSeriesRadius a = 0 := by
  intro a h
  simp only [realPowerSeriesRadius, h, ENNReal.inv_top]

def ComplexPowerSeriesCoefficients : Type :=
  ℕ → ℂ

noncomputable def complexPowerSeriesTerm : (ℕ → ℂ) → ℝ → ℂ → ℕ → ℂ :=
  fun a c z n => a n * (z - (c : ℂ)) ^ n

noncomputable def complexPowerSeriesPartialSum : (ℕ → ℂ) → ℝ → ℂ → ℕ → ℂ :=
  fun a c z => complexPartialSum (complexPowerSeriesTerm a c z)

noncomputable def ComplexPowerSeriesHasSum : (ℕ → ℂ) → ℝ → ℂ → ℂ → Prop :=
  fun a c z S => ComplexSeriesHasSum (complexPowerSeriesTerm a c z) S

noncomputable def ComplexPowerSeriesConverges : (ℕ → ℂ) → ℝ → ℂ → Prop :=
  fun a c z => ∃ S : ℂ, ComplexPowerSeriesHasSum a c z S

noncomputable def ComplexPowerSeriesAbsolutelyConverges : (ℕ → ℂ) → ℝ → ℂ → Prop :=
  fun a c z => RealSeriesConverges (fun n => ‖complexPowerSeriesTerm a c z n‖)

noncomputable def complexPowerPolynomial : (ℕ → ℂ) → ℝ → ℕ → Polynomial ℂ :=
  fun a c N => ∑ n ∈ Finset.range (N + 1),
    Polynomial.C (a n) * (Polynomial.X - Polynomial.C (c : ℂ)) ^ n

noncomputable def complexPowerSeriesDomain : (ℕ → ℂ) → ℝ → Set ℂ :=
  fun a c => {z | ComplexPowerSeriesConverges a c z}

noncomputable def complexPowerSeriesSum : (a : ℕ → ℂ) → (c : ℝ) → { z // z ∈ complexPowerSeriesDomain a c } → ℂ :=
  fun _ _ x => Classical.choose x.property

noncomputable def complexPowerSeriesRootGrowth : (ℕ → ℂ) → ℝ≥0∞ :=
  fun a => Filter.limsup (fun n : ℕ =>
    ENNReal.ofReal (nonnegativeRoot (n + 1) (‖a (n + 1)‖))) Filter.atTop

noncomputable def complexPowerSeriesRadius : (ℕ → ℂ) → ℝ≥0∞ :=
  fun a => (complexPowerSeriesRootGrowth a)⁻¹

theorem complex_powerSeries_hasSum_iff :
  ∀ (a : ℕ → ℂ) (c : ℝ) (z S : ℂ),
    ComplexPowerSeriesHasSum a c z S ↔
      ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N ≥ M,
        ‖complexPowerSeriesPartialSum a c z N - S‖ < ε := by
  intros
  rfl

theorem complex_powerPolynomial_eval :
  ∀ (a : ℕ → ℂ) (c : ℝ) (N : ℕ) (z : ℂ),
    (complexPowerPolynomial a c N).eval z = complexPowerSeriesPartialSum a c z N := by
  intros
  simp [complexPowerPolynomial, complexPowerSeriesPartialSum,
    complexPartialSum, complexPowerSeriesTerm, Polynomial.eval_finsetSum]

theorem complex_powerSeries_term_magnitude :
  ∀ (a : ℕ → ℂ) (c : ℝ) (z : ℂ) (n : ℕ),
    ‖complexPowerSeriesTerm a c z n‖ = ‖a n‖ * ‖z - (c : ℂ)‖ ^ n := by
  intros
  simp only [complexPowerSeriesTerm, norm_mul, norm_pow]

theorem complex_powerSeries_sum_unique :
  ∀ (a : ℕ → ℂ) (c : ℝ) (z S T : ℂ),
    ComplexPowerSeriesHasSum a c z S → ComplexPowerSeriesHasSum a c z T → S = T := by
  intro a c z S T hS hT
  exact complex_series_sum_unique (complexPowerSeriesTerm a c z) S T hS hT

theorem complex_powerSeriesSum_hasSum :
  ∀ (a : ℕ → ℂ) (c : ℝ) (z : { z // z ∈ complexPowerSeriesDomain a c }),
    ComplexPowerSeriesHasSum a c z.val (complexPowerSeriesSum a c z) := by
  intro a c z
  exact Classical.choose_spec z.property

theorem complex_powerSeriesSum_eq_iff :
  ∀ (a : ℕ → ℂ) (c : ℝ) (z : { z // z ∈ complexPowerSeriesDomain a c }) (S : ℂ),
    complexPowerSeriesSum a c z = S ↔ ComplexPowerSeriesHasSum a c z.val S := by
  intro a c z S
  constructor
  · intro h
    rw [← h]
    exact complex_powerSeriesSum_hasSum a c z
  · intro h
    exact complex_powerSeries_sum_unique a c z.val _ S
      (complex_powerSeriesSum_hasSum a c z) h

theorem complex_powerSeries_radius_zero_growth :
  ∀ a : ℕ → ℂ, complexPowerSeriesRootGrowth a = 0 →
    complexPowerSeriesRadius a = ⊤ := by
  intro a h
  simp only [complexPowerSeriesRadius, h, ENNReal.inv_zero]

theorem complex_powerSeries_radius_infinite_growth :
  ∀ a : ℕ → ℂ, complexPowerSeriesRootGrowth a = ⊤ →
    complexPowerSeriesRadius a = 0 := by
  intro a h
  simp only [complexPowerSeriesRadius, h, ENNReal.inv_top]

theorem real_powerSeries_term_complex :
  ∀ (a : ℕ → ℝ) (c x : ℝ) (n : ℕ),
    complexPowerSeriesTerm (fun n => (a n : ℂ)) c (x : ℂ) n =
      (realPowerSeriesTerm a c x n : ℂ) := by
  intros
  simp [complexPowerSeriesTerm, realPowerSeriesTerm]

theorem real_powerSeries_partialSum_complex :
  ∀ (a : ℕ → ℝ) (c x : ℝ) (N : ℕ),
    complexPowerSeriesPartialSum (fun n => (a n : ℂ)) c (x : ℂ) N =
      (realPowerSeriesPartialSum a c x N : ℂ) := by
  intros
  simp [complexPowerSeriesPartialSum, realPowerSeriesPartialSum,
    complexPartialSum, realPartialSum, real_powerSeries_term_complex]

theorem real_powerSeries_hasSum_complex_iff :
  ∀ (a : ℕ → ℝ) (c x S : ℝ),
    ComplexPowerSeriesHasSum (fun n => (a n : ℂ)) c (x : ℂ) (S : ℂ) ↔
      RealPowerSeriesHasSum a c x S := by
  intro a c x S
  rw [complex_powerSeries_hasSum_iff, real_powerSeries_hasSum_iff]
  simp only [real_powerSeries_partialSum_complex, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

end SingleVariableAnalysis
