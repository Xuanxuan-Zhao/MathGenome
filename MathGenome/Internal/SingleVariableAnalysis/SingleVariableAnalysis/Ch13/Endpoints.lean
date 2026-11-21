import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Radius
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Alternating
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Endpoints

/-!
# Independent endpoint behavior of three power series

K03.13.endpoints. The radius is the upstream reciprocal coefficient-root
limsup in ℝ≥0∞. The two reciprocal root limits were proved in Chapter 11
by finite power algebra and integer-root estimates. Reciprocal-square
convergence there is proved by condensation. Endpoint conclusions here
use ordinary partial sums, not unconditional summability.
-/
noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped ENNReal Topology

/-- A coefficient-root limit of one gives the canonical radius one. -/
theorem powerSeries_radius_one_of_root_limit (a : ℕ → ℝ)
    (h : RealSequenceConverges
      (fun n => nonnegativeRoot (n+1) |a (n+1)|) 1) :
    realPowerSeriesRadius a = 1 := by
  have hg := (ENNReal.tendsto_ofReal ((realSequenceConverges_iff _ _).mp h)).limsup_eq
  change (realPowerSeriesRootGrowth a)⁻¹ = 1
  have he : realPowerSeriesRootGrowth a = 1 := by simpa [realPowerSeriesRootGrowth] using hg
  rw [he, inv_one]

theorem geometric_powerSeries_radius : realPowerSeriesRadius (fun _ => 1) = 1 := by
  apply powerSeries_radius_one_of_root_limit
  have hr (n : ℕ) : nonnegativeRoot (n+1) 1 = 1 := by
    exact (nonnegativeRoot_unique (n+1) (Nat.succ_pos n) 1 zero_le_one
      1 zero_le_one (one_pow _)).symm
  simpa [hr] using
    (show RealSequenceConverges (fun _ : ℕ => (1 : ℝ)) 1 from
      (realSequenceConverges_iff _ _).mpr tendsto_const_nhds)

theorem harmonic_powerSeries_radius :
    realPowerSeriesRadius (fun n => 1 / (n : ℝ)) = 1 :=
  powerSeries_radius_one_of_root_limit _ harmonic_root_limit

theorem reciprocal_square_powerSeries_radius :
    realPowerSeriesRadius (fun n => 1 / (n : ℝ)^2) = 1 :=
  powerSeries_radius_one_of_root_limit _ reciprocal_square_root_limit

theorem reflected_harmonic_powerSeries_radius :
    realPowerSeriesRadius (fun n => (-1 : ℝ)^n / (n : ℝ)) = 1 := by
  apply powerSeries_radius_one_of_root_limit
  simpa only [abs_div, abs_pow, abs_neg, abs_one, one_pow] using harmonic_root_limit

/-- The reciprocal coefficients start at degree one, with a zero constant.
The shifted alternating harmonic series differs by the scalar -1. -/
theorem alternating_harmonic_from_one_converges :
    RealSeriesConverges (fun n => (-1 : ℝ)^n / (n : ℝ)) := by
  apply real_series_converges_of_shift
  obtain ⟨S, hS⟩ := alternating_harmonic_conditional.1
  refine ⟨(-1) * S, ?_⟩
  have h := real_series_const_mul _ S hS (-1)
  simpa only [pow_succ, Nat.cast_add, Nat.cast_one, mul_neg_one, neg_mul,
    neg_div, one_mul] using h

/-- Substitution by -x is represented by multiplying the nth coefficient
by (-1)^n, at every real argument and every degree. -/
theorem reflected_harmonic_term (x : ℝ) (n : ℕ) :
    realPowerSeriesTerm (fun n => (-1 : ℝ)^n / (n : ℝ)) 0 x n =
    realPowerSeriesTerm (fun n => 1 / (n : ℝ)) 0 (-x) n := by
  change ((-1 : ℝ)^n / (n : ℝ)) * (x - 0)^n =
    (1 / (n : ℝ)) * (-x - 0)^n
  simp only [sub_zero]
  rw [neg_pow]
  ring

theorem geometric_powerSeries_endpoints :
    ¬ RealPowerSeriesConverges (fun _ => 1) 0 (-1) ∧
    ¬ RealPowerSeriesConverges (fun _ => 1) 0 1 := by
  change ¬ RealSeriesConverges (fun n => 1 * ((-1 : ℝ) - 0)^n) ∧
    ¬ RealSeriesConverges (fun n => 1 * ((1 : ℝ) - 0)^n)
  constructor
  · simpa only [RealSeriesDiverges, sub_zero, one_mul] using
      real_geometric_series_diverges (-1 : ℝ) (by norm_num)
  · simpa only [RealSeriesDiverges, sub_zero, one_mul] using
      real_geometric_series_diverges (1 : ℝ) (by norm_num)

theorem harmonic_powerSeries_endpoints :
    RealPowerSeriesConverges (fun n => 1 / (n : ℝ)) 0 (-1) ∧
    ¬ RealPowerSeriesConverges (fun n => 1 / (n : ℝ)) 0 1 ∧
    ¬ RealPowerSeriesAbsolutelyConverges (fun n => 1 / (n : ℝ)) 0 (-1) := by
  change RealSeriesConverges (fun n => 1 / (n : ℝ) * ((-1 : ℝ) - 0)^n) ∧
    ¬ RealSeriesConverges (fun n => 1 / (n : ℝ) * ((1 : ℝ) - 0)^n) ∧
    ¬ RealSeriesConverges (fun n => |1 / (n : ℝ) * ((-1 : ℝ) - 0)^n|)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [sub_zero, one_div_mul_eq_div, mul_one] using
      alternating_harmonic_from_one_converges
  · simpa only [RealSeriesDiverges, sub_zero, one_pow, mul_one] using
      harmonic_series_diverges
  · simpa only [RealSeriesDiverges, sub_zero, abs_mul, abs_div, abs_pow, abs_neg, abs_one,
      one_pow, mul_one, Nat.abs_cast] using harmonic_series_diverges

theorem reciprocal_square_powerSeries_endpoints :
    RealPowerSeriesAbsolutelyConverges (fun n => 1 / (n : ℝ)^2) 0 (-1) ∧
    RealPowerSeriesAbsolutelyConverges (fun n => 1 / (n : ℝ)^2) 0 1 := by
  change RealSeriesConverges (fun n => |1 / (n : ℝ)^2 * ((-1 : ℝ) - 0)^n|) ∧
    RealSeriesConverges (fun n => |1 / (n : ℝ)^2 * ((1 : ℝ) - 0)^n|)
  constructor <;>
    simpa only [RealSeriesAbsolutelyConverges, sub_zero, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, mul_one] using reciprocal_square_series_absolute

theorem reflected_harmonic_powerSeries_endpoints :
    RealPowerSeriesConverges (fun n => (-1 : ℝ)^n / (n : ℝ)) 0 1 ∧
    ¬ RealPowerSeriesConverges (fun n => (-1 : ℝ)^n / (n : ℝ)) 0 (-1) ∧
    ¬ RealPowerSeriesAbsolutelyConverges
      (fun n => (-1 : ℝ)^n / (n : ℝ)) 0 1 := by
  have he (x : ℝ) :
      realPowerSeriesTerm (fun n => (-1 : ℝ)^n / (n : ℝ)) 0 x =
      realPowerSeriesTerm (fun n => 1 / (n : ℝ)) 0 (-x) := by
    funext n
    exact reflected_harmonic_term x n
  change RealSeriesConverges _ ∧ ¬ RealSeriesConverges _ ∧ ¬ RealSeriesConverges _
  simp_rw [he]
  have hh := harmonic_powerSeries_endpoints
  change RealSeriesConverges (realPowerSeriesTerm (fun n => 1 / (n : ℝ)) 0 (-1)) ∧
    ¬ RealSeriesConverges (realPowerSeriesTerm (fun n => 1 / (n : ℝ)) 0 1) ∧
    ¬ RealSeriesConverges
      (fun n => |realPowerSeriesTerm (fun n => 1 / (n : ℝ)) 0 (-1) n|) at hh
  simpa only [neg_neg] using hh

end SingleVariableAnalysis
