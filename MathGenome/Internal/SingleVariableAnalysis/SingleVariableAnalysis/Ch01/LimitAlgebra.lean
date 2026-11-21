import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.UniqueLimit
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.LimitAlgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Algebra and order of finite scalar sequence limits

The upstream epsilon/filter bridges identify precisely the manuscript's
limits. We use continuity of addition, scalar multiplication, multiplication,
and norm, and continuity of inversion at a nonzero scalar. The denominator
bound and eventual nonvanishing require only a nonzero limit, allowing
arbitrary zeros in the finite prefix. Closedness of the real order passes
an eventual weak inequality to the limits. The positive reciprocal sequence
and the constant zero sequence exhibit failure for strict inequalities.

Library proof provenance: Mathlib's topological algebra and norm continuity
APIs, and its natural-number reciprocal limit. No analytic result of later
project chapters is imported.
-/

namespace SingleVariableAnalysis

open scoped Topology

theorem real_add (u v : ℕ → ℝ) (a b : ℝ) (hu : RealSequenceConverges u a) (hv : RealSequenceConverges v b) :
    RealSequenceConverges (fun n => u n + v n) (a + b) := by
  exact (realSequenceConverges_iff _ _).mpr (((realSequenceConverges_iff _ _).mp hu).add ((realSequenceConverges_iff _ _).mp hv))

theorem real_mul (u v : ℕ → ℝ) (a b : ℝ) (hu : RealSequenceConverges u a) (hv : RealSequenceConverges v b) :
    RealSequenceConverges (fun n => u n * v n) (a * b) := by
  exact (realSequenceConverges_iff _ _).mpr (((realSequenceConverges_iff _ _).mp hu).mul ((realSequenceConverges_iff _ _).mp hv))

theorem real_const_mul (u : ℕ → ℝ) (a : ℝ) (hu : RealSequenceConverges u a) (c : ℝ) :
    RealSequenceConverges (fun n => c * u n) (c * a) := by
  exact (realSequenceConverges_iff _ _).mpr (Filter.Tendsto.const_mul c ((realSequenceConverges_iff _ _).mp hu))

theorem real_linear_combination (u v : ℕ → ℝ) (a b : ℝ) (hu : RealSequenceConverges u a) (hv : RealSequenceConverges v b) (c d : ℝ) :
    RealSequenceConverges (fun n => c * u n + d * v n) (c * a + d * b) := by
  exact real_add _ _ _ _ (real_const_mul u a hu c) (real_const_mul v b hv d)

theorem real_abs (u : ℕ → ℝ) (a : ℝ) (hu : RealSequenceConverges u a) :
    RealSequenceConverges (fun n => |u n|) |a| := by
  apply (realSequenceConverges_iff _ _).mpr
  simpa only [Real.norm_eq_abs] using ((realSequenceConverges_iff _ _).mp hu).norm

theorem real_eventually_ne_zero (u : ℕ → ℝ) (a : ℝ) (hu : RealSequenceConverges u a) (ha : a ≠ 0) :
    SequenceEventually (fun n => u n ≠ 0) := by
  exact (sequenceEventually_iff _).mpr (((realSequenceConverges_iff _ _).mp hu).eventually_ne ha)

theorem real_denominator_bound (u : ℕ → ℝ) (a : ℝ) (hu : RealSequenceConverges u a) (ha : a ≠ 0) :
    SequenceEventually (fun n => |a| / 2 ≤ |u n|) := by
  have hnorm := ((realSequenceConverges_iff _ _).mp hu).norm
  simp only [Real.norm_eq_abs] at hnorm
  have hpos : 0 < |a| := abs_pos.mpr ha
  exact (sequenceEventually_iff _).mpr
    ((hnorm.eventually_const_lt (half_lt_self hpos)).mono fun _ h => h.le)

theorem real_inv (u : ℕ → ℝ) (a : ℝ) (hu : RealSequenceConverges u a) (ha : a ≠ 0) :
    RealSequenceConverges (fun n => (u n)⁻¹) a⁻¹ := by
  exact (realSequenceConverges_iff _ _).mpr (((realSequenceConverges_iff _ _).mp hu).inv₀ ha)

theorem real_div (u v : ℕ → ℝ) (a b : ℝ) (hu : RealSequenceConverges u a) (hv : RealSequenceConverges v b) (hb : b ≠ 0) :
    RealSequenceConverges (fun n => u n / v n) (a / b) := by
  exact (realSequenceConverges_iff _ _).mpr (((realSequenceConverges_iff _ _).mp hu).div ((realSequenceConverges_iff _ _).mp hv) hb)

theorem complex_add (u v : ℕ → ℂ) (a b : ℂ) (hu : ComplexSequenceConverges u a) (hv : ComplexSequenceConverges v b) :
    ComplexSequenceConverges (fun n => u n + v n) (a + b) := by
  exact (complexSequenceConverges_iff _ _).mpr (((complexSequenceConverges_iff _ _).mp hu).add ((complexSequenceConverges_iff _ _).mp hv))

theorem complex_mul (u v : ℕ → ℂ) (a b : ℂ) (hu : ComplexSequenceConverges u a) (hv : ComplexSequenceConverges v b) :
    ComplexSequenceConverges (fun n => u n * v n) (a * b) := by
  exact (complexSequenceConverges_iff _ _).mpr (((complexSequenceConverges_iff _ _).mp hu).mul ((complexSequenceConverges_iff _ _).mp hv))

theorem complex_const_mul (u : ℕ → ℂ) (a : ℂ) (hu : ComplexSequenceConverges u a) (c : ℂ) :
    ComplexSequenceConverges (fun n => c * u n) (c * a) := by
  exact (complexSequenceConverges_iff _ _).mpr (Filter.Tendsto.const_mul c ((complexSequenceConverges_iff _ _).mp hu))

theorem complex_linear_combination (u v : ℕ → ℂ) (a b : ℂ) (hu : ComplexSequenceConverges u a) (hv : ComplexSequenceConverges v b) (c d : ℂ) :
    ComplexSequenceConverges (fun n => c * u n + d * v n) (c * a + d * b) := by
  exact complex_add _ _ _ _ (complex_const_mul u a hu c) (complex_const_mul v b hv d)

theorem complex_norm (u : ℕ → ℂ) (a : ℂ) (hu : ComplexSequenceConverges u a) :
    RealSequenceConverges (fun n => ‖u n‖) ‖a‖ := by
  exact (realSequenceConverges_iff _ _).mpr (((complexSequenceConverges_iff _ _).mp hu).norm)

theorem complex_eventually_ne_zero (u : ℕ → ℂ) (a : ℂ) (hu : ComplexSequenceConverges u a) (ha : a ≠ 0) :
    SequenceEventually (fun n => u n ≠ 0) := by
  exact (sequenceEventually_iff _).mpr (((complexSequenceConverges_iff _ _).mp hu).eventually_ne ha)

theorem complex_denominator_bound (u : ℕ → ℂ) (a : ℂ) (hu : ComplexSequenceConverges u a) (ha : a ≠ 0) :
    SequenceEventually (fun n => ‖a‖ / 2 ≤ ‖u n‖) := by
  have hnorm := ((complexSequenceConverges_iff _ _).mp hu).norm
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  exact (sequenceEventually_iff _).mpr
    ((hnorm.eventually_const_lt (half_lt_self hpos)).mono fun _ h => h.le)

theorem complex_inv (u : ℕ → ℂ) (a : ℂ) (hu : ComplexSequenceConverges u a) (ha : a ≠ 0) :
    ComplexSequenceConverges (fun n => (u n)⁻¹) a⁻¹ := by
  exact (complexSequenceConverges_iff _ _).mpr (((complexSequenceConverges_iff _ _).mp hu).inv₀ ha)

theorem complex_div (u v : ℕ → ℂ) (a b : ℂ) (hu : ComplexSequenceConverges u a) (hv : ComplexSequenceConverges v b) (hb : b ≠ 0) :
    ComplexSequenceConverges (fun n => u n / v n) (a / b) := by
  exact (complexSequenceConverges_iff _ _).mpr (((complexSequenceConverges_iff _ _).mp hu).div ((complexSequenceConverges_iff _ _).mp hv) hb)

theorem real_limit_le_of_eventually_le (u v : ℕ → ℝ) (a b : ℝ)
    (hu : RealSequenceConverges u a) (hv : RealSequenceConverges v b)
    (hle : SequenceEventually (fun n => u n ≤ v n)) : a ≤ b := by
  exact le_of_tendsto_of_tendsto ((realSequenceConverges_iff _ _).mp hu)
    ((realSequenceConverges_iff _ _).mp hv) ((sequenceEventually_iff _).mp hle)

/-- Strict inequalities between all terms need not give strict inequalities of limits. -/
theorem real_strict_order_counterexample :
    (∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1)) ∧
      RealSequenceConverges (fun _ => 0) 0 ∧
      RealSequenceConverges (fun n => 1 / ((n : ℝ) + 1)) 0 ∧
      ¬ (0 : ℝ) < 0 := by
  refine ⟨fun n => one_div_pos.mpr (by positivity), ?_, ?_, lt_irrefl 0⟩
  · exact (realSequenceConverges_iff _ _).mpr tendsto_const_nhds
  · exact (realSequenceConverges_iff _ _).mpr tendsto_one_div_add_atTop_nhds_zero_nat

end SingleVariableAnalysis
