import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.Continuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.LocalBounds
import Mathlib.Tactic.Linarith

/-!
# Local bounds, signs, and nonzero denominators

K03.03.local_bounds (paper.tex:513–521). Continuity with error 1 gives
the upper bound by the triangle inequality. Error ‖f a‖ / 2 and the reverse
triangle inequality give the lower bound. For positive real values the same
error bounds the signed difference directly. All neighborhoods are relative
to E and unpunctured, so the proof also applies at isolated points and endpoints.
-/

namespace SingleVariableAnalysis

universe u v

private theorem norm_local_upper_bound
    {X : Type u} {Y : Type v} [MetricSpace X] [NormedAddCommGroup Y]
    (f : X → Y) (E : Set X) (a : E) (hf : RelativeContinuousAt f E a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → ‖f x‖ ≤ ‖f a‖ + 1 := by
  obtain ⟨δ, hδ, hb⟩ := hf 1 zero_lt_one
  exact ⟨δ, hδ, fun x hx hd => norm_le_norm_add_const_of_dist_le (hb x hx hd).le⟩

private theorem norm_local_lower_bound
    {X : Type u} {Y : Type v} [MetricSpace X] [NormedAddCommGroup Y]
    (f : X → Y) (E : Set X) (a : E) (hf : RelativeContinuousAt f E a)
    (ha : f a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → ‖f a‖ / 2 ≤ ‖f x‖ := by
  obtain ⟨δ, hδ, hb⟩ := hf (‖f a‖ / 2) (half_pos (norm_pos_iff.mpr ha))
  refine ⟨δ, hδ, fun x hx hd => ?_⟩
  have hclose := hb x hx hd
  have hreverse : ‖f a‖ - ‖f x‖ ≤ dist (f x) (f a) := by
    simpa only [dist_eq_norm, norm_sub_rev] using norm_sub_norm_le (f a) (f x)
  linarith

theorem real_local_upper_bound
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : E)
    (hf : RelativeContinuousAt f E a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → |f x| ≤ |f a| + 1 := by
  simpa only [Real.norm_eq_abs] using norm_local_upper_bound f E a hf

theorem complex_local_upper_bound
    {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (a : E)
    (hf : RelativeContinuousAt f E a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → ‖f x‖ ≤ ‖f a‖ + 1 :=
  norm_local_upper_bound f E a hf

theorem real_local_lower_bound
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : E)
    (hf : RelativeContinuousAt f E a) (ha : f a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → |f a| / 2 ≤ |f x| := by
  simpa only [Real.norm_eq_abs] using norm_local_lower_bound f E a hf ha

theorem complex_local_lower_bound
    {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (a : E)
    (hf : RelativeContinuousAt f E a) (ha : f a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → ‖f a‖ / 2 ≤ ‖f x‖ :=
  norm_local_lower_bound f E a hf ha

theorem real_local_positive
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : E)
    (hf : RelativeContinuousAt f E a) (ha : 0 < f a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ →
      f a / 2 < f x ∧ 0 < f a / 2 := by
  obtain ⟨δ, hδ, hb⟩ := (real_relativeContinuousAt_iff f E a).mp hf
    (f a / 2) (half_pos ha)
  refine ⟨δ, hδ, fun x hx hd => ⟨?_, half_pos ha⟩⟩
  have hleft := (abs_lt.mp (hb x hx hd)).1
  linarith

theorem real_local_nonzero
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : E)
    (hf : RelativeContinuousAt f E a) (ha : f a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → f x ≠ 0 := by
  obtain ⟨δ, hδ, hb⟩ := real_local_lower_bound f E a hf ha
  exact ⟨δ, hδ, fun x hx hd =>
    abs_pos.mp ((half_pos (abs_pos.mpr ha)).trans_le (hb x hx hd))⟩

theorem complex_local_nonzero
    {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (a : E)
    (hf : RelativeContinuousAt f E a) (ha : f a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → f x ≠ 0 := by
  obtain ⟨δ, hδ, hb⟩ := complex_local_lower_bound f E a hf ha
  exact ⟨δ, hδ, fun x hx hd =>
    norm_pos_iff.mp ((half_pos (norm_pos_iff.mpr ha)).trans_le (hb x hx hd))⟩

end SingleVariableAnalysis
