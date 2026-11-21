import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.InexactBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace NumAnalysis206.Iterations

/-- Unrolling a nonnegative scalar one-step recurrence. -/
lemma recurrence_convolution_bound (a δ : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ j, a (j + 1) ≤ δ j + q * a j) (n : ℕ) :
    a n ≤ q ^ n * a 0 + ∑ j ∈ Finset.range n, q ^ (n - 1 - j) * δ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : (∑ j ∈ Finset.range (n + 1), q ^ (n + 1 - 1 - j) * δ j) =
        q * (∑ j ∈ Finset.range n, q ^ (n - 1 - j) * δ j) + δ n := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have hexp : n - j = (n - 1 - j) + 1 := by omega
      rw [hexp, pow_succ]
      ring
    calc
      a (n + 1) ≤ δ n + q * a n := hstep n
      _ ≤ δ n + q * (q ^ n * a 0 +
          ∑ j ∈ Finset.range n, q ^ (n - 1 - j) * δ j) :=
        add_le_add (le_refl (δ n)) (mul_le_mul_of_nonneg_left ih hq)
      _ = q ^ (n + 1) * a 0 +
          ∑ j ∈ Finset.range (n + 1), q ^ (n + 1 - 1 - j) * δ j := by
        rw [hsum, pow_succ]
        ring

/-- The metric triangle inequality gives the scalar recurrence on the domain. -/
lemma inexact_distance_step {X : Type*} [MetricSpace X]
    (D : Set X) (T : X → X) (q : ℝ) (p : X) (x : ℕ → X) (δ : ℕ → ℝ)
    (hcontract : ∀ u ∈ D, ∀ v ∈ D, dist (T u) (T v) ≤ q * dist u v)
    (hp : p ∈ D) (hfix : T p = p) (hx : ∀ j, x j ∈ D)
    (herror : ∀ j, dist (x (j + 1)) (T (x j)) ≤ δ j) (j : ℕ) :
    dist (x (j + 1)) p ≤ δ j + q * dist (x j) p := by
  calc
    dist (x (j + 1)) p ≤
        dist (x (j + 1)) (T (x j)) + dist (T (x j)) p := dist_triangle _ _ _
    _ ≤ δ j + q * dist (x j) p :=
      add_le_add (herror j) (by simpa only [hfix] using hcontract (x j) (hx j) p hp)

/-- W71: the finite convolution estimate. -/
theorem inexact_convolution_bound :
    Specs.NumAnalysis206.Iterations.InexactConvolutionBound := by
  intro X inst D T q p x δ hq _hq1 _hTD hcontract hp hfix hx herror n
  exact recurrence_convolution_bound (fun j => dist (x j) p) δ q hq
    (inexact_distance_step D T q p x δ hcontract hp hfix hx herror) n

/-- W71: the finite bound under a common step-error upper bound. -/
theorem inexact_common_bound :
    Specs.NumAnalysis206.Iterations.InexactCommonBound := by
  intro X inst D T q p x δ ε hq hq1 _hTD hcontract hp hfix hx herror hcommon n
  have hden : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  have hstep := inexact_distance_step D T q p x δ hcontract hp hfix hx herror
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      dist (x (n + 1)) p ≤ δ n + q * dist (x n) p := hstep n
      _ ≤ ε + q * (q ^ n * dist (x 0) p + ε * (1 - q ^ n) / (1 - q)) :=
        add_le_add (hcommon n) (mul_le_mul_of_nonneg_left ih hq)
      _ = q ^ (n + 1) * dist (x 0) p + ε * (1 - q ^ (n + 1)) / (1 - q) := by
        rw [pow_succ]
        field_simp [hden]
        ring

end NumAnalysis206.Iterations
