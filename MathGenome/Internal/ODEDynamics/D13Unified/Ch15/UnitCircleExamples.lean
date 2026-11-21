import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.DiscreteDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.UnitCircleExamples
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace D13Unified.Ch15.UnitCircleExamples
open Filter Function Set
open scoped Topology
open D13Unified.Ch15.DiscreteDefinitions

abbrev minus : Specs.D13Unified.Ch15.UnitCircleExamples.ScalarMapType :=
  Specs.D13Unified.Ch15.UnitCircleExamples.minus
abbrev plus : Specs.D13Unified.Ch15.UnitCircleExamples.ScalarMapType :=
  Specs.D13Unified.Ch15.UnitCircleExamples.plus

theorem minus_fixed : minus 0 = 0 := by norm_num [minus, Specs.D13Unified.Ch15.UnitCircleExamples.minus]
theorem plus_fixed : plus 0 = 0 := by norm_num [plus, Specs.D13Unified.Ch15.UnitCircleExamples.plus]

theorem minus_derivative : HasDerivAt minus 1 0 := by
  change HasDerivAt (fun x : ℝ => x - x ^ 3) 1 0
  convert (hasDerivAt_id (0 : ℝ)).sub ((hasDerivAt_id (0 : ℝ)).pow 3) using 1 <;> norm_num
  funext x
  rfl

theorem plus_derivative : HasDerivAt plus 1 0 := by
  change HasDerivAt (fun x : ℝ => x + x ^ 3) 1 0
  convert (hasDerivAt_id (0 : ℝ)).add ((hasDerivAt_id (0 : ℝ)).pow 3) using 1 <;> norm_num
  funext x
  rfl

theorem minus_continuous : Continuous minus := by
  change Continuous (fun x : ℝ => x - x ^ 3)
  exact continuous_id.sub (continuous_id.pow 3)

theorem plus_continuous : Continuous plus := by
  change Continuous (fun x : ℝ => x + x ^ 3)
  exact continuous_id.add (continuous_id.pow 3)

private theorem minus_formula (x : ℝ) : minus x = x * (1 - x ^ 2) := by
  dsimp [minus, Specs.D13Unified.Ch15.UnitCircleExamples.minus]
  ring

private theorem plus_formula (x : ℝ) : plus x = x * (1 + x ^ 2) := by
  dsimp [plus, Specs.D13Unified.Ch15.UnitCircleExamples.plus]
  ring

private theorem minus_abs (x : ℝ) (hx : |x| ≤ 1) : |minus x| = |x| - |x| ^ 3 := by
  have hs : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  rw [minus_formula, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - x ^ 2)]
  rw [← sq_abs x]
  ring

private theorem plus_abs (x : ℝ) : |plus x| = |x| + |x| ^ 3 := by
  rw [plus_formula, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + x ^ 2)]
  rw [← sq_abs x]
  ring

theorem minus_abs_decreases (x : ℝ) (hpos : 0 < |x|) (hx : |x| < 1) :
    |minus x| < |x| := by
  rw [minus_abs x hx.le]
  have : 0 < |x| ^ 3 := pow_pos hpos 3
  linarith

private theorem minus_abs_le (x : ℝ) (hx : |x| < 1) : |minus x| ≤ |x| := by
  rw [minus_abs x hx.le]
  have : 0 ≤ |x| ^ 3 := by positivity
  linarith

private theorem minus_orbit_bound (x : ℝ) (hx : |x| < 1) (n : ℕ) :
    |minus^[n] x| ≤ |x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (minus_abs_le _ (lt_of_le_of_lt ih hx)).trans ih

private theorem minus_orbit_abs_step (x : ℝ) (hx : |x| < 1) (n : ℕ) :
    |minus^[n+1] x| = |minus^[n] x| - |minus^[n] x| ^ 3 := by
  rw [Function.iterate_succ_apply', minus_abs _ ((minus_orbit_bound x hx n).trans hx.le)]

/-- Monotone convergence followed by passage to the polynomial recurrence. -/
theorem minus_converges (x : ℝ) (hx : |x| < 1) :
    Tendsto (fun n : ℕ => minus^[n] x) atTop (𝓝 0) := by
  let u : ℕ → ℝ := fun n => |minus^[n] x|
  have hstep (n : ℕ) : u (n+1) = u n - u n ^ 3 := minus_orbit_abs_step x hx n
  have hanti : Antitone u := antitone_nat_of_succ_le (fun n => by
    rw [hstep n]
    have : 0 ≤ u n ^ 3 := pow_nonneg (abs_nonneg _) _
    linarith)
  have hbdd : BddBelow (range u) := ⟨0, by rintro y ⟨n, rfl⟩; exact abs_nonneg _⟩
  have ht := tendsto_atTop_ciInf hanti hbdd
  have hshift : Tendsto (fun n => u (n+1)) atTop (𝓝 (⨅ n, u n)) :=
    (tendsto_add_atTop_iff_nat 1).2 ht
  have hrec : Tendsto (fun n => u (n+1)) atTop
      (𝓝 ((⨅ n, u n) - (⨅ n, u n) ^ 3)) := by
    simpa only [hstep] using ht.sub (ht.pow 3)
  have heq := tendsto_nhds_unique hshift hrec
  have hz : (⨅ n, u n) = 0 := by
    have : (⨅ n, u n) ^ 3 = 0 := by linarith
    exact (eq_zero_of_pow_eq_zero this)
  have hu : Tendsto u atTop (𝓝 0) := hz ▸ ht
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [u, Real.norm_eq_abs] using hu)

theorem minus_stable : LyapunovStable minus 0 := by
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro x hx n
  simp only [Real.dist_eq, sub_zero] at hx ⊢
  exact lt_of_le_of_lt (minus_orbit_bound x (lt_of_lt_of_le hx (min_le_right _ _)) n)
    (lt_of_lt_of_le hx (min_le_left _ _))

theorem minus_asymptotically_stable : AsymptoticallyStable minus 0 := by
  refine ⟨minus_stable, 1, zero_lt_one, ?_⟩
  intro x hx
  exact minus_converges x (by simpa [Real.dist_eq] using hx)

theorem plus_abs_increases (x : ℝ) (hx : x ≠ 0) : |x| < |plus x| := by
  rw [plus_abs]
  have : 0 < |x| ^ 3 := pow_pos (abs_pos.mpr hx) 3
  linarith

private theorem plus_orbit_abs_step (x : ℝ) (n : ℕ) :
    |plus^[n+1] x| = |plus^[n] x| + |plus^[n] x| ^ 3 := by
  rw [Function.iterate_succ_apply', plus_abs]

private theorem plus_orbit_mono (x : ℝ) : Monotone (fun n : ℕ => |plus^[n] x|) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [plus_orbit_abs_step]
  have : 0 ≤ |plus^[n] x| ^ 3 := by positivity
  linarith

theorem plus_abs_iterates_strictMono (x : ℝ) (hx : x ≠ 0) :
    StrictMono (fun n : ℕ => |plus^[n] x|) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [plus_orbit_abs_step]
  have hp : 0 < |plus^[n] x| := lt_of_lt_of_le (abs_pos.mpr hx)
    (by simpa using plus_orbit_mono x (Nat.zero_le n))
  have : 0 < |plus^[n] x| ^ 3 := pow_pos hp 3
  linarith

theorem plus_escape (r : ℝ) (_hr : 0 < r) (x : ℝ) (hx : x ≠ 0) :
    ∃ n : ℕ, r ≤ |plus^[n] x| := by
  by_contra h
  push Not at h
  let u : ℕ → ℝ := fun n => |plus^[n] x|
  have hbdd : BddAbove (range u) := ⟨r, by rintro y ⟨n, rfl⟩; exact (h n).le⟩
  have ht := tendsto_atTop_ciSup (plus_orbit_mono x) hbdd
  have hshift : Tendsto (fun n => u (n+1)) atTop (𝓝 (⨆ n, u n)) :=
    (tendsto_add_atTop_iff_nat 1).2 ht
  have hrec : Tendsto (fun n => u (n+1)) atTop
      (𝓝 ((⨆ n, u n) + (⨆ n, u n) ^ 3)) := by
    simpa only [u, plus_orbit_abs_step] using ht.add (ht.pow 3)
  have heq := tendsto_nhds_unique hshift hrec
  have hz : (⨆ n, u n) = 0 := by
    have : (⨆ n, u n) ^ 3 = 0 := by linarith
    exact eq_zero_of_pow_eq_zero this
  have hle : |x| ≤ (⨆ n, u n) := by simpa [u] using le_ciSup hbdd 0
  have : 0 < |x| := abs_pos.mpr hx
  linarith

theorem plus_first_exit (r : ℝ) (hr : 0 < r) (x : ℝ) (hx : 0 < |x|) (hxr : |x| < r) :
    ∃ N : ℕ, 0 < N ∧ r ≤ |plus^[N] x| ∧ ∀ n : ℕ, n < N → |plus^[n] x| < r := by
  have hex := plus_escape r hr x (abs_pos.mp hx)
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · by_contra hn
    have hz : Nat.find hex = 0 := Nat.eq_zero_of_not_pos hn
    have := Nat.find_spec hex
    rw [hz] at this
    simpa using (not_le.mpr hxr) this
  · intro n hn
    exact lt_of_not_ge (Nat.find_min hex hn)

theorem plus_unstable : ¬ LyapunovStable plus 0 := by
  intro hstable
  obtain ⟨δ, hδ, hb⟩ := hstable 1 zero_lt_one
  obtain ⟨n, hn⟩ := plus_escape 1 zero_lt_one (δ / 2) (by linarith)
  have hsmall : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  have := hb (δ / 2) hsmall n
  simp only [Real.dist_eq, sub_zero] at this
  linarith

end D13Unified.Ch15.UnitCircleExamples
