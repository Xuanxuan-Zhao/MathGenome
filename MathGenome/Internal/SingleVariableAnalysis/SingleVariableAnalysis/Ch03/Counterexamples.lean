import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.UniformContinuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Counterexamples
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Separating continuity conditions

K03.03.counterexamples (paper.tex:627–634). The two failures of uniform
continuity use exactly the manuscript's pairs, indexed from one. In applying
the sequential obstruction we shift the index by one to obtain sequences
defined on all naturals whose terms all lie in the required domain.
The square-root estimate is algebraic; its epsilon–delta consequence uses
δ = ε². Its failure of a local Lipschitz bound is witnessed by a sufficiently
small positive square. No derivatives are needed.
-/
namespace SingleVariableAnalysis

open scoped Topology

theorem reciprocal_continuous :
    RelativeContinuous (fun x : ℝ => 1 / x) (Set.Ioo 0 1) := by
  intro a ha
  apply (relativeContinuousAt_within_iff _ _ _).mpr
  exact (continuousAt_const.div continuousAt_id (ne_of_gt ha.1)).continuousWithinAt

theorem reciprocal_unbounded :
    ∀ B : ℝ, ∃ x ∈ Set.Ioo (0 : ℝ) 1, B < |1 / x| := by
  intro B
  obtain ⟨n, hn, hB⟩ := archimedean_bound (max B 1)
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  refine ⟨1 / ((n : ℝ) + 1), ⟨by positivity, ?_⟩, ?_⟩
  · exact (div_lt_one (by positivity)).mpr (by linarith)
  · simpa only [one_div_one_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
      using (lt_add_of_lt_of_pos ((le_max_left B 1).trans_lt hB) zero_lt_one)

theorem reciprocal_pair_values (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ∈ Set.Ioo (0 : ℝ) 1 ∧
    1 / ((n : ℝ) + 2) ∈ Set.Ioo (0 : ℝ) 1 ∧
    dist (1 / (1 / ((n : ℝ) + 1))) (1 / (1 / ((n : ℝ) + 2))) = 1 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  refine ⟨⟨by positivity, (div_lt_one (by positivity)).mpr (by linarith)⟩,
    ⟨by positivity, (div_lt_one (by positivity)).mpr (by linarith)⟩, ?_⟩
  simp only [one_div_one_div, Real.dist_eq]
  have heq : (n : ℝ) + 1 - ((n : ℝ) + 2) = -1 := by ring
  rw [heq]
  norm_num

theorem reciprocal_pair_distance_limit :
    Filter.Tendsto
      (fun n : ℕ => dist (1 / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 2)))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have h (k : ℕ) : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + (k : ℝ)))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Nat.cast_add] using
      reciprocal_limit.comp (Filter.tendsto_add_atTop_nat k)
  simpa only [Real.dist_eq, sub_self, abs_zero, Nat.cast_one, Nat.cast_ofNat] using ((h 1).sub (h 2)).abs

theorem reciprocal_not_uniformContinuous :
    ¬ RelativeUniformContinuous (fun x : ℝ => 1 / x) (Set.Ioo 0 1) := by
  apply (relativeUniformContinuous_failure_iff _ _).mpr
  refine ⟨1, zero_lt_one,
    (fun n => 1 / (((n + 1 : ℕ) : ℝ) + 1)),
    (fun n => 1 / (((n + 1 : ℕ) : ℝ) + 2)),
    (fun n => (reciprocal_pair_values (n + 1) (by omega)).1),
    (fun n => (reciprocal_pair_values (n + 1) (by omega)).2.1),
    reciprocal_pair_distance_limit.comp (Filter.tendsto_add_atTop_nat 1), ?_⟩
  intro n
  exact (reciprocal_pair_values (n + 1) (by omega)).2.2.ge

theorem square_continuous : RelativeContinuous (fun x : ℝ => x ^ 2) Set.univ := by
  intro a _
  apply (relativeContinuousAt_within_iff _ _ _).mpr
  exact (continuous_id.pow 2).continuousAt.continuousWithinAt

theorem square_pair_values (n : ℕ) (hn : 1 ≤ n) :
    dist (n : ℝ) ((n : ℝ) + 1 / (n : ℝ)) = 1 / (n : ℝ) ∧
    dist ((n : ℝ) ^ 2) (((n : ℝ) + 1 / (n : ℝ)) ^ 2) =
      2 + 1 / (n : ℝ) ^ 2 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  constructor
  · rw [Real.dist_eq, show (n : ℝ) - ((n : ℝ) + 1 / (n : ℝ)) =
      -(1 / (n : ℝ)) by ring, abs_neg, abs_of_pos (by positivity)]
  · have heq : (n : ℝ) ^ 2 - ((n : ℝ) + 1 / (n : ℝ)) ^ 2 =
        -(2 + 1 / (n : ℝ) ^ 2) := by
      field_simp
      ring
    rw [Real.dist_eq, heq, abs_neg, abs_of_pos (by positivity)]

theorem square_pair_distance_limit :
    Filter.Tendsto (fun n : ℕ => dist (n : ℝ) ((n : ℝ) + 1 / (n : ℝ)))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have heq (n : ℕ) : dist (n : ℝ) ((n : ℝ) + 1 / (n : ℝ)) = 1 / (n : ℝ) := by
    rw [Real.dist_eq, show (n : ℝ) - ((n : ℝ) + 1 / (n : ℝ)) =
      -(1 / (n : ℝ)) by ring, abs_neg, abs_of_nonneg (by positivity)]
  simpa only [heq] using reciprocal_limit

theorem square_not_uniformContinuous :
    ¬ RelativeUniformContinuous (fun x : ℝ => x ^ 2) Set.univ := by
  apply (relativeUniformContinuous_failure_iff _ _).mpr
  refine ⟨2, by norm_num, (fun n => ((n + 1 : ℕ) : ℝ)),
    (fun n => ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ)),
    (fun _ => Set.mem_univ _), (fun _ => Set.mem_univ _),
    square_pair_distance_limit.comp (Filter.tendsto_add_atTop_nat 1), ?_⟩
  intro n
  rw [(square_pair_values (n + 1) (by omega)).2]
  exact le_add_of_nonneg_right (by positivity)

theorem sqrt_difference_sq_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ^ 2 ≤ |x - y| := by
  have h (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a) :
      (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a - b := by
    have hs := Real.sqrt_le_sqrt hab
    have hp := mul_nonneg (Real.sqrt_nonneg b) (sub_nonneg.mpr hs)
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
  rcases le_total y x with hxy | hxy
  · rw [sq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact h x y hx hy hxy
  · rw [abs_sub_comm (Real.sqrt x), abs_sub_comm x]
    rw [sq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact h y x hy hx hxy

theorem sqrt_uniformContinuous :
    RelativeUniformContinuous Real.sqrt (Set.Icc (0 : ℝ) 1) := by
  intro ε hε
  refine ⟨ε ^ 2, sq_pos_of_pos hε, ?_⟩
  intro x hx y hy hdist
  have he := sqrt_difference_sq_le x y hx.1 hy.1
  rw [Real.dist_eq] at hdist ⊢
  have hs := he.trans_lt hdist
  nlinarith [abs_nonneg (Real.sqrt x - Real.sqrt y)]

theorem sqrt_not_lipschitz_at_zero :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, x < r →
        |Real.sqrt x - Real.sqrt 0| ≤ C * |x - 0| := by
  rintro ⟨C, hC, r, hr, hbound⟩
  let t : ℝ := min (1 / 2) (min (r / 2) (1 / (2 * (C + 1))))
  have ht : 0 < t := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htr : t ≤ r / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have htC : t ≤ 1 / (2 * (C + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have htC' : t * (2 * (C + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp htC
  have hCt : C * t < 1 := by nlinarith
  have hb := hbound (t ^ 2) ⟨sq_nonneg _, by nlinarith⟩ (by nlinarith)
  rw [Real.sqrt_sq ht.le, Real.sqrt_zero, sub_zero, sub_zero,
    abs_of_pos ht, abs_of_nonneg (sq_nonneg t)] at hb
  have hlt := mul_lt_mul_of_pos_right hCt ht
  nlinarith

theorem sqrt_not_lipschitz :
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |Real.sqrt x - Real.sqrt y| ≤ C * |x - y| := by
  rintro ⟨C, hC, hb⟩
  apply sqrt_not_lipschitz_at_zero
  exact ⟨C, hC, 1, zero_lt_one, fun x hx _ => hb x hx 0 ⟨le_rfl, zero_le_one⟩⟩

theorem step_bounded (x : ℝ) : |(if x < 0 then 0 else 1 : ℝ)| ≤ 1 := by
  split_ifs <;> norm_num

theorem step_discontinuous :
    ¬ RelativeContinuousAt (fun x : ℝ => (if x < 0 then 0 else 1 : ℝ)) Set.univ 0 := by
  intro hc
  obtain ⟨δ, hδ, hb⟩ := hc (1 / 2) (by norm_num)
  have hx : -(δ / 2) < 0 := by linarith
  have hd : dist (-(δ / 2)) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]
    linarith
  have hbad := hb (-(δ / 2)) (Set.mem_univ _) hd
  norm_num [hx, Real.dist_eq] at hbad

end SingleVariableAnalysis
