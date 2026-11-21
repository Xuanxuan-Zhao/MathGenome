import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.EquispacedLebesgue
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.InterpolationNorm
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.Approximation

abbrev equispacedNodes := Specs.NumAnalysis206.Approximation.equispacedNodesValue

/-- Factorial expression for the denominator of a cardinal function on an integer grid. -/
theorem integer_grid_denominator (n j : ℕ) (hj : j ≤ n) :
    (∏ k ∈ (Finset.range (n + 1)).erase j, |(j : ℝ) - k|) =
      (j.factorial : ℝ) * (n - j).factorial := by
  induction n with
  | zero =>
    have : j = 0 := by omega
    subst j
    norm_num
  | succ n ih =>
    by_cases h : j = n + 1
    · subst j
      rw [Finset.range_add_one, Finset.erase_insert (by simp)]
      have he : (∏ k ∈ Finset.range (n+1), |((n+1 : ℕ) : ℝ) - k|) =
          ∏ k ∈ Finset.range (n+1), ((k+1 : ℕ) : ℝ) := by
        conv_rhs => rw [← Finset.prod_range_reflect (fun k => ((k+1 : ℕ) : ℝ)) (n+1)]
        apply Finset.prod_congr rfl
        intro k hk
        have hk' : k ≤ n := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (show k ≤ n+1 by omega)))]
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk']
        ring
      rw [he, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
      simp
    · have hj' : j ≤ n := by omega
      rw [Finset.range_add_one, Finset.erase_insert_of_ne (Ne.symm h),
        Finset.prod_insert (by simp), ih hj']
      have hcast : |(j : ℝ) - (n + 1 : ℕ)| = ((n + 1 - j : ℕ) : ℝ) := by
        rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hj)), Nat.cast_sub hj]
        ring
      rw [hcast]
      have hs : n + 1 - j = (n - j) + 1 := by omega
      rw [hs, Nat.factorial_succ]
      push_cast
      ring

/-- The product of distances from the half-grid point has a uniform factorial lower bound. -/
theorem half_grid_product_lower (n : ℕ) :
    (n.factorial : ℝ) ≤ 2 * ((n : ℝ) + 1) *
      ∏ k ∈ Finset.range (n + 1), |(1 / 2 : ℝ) - k| := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ, Nat.factorial_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp : 0 ≤ ∏ k ∈ Finset.range (n+1), |(1/2 : ℝ) - k| :=
      Finset.prod_nonneg (fun _ _ => abs_nonneg _)
    rw [abs_of_nonpos (by push_cast; linarith)]
    push_cast
    have hm := mul_le_mul_of_nonneg_left ih (show 0 ≤ (n : ℝ) + 1 by positivity)
    nlinarith

/-- Canceling all the grid denominators in the normalized cardinal product. -/
theorem integer_grid_cardinal_mul_denominator (n j : ℕ) :
    |(cardinal (Finset.range (n+1)) (fun k : ℕ => (k : ℝ)) j).eval (1/2)| *
        (∏ k ∈ (Finset.range (n+1)).erase j, |(j : ℝ) - k|) =
      ∏ k ∈ (Finset.range (n+1)).erase j, |(1/2 : ℝ) - k| := by
  simp only [cardinal, Specs.NumAnalysis206.Approximation.cardinalValue,
    Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, Finset.abs_prod, abs_mul, abs_inv]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have hkj : (j : ℝ) - k ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (Finset.mem_erase.mp hk).1.symm)
  rw [mul_right_comm, inv_mul_cancel₀ (abs_ne_zero.mpr hkj), one_mul]

/-- A binomial lower bound for each cardinal term; summing will avoid a maximizing index. -/
theorem half_grid_cardinal_lower (n j : ℕ) (hn : 1 ≤ n) (hj : j ≤ n) :
    (n.choose j : ℝ) / (2 * (n : ℝ) * ((n : ℝ) + 1)) ≤
      |(cardinal (Finset.range (n+1)) (fun k : ℕ => (k : ℝ)) j).eval (1/2)| := by
  let P := ∏ k ∈ (Finset.range (n+1)).erase j, |(1/2 : ℝ) - k|
  let L := |(cardinal (Finset.range (n+1)) (fun k : ℕ => (k : ℝ)) j).eval (1/2)|
  have hP : 0 ≤ P := Finset.prod_nonneg (fun _ _ => abs_nonneg _)
  have hj' : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdist : |(1/2 : ℝ) - j| ≤ n := by
    apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j]
  have hprod := half_grid_product_lower n
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))] at hprod
  have hfac : (n.factorial : ℝ) ≤ 2 * (n : ℝ) * ((n : ℝ) + 1) * P := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdist hP)
      (show 0 ≤ 2 * ((n : ℝ) + 1) by positivity)
    dsimp [P] at *
    nlinarith
  have hcancel := integer_grid_cardinal_mul_denominator n j
  rw [integer_grid_denominator n j hj] at hcancel
  have hchoose : (n.choose j : ℝ) * (j.factorial : ℝ) * (n-j).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have hmul : (n.factorial : ℝ) * L = (n.choose j : ℝ) * P := by
    rw [← hchoose]
    dsimp [L, P] at *
    nlinarith [congrArg (fun z : ℝ => (n.choose j : ℝ) * z) hcancel]
  have hc : 0 ≤ (n.choose j : ℝ) := Nat.cast_nonneg _
  have hineq := mul_le_mul_of_nonneg_left hfac hc
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ) * ((n : ℝ)+1))]
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply (mul_le_mul_iff_right₀ hfpos).mp
  calc
    (n.factorial : ℝ) * (n.choose j : ℝ) = (n.choose j : ℝ) * n.factorial := by ring
    _ ≤ (n.choose j : ℝ) *
        (2 * (n : ℝ) * ((n : ℝ)+1) * P) := hineq
    _ = (n.factorial : ℝ) * (L * (2 * (n : ℝ) * ((n : ℝ)+1))) := by
      calc
        _ = (2 * (n : ℝ) * ((n : ℝ)+1)) * ((n.choose j : ℝ) * P) := by ring
        _ = _ := by rw [← hmul]; ring

/-- The affine endpoint grid consists of distinct nodes. -/
theorem equispaced_nodes_injective (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    Function.Injective (equispacedNodes a b hab n hn) := by
  intro i j hij
  have hval := congrArg Subtype.val hij
  change a + (b-a) * (i : ℝ) / n = a + (b-a) * (j : ℝ) / n at hval
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hij' : (i : ℝ) = j := by
    have := (div_left_inj' hn').mp (add_left_cancel hval)
    exact mul_left_cancel₀ (sub_ne_zero.mpr (ne_of_gt hab)) this
  exact Fin.ext (Nat.cast_injective hij')

/-- Affine rescaling preserves the cardinal values at the half-grid point. -/
theorem equispaced_cardinal_half (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n)
    (i : Fin (n+1)) :
    (cardinal Finset.univ (fun j => (equispacedNodes a b hab n hn j : ℝ)) i).eval
        (a + (b-a) / (2 * n)) =
      (cardinal (Finset.range (n+1)) (fun k : ℕ => (k : ℝ)) (i : ℕ)).eval (1/2) := by
  simp only [cardinal, Specs.NumAnalysis206.Approximation.cardinalValue,
    Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X]
  apply Finset.prod_bij (fun (j : Fin (n+1)) _ => (j : ℕ))
  · intro j hj
    exact Finset.mem_erase.mpr ⟨by
      intro h
      exact (Finset.mem_erase.mp hj).1 (Fin.ext h), Finset.mem_range.mpr j.isLt⟩
  · intro j hj k hk h
    exact Fin.ext h
  · intro k hk
    exact ⟨⟨k, Finset.mem_range.mp (Finset.mem_erase.mp hk).2⟩,
      Finset.mem_erase.mpr ⟨by
        intro h
        exact (Finset.mem_erase.mp hk).1 (congrArg Fin.val h), Finset.mem_univ _⟩, rfl⟩
  · intro j hj
    change ((a + (b-a) * (i : ℝ) / n) - (a + (b-a) * (j : ℝ) / n))⁻¹ *
        ((a + (b-a) / (2 * n)) - (a + (b-a) * (j : ℝ) / n)) =
      ((i : ℝ) - (j : ℝ))⁻¹ * ((1/2 : ℝ) - (j : ℝ))
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    have hab' : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
    have hij : (i : ℝ) - (j : ℝ) ≠ 0 := sub_ne_zero.mpr (by
      intro h
      exact (Finset.mem_erase.mp hj).1 (Fin.ext (Nat.cast_injective h.symm)))
    have heq : a + (b-a) * (i : ℝ) / n - (a + (b-a) * (j : ℝ) / n) =
        (b-a) * ((i : ℝ) - j) / n := by ring
    rw [heq]
    field_simp
    ring

/-- W54: the quantitative lower bound, on any fixed nondegenerate compact interval. -/
theorem equispaced_lebesgue_lower (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 2 ≤ n) :
    (2 : ℝ) ^ n / (2 * (n : ℝ) * ((n : ℝ) + 1) ^ 2) ≤
      lebesgueConstant (equispacedNodes a b hab n (by omega)) := by
  have hn0 : 0 < n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by positivity
  let t : Set.Icc a b := ⟨a + (b-a) / (2 * n), by
    constructor
    · exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hab.le) (by positivity))
    · have hdiv : (b-a) / (2 * n) ≤ b-a :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr (by nlinarith)
      linarith⟩
  have hs : (∑ i : Fin (n+1), (n.choose (i : ℕ) : ℝ) /
        (2 * (n : ℝ) * ((n : ℝ)+1))) ≤
      ∑ i : Fin (n+1),
        |(cardinal (Finset.range (n+1)) (fun k : ℕ => (k : ℝ)) (i : ℕ)).eval (1/2)| := by
    apply Finset.sum_le_sum
    intro i _
    exact half_grid_cardinal_lower n i (by omega) (Nat.le_of_lt_succ i.isLt)
  rw [← Finset.sum_div] at hs
  have hsum : (∑ i : Fin (n+1), (n.choose (i : ℕ) : ℝ)) = (2 : ℝ) ^ n := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (n.choose k : ℝ)) (n+1)]
    exact_mod_cast Nat.sum_range_choose n
  rw [hsum] at hs
  have hpoint : (2 : ℝ)^n / (2 * (n : ℝ) * ((n : ℝ)+1)) ≤
      lebesgueFunction (equispacedNodes a b hab n hn0) t := by
    change _ ≤ ∑ i : Fin (n+1),
      |(cardinal Finset.univ (fun j => (equispacedNodes a b hab n hn0 j : ℝ)) i).eval
        (a + (b-a) / (2 * n))|
    simp_rw [equispaced_cardinal_half]
    exact hs
  calc
    (2 : ℝ)^n / (2 * (n : ℝ) * ((n : ℝ)+1)^2) ≤
        (2 : ℝ)^n / (2 * (n : ℝ) * ((n : ℝ)+1)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    _ ≤ lebesgueFunction (equispacedNodes a b hab n hn0) t := hpoint
    _ ≤ lebesgueConstant (equispacedNodes a b hab n hn0) := lebesgueFunction_le _ t

end NumAnalysis206.Approximation
