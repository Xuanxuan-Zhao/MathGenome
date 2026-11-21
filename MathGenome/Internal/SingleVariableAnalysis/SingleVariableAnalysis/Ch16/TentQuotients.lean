import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.TentContinuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.TentQuotients
import Mathlib.Tactic.FieldSimp

/-! Signed half-cell difference quotients for the periodic tent construction.
No derivative or exchange of differentiation and infinite sums is used. -/

noncomputable section
namespace SingleVariableAnalysis

open scoped BigOperators

private abbrev gamma := Specs.SingleVariableAnalysis.Ch16.TentQuotients.gamma

/-- One of the two half-unit directions stays inside the current integer cell. -/
theorem exists_tent_half_cell (y : ℝ) :
    ∃ (s : ℝ) (k : ℤ), (s = 1 / 2 ∨ s = -(1 / 2)) ∧
      y ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1) ∧
      y + s ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1) := by
  have hl := Int.floor_le y
  have hu := Int.lt_floor_add_one y
  by_cases h : y - (⌊y⌋ : ℝ) ≤ 1 / 2
  · exact ⟨1 / 2, ⌊y⌋, Or.inl rfl, ⟨hl, hu.le⟩, by constructor <;> linarith⟩
  · exact ⟨-(1 / 2), ⌊y⌋, Or.inr rfl, ⟨hl, hu.le⟩, by constructor <;> linarith⟩

/-- An open segment contained in one integer cell has no integer inside it. -/
theorem tent_cell_no_integer {u v : ℝ} {k : ℤ}
    (hu : u ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1))
    (hv : v ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) :
    ∀ j : ℤ, (j : ℝ) ∉ Set.uIoo u v := by
  intro j hj
  have hj' := Set.uIoo_subset_Ioo hu hv hj
  have ha : k < j := by exact_mod_cast hj'.1
  have hb : j < k + 1 := by exact_mod_cast hj'.2
  omega

theorem tent_gamma_bound (n : ℕ) (x h : ℝ) (hh : h ≠ 0) :
    |gamma n x h| ≤ (4 : ℝ) ^ n := by
  have hb := periodicTent_lipschitz ((4 : ℝ) ^ n * (x + h)) ((4 : ℝ) ^ n * x)
  have hp : 0 ≤ (4 : ℝ) ^ n := pow_nonneg (by norm_num) _
  change |(periodicTent _ - periodicTent _) / h| ≤ _
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hh)]
  calc
    |periodicTent _ - periodicTent _| ≤
        |(4 : ℝ) ^ n * (x + h) - 4 ^ n * x| := hb
    _ = (4 : ℝ) ^ n * |h| := by
      rw [show (4 : ℝ) ^ n * (x + h) - 4 ^ n * x = 4 ^ n * h by ring,
        abs_mul, abs_of_nonneg hp]

theorem tent_gamma_main (m : ℕ) (x h : ℝ) (hh : h ≠ 0) (k : ℤ)
    (hx : (4 : ℝ) ^ m * x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1))
    (hy : (4 : ℝ) ^ m * (x + h) ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) :
    |gamma m x h| = (4 : ℝ) ^ m := by
  obtain ⟨a, ha, hf⟩ := periodicTent_affine k
  have he : gamma m x h = a * (4 : ℝ) ^ m := by
    change (periodicTent _ - periodicTent _) / h = _
    rw [hf _ hy, hf _ hx]
    apply (div_eq_iff hh).mpr
    ring
  rw [he, abs_mul, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 4) m)]
  rcases ha with rfl | rfl <;> norm_num

/-- All terms above the chosen scale undergo an even integral translation. -/
theorem tent_gamma_later (m n : ℕ) (x h : ℝ) (hmn : m < n)
    (hh : h = (1 / 2 : ℝ) / 4 ^ m ∨ h = -((1 / 2 : ℝ) / 4 ^ m)) :
    gamma n x h = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, n = m + (r + 1) := ⟨n - m - 1, by omega⟩
  have hp : (4 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hd : (4 : ℝ) ^ (m + (r + 1)) * ((1 / 2 : ℝ) / 4 ^ m) =
      (4 ^ r : ℕ) * (2 : ℝ) := by
    push_cast
    rw [pow_add, pow_succ]
    field_simp
    ring
  change (periodicTent _ - periodicTent _) / h = 0
  rw [mul_add]
  rcases hh with rfl | rfl
  · rw [hd, periodicTent_period.nat_mul (4 ^ r)]
    simp
  · rw [mul_neg, hd, periodicTent_period.neg_nat_mul (4 ^ r)]
    simp

/-- The infinite sum difference is finitely supported at these increments. -/
theorem tentSeries_quotient_finite (m : ℕ) (x h : ℝ)
    (hh : h = (1 / 2 : ℝ) / 4 ^ m ∨ h = -((1 / 2 : ℝ) / 4 ^ m)) :
    (tentSeries (x + h) - tentSeries x) / h =
      ∑ n ∈ Finset.range (m + 1), (3 / 4 : ℝ) ^ n * gamma n x h := by
  have ht : ∀ n ∉ Finset.range (m + 1),
      tentSeriesTerm n (x + h) - tentSeriesTerm n x = 0 := by
    intro n hn
    have hn' : m < n := by simp only [Finset.mem_range] at hn; omega
    have hz := tent_gamma_later m n x h hn' hh
    have hne : h ≠ 0 := by
      rcases hh with rfl | rfl
      · exact div_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
      · exact neg_ne_zero.mpr (div_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
    have he : periodicTent ((4 : ℝ) ^ n * (x + h)) - periodicTent (4 ^ n * x) = 0 :=
      (div_eq_zero_iff.mp hz).resolve_right hne
    dsimp [tentSeriesTerm]
    rw [← mul_sub, he, mul_zero]
  change ((∑' n, tentSeriesTerm n (x + h)) - ∑' n, tentSeriesTerm n x) / h = _
  rw [← (tentSeries_summable (x + h)).tsum_sub (tentSeries_summable x),
    tsum_eq_sum ht, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  change ((3 / 4 : ℝ) ^ n * periodicTent _ - (3 / 4 : ℝ) ^ n * periodicTent _) * h⁻¹ =
    (3 / 4 : ℝ) ^ n * ((periodicTent _ - periodicTent _) / h)
  ring

/-- The largest scale dominates the sum of all earlier quotient bounds. -/
theorem tentSeries_quotient_lower_bound (m : ℕ) (x h : ℝ)
    (hh : h = (1 / 2 : ℝ) / 4 ^ m ∨ h = -((1 / 2 : ℝ) / 4 ^ m))
    (hm : |gamma m x h| = (4 : ℝ) ^ m)
    (hb : ∀ n < m, |gamma n x h| ≤ (4 : ℝ) ^ n) :
    ((3 : ℝ) ^ m + 1) / 2 ≤ |(tentSeries (x + h) - tentSeries x) / h| := by
  have hw (n : ℕ) : (3 / 4 : ℝ) ^ n * (4 : ℝ) ^ n = 3 ^ n := by
    rw [← mul_pow]
    norm_num
  have hmain : |(3 / 4 : ℝ) ^ m * gamma m x h| = 3 ^ m := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by norm_num) _), hm, hw]
  have hrest : |∑ n ∈ Finset.range m, (3 / 4 : ℝ) ^ n * gamma n x h| ≤
      ∑ n ∈ Finset.range m, (3 : ℝ) ^ n := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by norm_num) _), ← hw n]
    exact mul_le_mul_of_nonneg_left (hb n (Finset.mem_range.mp hn))
      (pow_nonneg (by norm_num) _)
  have hgeom : (∑ n ∈ Finset.range m, (3 : ℝ) ^ n) = (3 ^ m - 1) / 2 := by
    rw [geometric_sum_range (3 : ℝ) (by norm_num)]
    ring
  have htri := abs_sub
    ((∑ n ∈ Finset.range m, (3 / 4 : ℝ) ^ n * gamma n x h) +
      (3 / 4 : ℝ) ^ m * gamma m x h)
    (∑ n ∈ Finset.range m, (3 / 4 : ℝ) ^ n * gamma n x h)
  rw [add_sub_cancel_left, hmain] at htri
  rw [tentSeries_quotient_finite m x h hh, Finset.sum_range_succ]
  rw [hgeom] at hrest
  linarith

/-- The simultaneous conclusions for the signed increments in the manuscript. -/
theorem tent_half_cell_quotients :
    Specs.SingleVariableAnalysis.Ch16.TentQuotients.halfCellQuotients := by
  intro x m _hm
  obtain ⟨s, k, hs, hx, hy⟩ := exists_tent_half_cell ((4 : ℝ) ^ m * x)
  let h : ℝ := s / (4 : ℝ) ^ m
  have hp : (4 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hh : h = (1 / 2 : ℝ) / 4 ^ m ∨ h = -((1 / 2 : ℝ) / 4 ^ m) := by
    rcases hs with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (neg_div _ _)
  have hne : h ≠ 0 := by
    apply div_ne_zero _ hp
    rcases hs with rfl | rfl <;> norm_num
  have hd : (4 : ℝ) ^ m * (x + h) = (4 : ℝ) ^ m * x + s := by
    dsimp [h]
    field_simp
  have hy' : (4 : ℝ) ^ m * (x + h) ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1) := hd ▸ hy
  have hmain := tent_gamma_main m x h hne k hx hy'
  have hbound : ∀ n < m, |gamma n x h| ≤ (4 : ℝ) ^ n :=
    fun n _ => tent_gamma_bound n x h hne
  refine ⟨h, hh, hne, tent_cell_no_integer hx hy', hmain, hbound, ?_, ?_, ?_⟩
  · exact fun n hn => tent_gamma_later m n x h hn hh
  · exact tentSeries_quotient_finite m x h hh
  · exact tentSeries_quotient_lower_bound m x h hh hmain hbound

end SingleVariableAnalysis
