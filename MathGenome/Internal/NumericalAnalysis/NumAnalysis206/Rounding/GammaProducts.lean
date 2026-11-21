import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.GammaProducts
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open scoped BigOperators
namespace NumAnalysis206.Rounding

/-- The real rounding budget; its validity is expressed by `BudgetDomain`. -/
def gamma (n : ℕ) (u : ℝ) : ℝ := (n : ℝ) * u / (1 - (n : ℝ) * u)

/-- W06's admissible domain, also required when using larger path budgets. -/
def BudgetDomain (n : ℕ) (u : ℝ) : Prop :=
  0 ≤ u ∧ u < 1 ∧ (n : ℝ) * u < 1

theorem budgetDomain_mono {n N : ℕ} {u : ℝ} (h : n ≤ N)
    (hu : BudgetDomain N u) : BudgetDomain n u := by
  refine ⟨hu.1, hu.2.1, lt_of_le_of_lt ?_ hu.2.2⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) hu.1

theorem gamma_nonneg {n : ℕ} {u : ℝ} (hu : BudgetDomain n u) :
    0 ≤ gamma n u :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu.1) (by linarith [hu.2.2])

theorem gamma_mono {n N : ℕ} {u : ℝ} (h : n ≤ N)
    (hu : BudgetDomain N u) : gamma n u ≤ gamma N u := by
  have hn := budgetDomain_mono h hu
  have hmul : (n : ℝ) * u ≤ (N : ℝ) * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h) hu.1
  unfold gamma
  apply (div_le_div_iff₀ (by linarith [hn.2.2]) (by linarith [hu.2.2])).2
  nlinarith

private theorem factor_bounds {u d : ℝ} (_hu : 0 ≤ u) (hu1 : u < 1)
    (hd : |d| ≤ u) :
    0 < 1 + d ∧ 1 - u ≤ 1 + d ∧ 1 - u ≤ (1 + d)⁻¹ := by
  obtain ⟨hdl, hdr⟩ := abs_le.mp hd
  have hp : 0 < 1 + d := by linarith
  refine ⟨hp, by linarith, ?_⟩
  rw [← one_div]
  apply (le_div_iff₀ hp).2
  have hprod := mul_le_mul_of_nonneg_left hdr (show 0 ≤ 1 - u by linarith)
  nlinarith [sq_nonneg u]

private theorem signed_factor_bounds {u d : ℝ} {r : ℤ}
    (hu : 0 ≤ u) (hu1 : u < 1) (hd : |d| ≤ u) (hr : r = -1 ∨ r = 1) :
    0 < (1 + d) ^ r ∧ 1 - u ≤ (1 + d) ^ r ∧
      1 - u ≤ ((1 + d) ^ r)⁻¹ := by
  obtain ⟨hp, hl, hi⟩ := factor_bounds hu hu1 hd
  rcases hr with rfl | rfl
  · simpa using And.intro (inv_pos.mpr hp) (And.intro hi hl)
  · simpa using And.intro hp (And.intro hl hi)

theorem factors_positive {n : ℕ} {u : ℝ} (δ : ℕ → ℝ) (ρ : ℕ → ℤ)
    (hu : BudgetDomain n u) (hd : ∀ i < n, |δ i| ≤ u)
    (hr : ∀ i < n, ρ i = -1 ∨ ρ i = 1) :
    ∀ i < n, 0 < 1 + δ i ∧ 1 + δ i ≠ 0 ∧
      0 < (1 + δ i) ^ (ρ i) ∧ (1 + δ i) ^ (ρ i) ≠ 0 := by
  intro i hi
  have hp := (factor_bounds hu.1 hu.2.1 (hd i hi)).1
  have hsp := (signed_factor_bounds hu.1 hu.2.1 (hd i hi) (hr i hi)).1
  exact ⟨hp, ne_of_gt hp, hsp, ne_of_gt hsp⟩

private theorem product_lower {n : ℕ} {u : ℝ} (f : ℕ → ℝ)
    (hu : u < 1) (hf : ∀ i < n, 1 - u ≤ f i) :
    1 - (n : ℝ) * u ≤ ∏ i ∈ Finset.range n, f i := by
  have hb : 1 - (n : ℝ) * u ≤ (1 - u) ^ n := by
    simpa only [mul_neg, ← sub_eq_add_neg] using
      (one_add_mul_le_pow (show (-2 : ℝ) ≤ -u by linarith) n)
  apply hb.trans
  calc
    (1 - u) ^ n = ∏ _i ∈ Finset.range n, (1 - u) := by simp
    _ ≤ ∏ i ∈ Finset.range n, f i :=
      Finset.prod_le_prod₀ (fun _ _ => by linarith) (fun i hi => hf i (Finset.mem_range.mp hi))

theorem signed_products {n : ℕ} {u : ℝ} (δ : ℕ → ℝ) (ρ : ℕ → ℤ)
    (hu : BudgetDomain n u) (hd : ∀ i < n, |δ i| ≤ u)
    (hr : ∀ i < n, ρ i = -1 ∨ ρ i = 1) :
    ∃ θ : ℝ, (∏ i ∈ Finset.range n, (1 + δ i) ^ (ρ i)) = 1 + θ ∧
      |θ| ≤ gamma n u ∧ (n = 0 → θ = 0) := by
  let f : ℕ → ℝ := fun i => (1 + δ i) ^ (ρ i)
  let P : ℝ := ∏ i ∈ Finset.range n, f i
  have hf (i : ℕ) (hi : i < n) :
      0 < f i ∧ 1 - u ≤ f i ∧ 1 - u ≤ (f i)⁻¹ :=
    signed_factor_bounds hu.1 hu.2.1 (hd i hi) (hr i hi)
  have hp : 0 < P := Finset.prod_pos (fun i hi => (hf i (Finset.mem_range.mp hi)).1)
  have hl : 1 - (n : ℝ) * u ≤ P :=
    product_lower f hu.2.1 (fun i hi => (hf i hi).2.1)
  have hi : 1 - (n : ℝ) * u ≤ P⁻¹ := by
    simpa only [Finset.prod_inv_distrib] using
      (product_lower (fun i => (f i)⁻¹) hu.2.1 (fun i hi => (hf i hi).2.2))
  have hdpos : 0 < 1 - (n : ℝ) * u := by linarith [hu.2.2]
  have hupper : P ≤ (1 - (n : ℝ) * u)⁻¹ := le_inv_of_le_inv₀ hdpos hi
  have hnu : 0 ≤ (n : ℝ) * u := mul_nonneg (Nat.cast_nonneg n) hu.1
  have hbudget : (n : ℝ) * u ≤ gamma n u := by
    unfold gamma
    apply (le_div_iff₀ hdpos).2
    nlinarith [sq_nonneg ((n : ℝ) * u)]
  refine ⟨P - 1, by dsimp [P, f]; ring, abs_le.mpr ⟨by linarith, ?_⟩, ?_⟩
  · have heq : (1 - (n : ℝ) * u)⁻¹ - 1 = gamma n u := by
      unfold gamma
      field_simp [ne_of_gt hdpos]
      ring
    linarith
  · intro hn
    subst n
    simp [P]

theorem empty_product (u : ℝ) (δ : ℕ → ℝ) (ρ : ℕ → ℤ) :
    (∏ i ∈ Finset.range 0, (1 + δ i) ^ (ρ i)) = 1 + (0 : ℝ) ∧ gamma 0 u = 0 := by
  simp [gamma]

end NumAnalysis206.Rounding
