import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.Bernstein
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.BernsteinConvergence
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! K03.16.bernstein_convergence. The quantitative estimate is proved from
finite sums and the variance identity; uniform convergence is then deduced
from this estimate and compact uniform continuity. -/
noncomputable section
open scoped BigOperators unitInterval Topology

namespace SingleVariableAnalysis

def bernsteinModulus {E : Type} [NormedAddCommGroup E] (f : C(I, E)) (δ : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x y : I, |(x : ℝ) - y| ≤ δ ∧ r = ‖f x - f y‖}

variable {E : Type} [NormedAddCommGroup E]

lemma bernstein_difference_le (f : C(I, E)) (x y : I) :
    ‖f x - f y‖ ≤ 2 * ‖f‖ := by
  calc
    _ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm x) (f.norm_coe_le_norm y)
    _ = _ := by ring

lemma bernsteinModulus_bddAbove (f : C(I, E)) (δ : ℝ) :
    BddAbove {r : ℝ | ∃ x y : I, |(x : ℝ) - y| ≤ δ ∧ r = ‖f x - f y‖} := by
  refine ⟨2 * ‖f‖, ?_⟩
  rintro r ⟨x, y, _, rfl⟩
  exact bernstein_difference_le f x y

lemma bernsteinModulus_nonempty (f : C(I, E)) {δ : ℝ} (hδ : 0 ≤ δ) :
    Set.Nonempty {r : ℝ | ∃ x y : I, |(x : ℝ) - y| ≤ δ ∧ r = ‖f x - f y‖} := by
  exact ⟨0, 0, 0, by simpa using hδ, by simp⟩

lemma bernsteinModulus_nonneg (f : C(I, E)) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ bernsteinModulus f δ := by
  exact le_csSup (bernsteinModulus_bddAbove f δ)
    ⟨0, 0, by simpa using hδ, by simp⟩

lemma le_bernsteinModulus (f : C(I, E)) (δ : ℝ) (x y : I)
    (h : |(x : ℝ) - y| ≤ δ) : ‖f x - f y‖ ≤ bernsteinModulus f δ := by
  exact le_csSup (bernsteinModulus_bddAbove f δ) ⟨x, y, h, rfl⟩

lemma bernsteinModulus_le (f : C(I, E)) {δ c : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ x y : I, |(x : ℝ) - y| ≤ δ → ‖f x - f y‖ ≤ c) :
    bernsteinModulus f δ ≤ c := by
  apply csSup_le (bernsteinModulus_nonempty f hδ)
  rintro r ⟨x, y, hxy, rfl⟩
  exact h x y hxy

lemma bernsteinModulus_small (f : C(I, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ bernsteinModulus f δ ≤ ε := by
  have hu := CompactSpace.uniformContinuous_of_continuous f.continuous
  obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨η / 2, half_pos hη, bernsteinModulus_le f (half_pos hη).le ?_⟩
  intro x y hxy
  have hd : dist x y < η := by
    rw [Subtype.dist_eq, Real.dist_eq]
    exact hxy.trans_lt (half_lt_self hη)
  simpa only [dist_eq_norm] using (h hd).le


/-- A quadratic envelope handles both near and far sampling nodes. -/
lemma bernstein_difference_quadratic (f : C(I, E)) {δ : ℝ} (hδ : 0 < δ)
    (x y : I) :
    ‖f y - f x‖ ≤ bernsteinModulus f δ +
      (2 * ‖f‖ / δ ^ 2) * ((x : ℝ) - y) ^ 2 := by
  have hω := bernsteinModulus_nonneg f hδ.le
  have hq : 0 ≤ (2 * ‖f‖ / δ ^ 2) * ((x : ℝ) - y) ^ 2 := by positivity
  by_cases hnear : |(x : ℝ) - y| ≤ δ
  · have h := le_bernsteinModulus f δ x y hnear
    rw [norm_sub_rev] at h
    exact h.trans (le_add_of_nonneg_right hq)
  · have hs : δ ^ 2 ≤ ((x : ℝ) - y) ^ 2 := by
      have ha := (not_le.mp hnear).le
      nlinarith [sq_abs ((x : ℝ) - y)]
    have hm : 2 * ‖f‖ ≤ (2 * ‖f‖ / δ ^ 2) * ((x : ℝ) - y) ^ 2 := by
      calc
        _ = (2 * ‖f‖ / δ ^ 2) * δ ^ 2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
    exact (bernstein_difference_le f y x).trans (hm.trans (le_add_of_nonneg_left hω))

section Estimate
variable [NormedSpace ℝ E]

theorem bernsteinApproximation_estimate (f : C(I, E)) (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ : 0 < δ) :
    ‖bernsteinApproximation n f - f‖ ≤
      bernsteinModulus f δ + ‖f‖ / (2 * (n : ℝ) * δ ^ 2) := by
  have hn0 : (n : ℝ) > 0 := by exact_mod_cast hn
  have hω := bernsteinModulus_nonneg f hδ.le
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖bernsteinApproximation n f x - f x‖ ≤ _
  calc
    _ = ‖∑ k : Fin (n + 1), bernstein n k x • (f (bernstein.z k) - f x)‖ := by
      congr 1
      simp [bernsteinApproximation.apply, smul_sub, ← Finset.sum_smul]
    _ ≤ ∑ k : Fin (n + 1), ‖bernstein n k x • (f (bernstein.z k) - f x)‖ :=
      norm_sum_le _ _
    _ = ∑ k : Fin (n + 1), bernstein n k x * ‖f (bernstein.z k) - f x‖ := by
      simp only [norm_smul, Real.norm_of_nonneg bernstein_nonneg]
    _ ≤ ∑ k : Fin (n + 1), bernstein n k x * (bernsteinModulus f δ +
          (2 * ‖f‖ / δ ^ 2) * ((x : ℝ) - bernstein.z k) ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (bernstein_difference_quadratic f hδ x _)
        bernstein_nonneg
    _ = bernsteinModulus f δ + (2 * ‖f‖ / δ ^ 2) * ((x : ℝ) * (1 - x) / n) := by
      simp only [mul_add, Finset.sum_add_distrib]
      have hsum : (∑ k : Fin (n + 1), bernstein n k x *
          ((2 * ‖f‖ / δ ^ 2) * ((x : ℝ) - bernstein.z k) ^ 2)) =
          (2 * ‖f‖ / δ ^ 2) * ∑ k : Fin (n + 1),
            ((x : ℝ) - bernstein.z k) ^ 2 * bernstein n k x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [← Finset.sum_mul, bernstein.probability, one_mul, hsum,
        bernstein.variance (Nat.ne_zero_of_lt hn)]
    _ ≤ bernsteinModulus f δ + (2 * ‖f‖ / δ ^ 2) * ((1 / 4) / n) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_right _ hn0.le
      nlinarith [sq_nonneg ((x : ℝ) - 1 / 2)]
    _ = _ := by congr 1; field_simp; ring

/-- Uniform convergence, obtained from the quantitative estimate above. -/
theorem bernsteinApproximation_uniform_estimate (f : C(I, E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ‖bernsteinApproximation n f - f‖ < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hω⟩ := bernsteinModulus_small f (half_pos hε)
  have ht := tendsto_const_div_atTop_nhds_zero_nat (‖f‖ / (2 * δ ^ 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const (half_pos hε))
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn1)
  have htail : ‖f‖ / (2 * (n : ℝ) * δ ^ 2) < ε / 2 := by
    have hh := hN n ((le_max_right _ _).trans hn)
    convert hh using 1
    field_simp
  exact (bernsteinApproximation_estimate f n hn1 δ hδ).trans_lt (by linarith)

end Estimate

theorem realBernsteinApproximation_estimate (f : C(I, ℝ)) (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ : 0 < δ) :
    ‖realBernsteinApproximation n f - f‖ ≤
      bernsteinModulus f δ + ‖f‖ / (2 * (n : ℝ) * δ ^ 2) :=
  bernsteinApproximation_estimate f n hn δ hδ

theorem complexBernsteinApproximation_estimate (f : C(I, ℂ)) (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ : 0 < δ) :
    ‖complexBernsteinApproximation n f - f‖ ≤
      bernsteinModulus f δ + ‖f‖ / (2 * (n : ℝ) * δ ^ 2) :=
  bernsteinApproximation_estimate f n hn δ hδ

theorem realBernsteinApproximation_uniform (f : C(I, ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x : I,
      |realBernsteinApproximation n f x - f x| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := bernsteinApproximation_uniform_estimate f ε hε
  refine ⟨N, fun n hn x => ?_⟩
  have h := ((bernsteinApproximation n f - f).norm_coe_le_norm x).trans_lt (hN n hn)
  simpa only [realBernsteinApproximation, ContinuousMap.sub_apply, Real.norm_eq_abs] using h

theorem complexBernsteinApproximation_uniform (f : C(I, ℂ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x : I,
      ‖complexBernsteinApproximation n f x - f x‖ < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := bernsteinApproximation_uniform_estimate f ε hε
  exact ⟨N, fun n hn x =>
    ((bernsteinApproximation n f - f).norm_coe_le_norm x).trans_lt (hN n hn)⟩

end SingleVariableAnalysis
