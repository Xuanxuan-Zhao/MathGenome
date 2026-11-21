import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.HolderBernstein
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators unitInterval

namespace NumAnalysis206.HolderBernstein

/-- The Jensen bridge from a second moment to a fractional absolute moment. -/
theorem weighted_abs_rpow_le {ι : Type*} [Fintype ι]
    (w d : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∑ i, w i * |d i| ^ α) ≤ (∑ i, w i * (d i) ^ 2) ^ (α / 2) := by
  have hj := (Real.concaveOn_rpow (by positivity : 0 ≤ α / 2)
      (by linarith : α / 2 ≤ 1)).le_map_sum
      (t := Finset.univ) (w := w) (p := fun i => (d i) ^ 2)
      (fun i _ => hw i) hs (fun i _ => sq_nonneg (d i))
  simp only [smul_eq_mul] at hj
  convert hj using 1
  congr 1
  funext i
  congr 1
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg (d i))]
  congr 1
  ring

/-- The fractional Bernstein moment, with the sharp variance bound `1/(4n)`. -/
theorem bernstein_moment_le {n : ℕ} (hn : 1 ≤ n) (x : I)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∑ k : Fin (n + 1), bernstein n k x * |(x : ℝ) - bernstein.z k| ^ α)
      ≤ (4 * (n : ℝ)) ^ (-α / 2) := by
  calc
    _ ≤ (∑ k : Fin (n + 1), bernstein n k x *
          ((x : ℝ) - bernstein.z k) ^ 2) ^ (α / 2) :=
      weighted_abs_rpow_le _ _ (fun _ => bernstein_nonneg) (bernstein.probability n x) hα hα1
    _ = ((x : ℝ) * (1 - x) / n) ^ (α / 2) := by
      congr 1
      simpa only [mul_comm] using bernstein.variance (by omega : n ≠ 0) x
    _ ≤ (1 / (4 * (n : ℝ))) ^ (α / 2) := by
      apply Real.rpow_le_rpow
        (div_nonneg (mul_nonneg x.property.1 (sub_nonneg.mpr x.property.2))
          (Nat.cast_nonneg n)) _ (by positivity)
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      apply (div_le_iff₀ hn').2
      have hx : (x : ℝ) * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg ((x : ℝ) - 1/2)]
      calc
        _ ≤ 1 / 4 := hx
        _ = 1 / (4 * (n : ℝ)) * n := by field_simp
    _ = (4 * (n : ℝ)) ^ (-α / 2) := by
      rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
      congr 1
      ring

/-- Quantitative pointwise Bernstein approximation for Hölder data. -/
theorem pointwise_error_le (f : C(I, ℝ)) {α L : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : ∀ s t : I, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α)
    {n : ℕ} (hn : 1 ≤ n) (x : I) :
    |bernsteinApproximation n f x - f x| ≤ L * (4 * (n : ℝ)) ^ (-α / 2) := by
  have herr : bernsteinApproximation n f x - f x =
      ∑ k : Fin (n + 1), bernstein n k x * (f (bernstein.z k) - f x) := by
    simp [bernsteinApproximation.apply, mul_sub, ← Finset.sum_mul]
  rw [herr]
  calc
    _ ≤ ∑ k : Fin (n + 1), |bernstein n k x * (f (bernstein.z k) - f x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin (n + 1), bernstein n k x * |f (bernstein.z k) - f x| := by
      simp only [abs_mul, abs_of_nonneg bernstein_nonneg]
    _ ≤ ∑ k : Fin (n + 1), bernstein n k x * (L * |(x : ℝ) - bernstein.z k| ^ α) := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ bernstein_nonneg
      simpa only [abs_sub_comm] using hf x (bernstein.z k)
    _ = L * ∑ k : Fin (n + 1), bernstein n k x * |(x : ℝ) - bernstein.z k| ^ α := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (bernstein_moment_le hn x hα hα1) hL

/-- The uniform norm estimate on the full closed unit interval. -/
theorem uniform_error_le (f : C(I, ℝ)) {α L : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : ∀ s t : I, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖bernsteinApproximation n f - f‖ ≤ L * (4 * (n : ℝ)) ^ (-α / 2) := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro x
  simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using
    pointwise_error_le f hα hα1 hL hf hn x

/-- The continuous Bernstein sum is the evaluation of the algebraic polynomial. -/
theorem unitPolynomial_eval (n : ℕ) (f : C(I, ℝ)) (x : I) :
    (unitPolynomial n f).eval (x : ℝ) = bernsteinApproximation n f x := by
  simp [unitPolynomial, Polynomial.eval_finsetSum, bernsteinApproximation.apply, bernstein, smul_eq_mul,
    Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply, mul_comm]

/-- The Bernstein sum has degree at most `n`, also for `n = 0`. -/
theorem unitPolynomial_natDegree_le (n : ℕ) (f : C(I, ℝ)) :
    (unitPolynomial n f).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  unfold bernsteinPolynomial
  have hlin : (1 - Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp
  calc
    _ ≤ ((n.choose (k : ℕ) : Polynomial ℝ) * Polynomial.X ^ (k : ℕ)).natDegree +
        ((1 - Polynomial.X : Polynomial ℝ) ^ (n - (k : ℕ))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (k : ℕ) + (n - (k : ℕ)) := by
      apply Nat.add_le_add
      · simpa using (Polynomial.natDegree_C_mul_le (n.choose (k : ℕ) : ℝ)
          (Polynomial.X ^ (k : ℕ)))
      · exact (Polynomial.natDegree_pow_le).trans (by nlinarith)
    _ = n := Nat.add_sub_of_le k.is_le

/-- Affine pullback multiplies the Hölder constant by the length to the power `α`. -/
theorem pullback_holder (a b : ℝ) (hab : a < b) (f : C(Set.Icc a b, ℝ))
    {α L : ℝ}
    (hf : ∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α)
    (s t : I) :
    |pullback a b hab.le f t - pullback a b hab.le f s| ≤
      (L * (b - a) ^ α) * |(t : ℝ) - s| ^ α := by
  have h := hf (affineParam a b hab.le s) (affineParam a b hab.le t)
  change |pullback a b hab.le f t - pullback a b hab.le f s| ≤
    L * |(a + (b - a) * (t : ℝ)) - (a + (b - a) * (s : ℝ))| ^ α at h
  convert h using 1
  have hid : a + (b - a) * (t : ℝ) - (a + (b - a) * (s : ℝ)) =
      (b - a) * ((t : ℝ) - s) := by ring
  rw [hid, abs_mul, abs_of_nonneg (sub_nonneg.mpr hab.le),
    Real.mul_rpow (sub_nonneg.mpr hab.le) (abs_nonneg _)]
  ring

/-- Returning a normalized point to the interval recovers the original point. -/
theorem affineParam_normalize (a b : ℝ) (hab : a < b) (x : Set.Icc a b) :
    affineParam a b hab.le (normalize a b hab x) = x := by
  apply Subtype.ext
  change a + (b - a) * (((x : ℝ) - a) / (b - a)) = x
  field_simp
  ring

/-- The transported algebraic polynomial agrees with the normalized Bernstein sum. -/
theorem intervalApproximation_apply (a b : ℝ) (hab : a < b) (n : ℕ)
    (f : C(Set.Icc a b, ℝ)) (x : Set.Icc a b) :
    intervalApproximation a b hab n f x =
      bernsteinApproximation n (pullback a b hab.le f) (normalize a b hab x) := by
  rw [← unitPolynomial_eval]
  change (intervalPolynomial a b hab n f).eval (x : ℝ) = _
  simp only [intervalPolynomial, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  congr 1
  change (b - a)⁻¹ * ((x : ℝ) - a) = ((x : ℝ) - a) / (b - a)
  ring

/-- Affine transport does not increase the degree. -/
theorem intervalPolynomial_natDegree_le (a b : ℝ) (hab : a < b) (n : ℕ)
    (f : C(Set.Icc a b, ℝ)) :
    (intervalPolynomial a b hab n f).natDegree ≤ n := by
  have hlin : (Polynomial.C (b - a)⁻¹ *
      (Polynomial.X - Polynomial.C a)).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp
  exact Polynomial.natDegree_comp_le.trans
    ((Nat.mul_le_mul (unitPolynomial_natDegree_le n _) hlin).trans (by simp))

/-- Uniform quantitative approximation on any nondegenerate compact interval. -/
theorem interval_uniform_error_le (a b : ℝ) (hab : a < b)
    (f : C(Set.Icc a b, ℝ)) {α L : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : ∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖intervalApproximation a b hab n f - f‖ ≤
      (L * (b - a) ^ α) * (4 * (n : ℝ)) ^ (-α / 2) := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro x
  have h := pointwise_error_le (pullback a b hab.le f) hα hα1
    (by positivity) (pullback_holder a b hab f hf) hn (normalize a b hab x)
  simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs, intervalApproximation_apply,
    pullback, ContinuousMap.comp_apply, affineParam_normalize] using h

end NumAnalysis206.HolderBernstein
