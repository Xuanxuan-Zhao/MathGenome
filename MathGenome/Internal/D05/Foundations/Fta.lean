import MathGenome.Internal.Specs.D05.Foundations.Fta
import MathGenome.Internal.D05.Foundations.ComplexRoots
import MathGenome.Internal.D05.Foundations.Division
import MathGenome.Internal.D05.Foundations.FtaMinimum
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! An elementary minimum-modulus proof. No algebraic closedness of ℂ or
complex analytic root-existence theorem is imported or assumed. -/
namespace D05.Foundations.Fta
open Polynomial

theorem coercivity : D05.Specs.Fta.coercivity := FtaMinimum.coercivity
theorem globalMinimum : D05.Specs.Fta.globalMinimum := FtaMinimum.globalMinimum

theorem firstTermExpansion : D05.Specs.Fta.firstTermExpansion := by
  intro p hp z₀ hz₀
  let q := C (p.eval z₀)⁻¹ * p.comp (X + C z₀)
  have hqdeg : q.natDegree = p.natDegree := by
    simp [q, natDegree_C_mul (inv_ne_zero hz₀), natDegree_comp]
  have hq0 : q.coeff 0 = 1 := by
    simp [q, coeff_zero_eq_eval_zero, eval_comp, hz₀]
  let f := q - C 1
  have hf : f ≠ 0 := by
    intro h
    have hd : f.natDegree = p.natDegree := by
      dsimp only [f]
      rw [natDegree_sub_C, hqdeg]
    rw [h, natDegree_zero] at hd
    omega
  have hf0 : f.coeff 0 = 0 := by simp [f, hq0]
  let m := f.natTrailingDegree
  have hm : 0 < m := Nat.pos_of_ne_zero (natTrailingDegree_ne_zero.mpr ⟨hf, hf0⟩)
  obtain ⟨s, hs⟩ := X_pow_dvd_iff.mpr
    (fun j hj => coeff_eq_zero_of_lt_natTrailingDegree (p := f) hj)
  have hs0 : s.coeff 0 ≠ 0 := by
    have h := coeff_natTrailingDegree_ne_zero.mpr hf
    have he : f.coeff m = s.coeff 0 := by
      conv_lhs => rw [hs]
      simpa using (coeff_X_pow_mul s m 0)
    exact he ▸ h
  refine ⟨m, s.coeff 0, s.divX, hm, hs0, ?_⟩
  have hq : q = 1 + X ^ m * s := by
    have : q - 1 = X ^ m * s := hs
    linear_combination this
  change q = _
  calc
    q = 1 + X ^ m * (X * s.divX + C (s.coeff 0)) := by rw [X_mul_divX_add, hq]
    _ = _ := by rw [pow_succ]; ring

/-- Bound a polynomial on the radial segment from zero to u by its finite
coefficient sum. This includes constant and zero remainder polynomials. -/
theorem radialBound (r : Polynomial ℂ) (u : ℂ) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖r.eval ((t : ℂ) * u)‖ ≤
      ∑ j ∈ Finset.range (r.natDegree + 1), ‖r.coeff j‖ * ‖u‖ ^ j := by
  have htu : ‖(t : ℂ) * u‖ ≤ ‖u‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    exact mul_le_of_le_one_left (norm_nonneg u) ht1
  rw [eval_eq_sum_range]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) htu j) (norm_nonneg _)

theorem descentEstimate : D05.Specs.Fta.descentEstimate := by
  intro m a r hm ha
  obtain ⟨u, hu⟩ := ComplexRoots.complexRoot (-a⁻¹) m hm
  have hau : a * u ^ m = -1 := by rw [hu, mul_neg, mul_inv_cancel₀ ha]
  let S : ℝ := ∑ j ∈ Finset.range (r.natDegree + 1), ‖r.coeff j‖ * ‖u‖ ^ j
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
  refine ⟨u, ‖u‖ ^ (m + 1) * S, hau, mul_nonneg (pow_nonneg (norm_nonneg _) _) hS, ?_⟩
  intro t ht ht1
  have htm : t ^ m ≤ 1 := pow_le_one₀ ht ht1
  have hlead : 1 + a * ((t : ℂ) * u) ^ m = ((1 - t ^ m : ℝ) : ℂ) := by
    rw [mul_pow]
    calc
      1 + a * ((t : ℂ) ^ m * u ^ m) = 1 + (t : ℂ) ^ m * (a * u ^ m) := by ring
      _ = _ := by
        rw [hau]
        simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
        ring
  have hnlead : ‖1 + a * ((t : ℂ) * u) ^ m‖ = 1 - t ^ m := by
    rw [hlead, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr htm)]
  have htail : ‖((t : ℂ) * u) ^ (m + 1) * r.eval ((t : ℂ) * u)‖ ≤
      (‖u‖ ^ (m + 1) * S) * t ^ (m + 1) := by
    rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht, mul_pow]
    calc
      _ ≤ (t ^ (m + 1) * ‖u‖ ^ (m + 1)) * S :=
        mul_le_mul_of_nonneg_left (radialBound r u t ht ht1) (by positivity)
      _ = _ := by ring
  exact (norm_add_le _ _).trans (by rw [hnlead]; linarith)

theorem strictDescent : D05.Specs.Fta.strictDescent := by
  intro p hp z₀ hz₀
  obtain ⟨m, a, r, hm, ha, hexp⟩ := firstTermExpansion p hp z₀ hz₀
  obtain ⟨u, B, _, hB, hest⟩ := descentEstimate m a r hm ha
  let t : ℝ := 1 / (2 * (B + 1))
  have hden : 0 < 2 * (B + 1) := by positivity
  have ht : 0 < t := one_div_pos.mpr hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have hBt : B * t < 1 := by
    dsimp [t]
    rw [mul_one_div, div_lt_one hden]
    linarith
  have htm : 0 < t ^ m := pow_pos ht m
  have hsmall : 1 - t ^ m + B * t ^ (m + 1) < 1 := by
    rw [pow_succ]
    nlinarith [mul_lt_mul_of_pos_left hBt htm]
  have heval :
      (p.eval z₀)⁻¹ * p.eval (z₀ + (t : ℂ) * u) =
        1 + a * ((t : ℂ) * u) ^ m +
        ((t : ℂ) * u) ^ (m + 1) * r.eval ((t : ℂ) * u) := by
    have he := congrArg (fun f : Polynomial ℂ => f.eval ((t : ℂ) * u)) hexp
    simpa [eval_comp, add_comm] using he
  have hratio : ‖(p.eval z₀)⁻¹ * p.eval (z₀ + (t : ℂ) * u)‖ < 1 := by
    rw [heval]
    exact (hest t ht.le ht1.le).trans_lt hsmall
  refine ⟨z₀ + (t : ℂ) * u, ?_⟩
  have hpz : 0 < ‖p.eval z₀‖ := norm_pos_iff.mpr hz₀
  rw [norm_mul, norm_inv, ← div_eq_inv_mul, div_lt_one hpz] at hratio
  exact hratio

theorem minimumZero : D05.Specs.Fta.minimumZero := by
  intro p hp z₀ hmin
  by_contra hne
  obtain ⟨z, hz⟩ := strictDescent p hp z₀ hne
  exact (not_lt_of_ge (hmin z)) hz

theorem existsRoot : D05.Specs.Fta.existsRoot := by
  intro p hp
  obtain ⟨z₀, hmin⟩ := globalMinimum p hp
  exact ⟨z₀, minimumZero p hp z₀ hmin⟩

/-- Repeated removal of a scalar root terminates by natural-degree induction.
The generic `Splits` predicate is only algebraic factorization, with no instance
of algebraic closedness being used. -/
theorem splits (p : Polynomial ℂ) : p.Splits := by
  suffices ∀ (n : ℕ) (f : Polynomial ℂ), f.natDegree = n → f.Splits from
    this p.natDegree p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hd
    by_cases hfdeg : f.natDegree = 0
    · exact Splits.of_natDegree_eq_zero hfdeg
    have hf : f ≠ 0 := by
      intro hzero
      simp [hzero] at hfdeg
    obtain ⟨z, hz⟩ := existsRoot f (Nat.pos_of_ne_zero hfdeg)
    obtain ⟨q, hq⟩ := (dvd_iff_isRoot).mpr hz
    have hq0 : q ≠ 0 := by
      intro hzero
      simp [hzero] at hq
      exact hf hq
    have hdeg : q.natDegree < n := by
      rw [hq, natDegree_mul (X_sub_C_ne_zero z) hq0, natDegree_X_sub_C] at hd
      omega
    rw [hq]
    exact (Splits.X_sub_C z).mul (ih q.natDegree hdeg q rfl)

theorem linearFactorization : D05.Specs.Fta.linearFactorization := by
  intro p _hp
  exact ⟨p.roots, (splits p).natDegree_eq_card_roots.symm, (splits p).eq_prod_roots⟩

end D05.Foundations.Fta
