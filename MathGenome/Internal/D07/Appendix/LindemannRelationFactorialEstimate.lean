import MathGenome.Internal.Specs.D07.Appendix.LindemannRelationFactorialEstimate
import MathGenome.Internal.D07.Appendix.LindemannRelationIntegerScaling
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section

namespace D07.Appendix.LindemannRelationFactorialEstimate

open Polynomial Filter
open scoped BigOperators Topology
open Specs.D07.Appendix.LindemannRelationFactorialEstimate

abbrev sourcePolynomial :=
  Specs.D07.Appendix.LindemannRelationFactorialEstimate.sourcePolynomial

abbrev weightedIntegralSum :=
  @Specs.D07.Appendix.LindemannRelationFactorialEstimate.weightedIntegralSum

/-- A finite sum gives an explicit bound even when the root list is empty. -/
theorem exists_segment_bound (m : ℕ) (β : Fin m → ℂ) (a : ℤ) :
    ∃ R : ℝ, 1 ≤ R ∧ (∀ j, ‖(a : ℂ) * β j‖ ≤ R) ∧
      ∀ (j : Fin m) (t : ℝ), 0 ≤ t → t ≤ 1 →
        ‖(a : ℂ) * ((t : ℂ) * β j)‖ ≤ R := by
  let R : ℝ := 1 + ∑ j, ‖(a : ℂ) * β j‖
  have hsum : 0 ≤ ∑ j, ‖(a : ℂ) * β j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hroot (j : Fin m) : ‖(a : ℂ) * β j‖ ≤ R := by
    have hj := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
      norm_nonneg ((a : ℂ) * β i)) (Finset.mem_univ j)
    dsimp [R]
    linarith
  refine ⟨R, by dsimp [R]; linarith, hroot, ?_⟩
  intro j t ht ht'
  calc
    ‖(a : ℂ) * ((t : ℂ) * β j)‖ = |t| * ‖(a : ℂ) * β j‖ := by
      rw [← mul_assoc, mul_comm (a : ℂ) (t : ℂ), mul_assoc, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 * ‖(a : ℂ) * β j‖ :=
      mul_le_mul_of_nonneg_right (by rwa [abs_of_nonneg ht]) (norm_nonneg _)
    _ ≤ R := by simpa using hroot j

theorem sourcePolynomial_eval (a : ℤ) (Q : ℤ[X]) (p : ℕ) (z : ℂ) :
    (sourcePolynomial a Q p).eval z =
      (((a : ℂ) * z) ^ (p - 1) * (Q.map (algebraMap ℤ ℂ)).eval ((a : ℂ) * z) ^ p) /
        (Nat.factorial (p - 1) : ℂ) := by
  simp [sourcePolynomial, Specs.D07.Appendix.LindemannRelationFactorialEstimate.sourcePolynomial,
    auxiliaryPolynomial, Polynomial.eval_comp, div_eq_mul_inv, mul_comm]

/-- The factorization bounds Q on the entire disk of radius R. -/
theorem norm_eval_le (m : ℕ) (β : Fin m → ℂ) (a : ℤ) (Q : ℤ[X])
    (hQ : Q.map (algebraMap ℤ ℂ) = ∏ j, (X - C ((a : ℂ) * β j)))
    (R : ℝ) (_hR : 0 ≤ R) (hroot : ∀ j, ‖(a : ℂ) * β j‖ ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(Q.map (algebraMap ℤ ℂ)).eval z‖ ≤ (2 * R) ^ m := by
  rw [hQ, Polynomial.eval_prod]
  calc
    ‖∏ j, (X - C ((a : ℂ) * β j)).eval z‖ ≤
        ∏ j : Fin m, (2 * R) := by
      apply (Finset.norm_prod_le _ _).trans
      apply Finset.prod_le_prod₀
      · intro j _; exact norm_nonneg _
      · intro j _
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        exact (norm_sub_le _ _).trans (by linarith [hroot j])
    _ = (2 * R) ^ m := by simp

theorem pointwise_factorial_bound (m : ℕ) (β : Fin m → ℂ) (a : ℤ) (Q : ℤ[X])
    (hQ : Q.map (algebraMap ℤ ℂ) = ∏ j, (X - C ((a : ℂ) * β j)))
    (R : ℝ) (hR : 1 ≤ R) (hroot : ∀ j, ‖(a : ℂ) * β j‖ ≤ R)
    (p : ℕ) (j : Fin m) (t : ℝ)
    (hseg : ‖(a : ℂ) * ((t : ℂ) * β j)‖ ≤ R) :
    ‖(sourcePolynomial a Q p).eval ((t : ℂ) * β j)‖ ≤
      (R * (2 * R) ^ m) ^ p / (Nat.factorial (p - 1) : ℝ) := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  rw [sourcePolynomial_eval, norm_div, norm_mul, norm_pow, norm_pow,
    Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    ‖(a : ℂ) * ((t : ℂ) * β j)‖ ^ (p - 1) *
        ‖(Q.map (algebraMap ℤ ℂ)).eval ((a : ℂ) * ((t : ℂ) * β j))‖ ^ p ≤
      R ^ (p - 1) * ((2 * R) ^ m) ^ p := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (norm_nonneg _) hseg _
        · exact pow_le_pow_left₀ (norm_nonneg _)
            (norm_eval_le m β a Q hQ R hR0 hroot _ hseg) _
        · positivity
        · positivity
    _ ≤ R ^ p * ((2 * R) ^ m) ^ p := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR (Nat.sub_le _ _))
        (by positivity)
    _ = (R * (2 * R) ^ m) ^ p := (mul_pow _ _ _).symm

/-- The indexing convention is compatible with the upstream scaling theorem's
root list, without discarding repeated roots. -/
theorem scaled_root_list_factorization (β : List ℂ) (a : ℤ) (Q : ℤ[X])
    (h : Q.map (algebraMap ℤ ℂ) =
      (β.map (fun b => X - C ((a : ℂ) * b))).prod) :
    Q.map (algebraMap ℤ ℂ) =
      ∏ j : Fin β.length, (X - C ((a : ℂ) * β[j.val])) := by
  exact h.trans (Fin.prod_univ_fun_getElem β (fun b : ℂ => X - C ((a : ℂ) * b))).symm

/-- The elementary exponential estimate on every segment. -/
theorem norm_exp_segment_le (β : ℂ) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ‖Complex.exp ((1 - (t : ℂ)) * β)‖ ≤ Real.exp ‖β‖ := by
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht')]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

/-- Any common pointwise bound gives the manuscript's precise integral
weight. The interval norm estimate also applies to the empty root list. -/
theorem weighted_integral_bound (m : ℕ) (β : Fin m → ℂ)
    (a : ℤ) (Q : ℤ[X]) (p : ℕ) (D : ℝ) (_hD : 0 ≤ D)
    (hpoint : ∀ (j : Fin m) (t : ℝ), 0 ≤ t → t ≤ 1 →
      ‖(sourcePolynomial a Q p).eval ((t : ℂ) * β j)‖ ≤ D) :
    ‖weightedIntegralSum β a Q p‖ ≤ (∑ j, ‖β j‖ * Real.exp ‖β j‖) * D := by
  unfold weightedIntegralSum
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => Complex.exp ((1 - (t : ℂ)) * β j) *
      (sourcePolynomial a Q p).eval ((t : ℂ) * β j))
    (C := Real.exp ‖β j‖ * D) ?_
  · simpa using hi
  · intro t ht
    have hmem : 0 < t ∧ t ≤ 1 := by simpa only [Set.uIoc_of_le zero_le_one,
      Set.mem_Ioc] using ht
    rw [norm_mul]
    exact mul_le_mul (norm_exp_segment_le _ _ hmem.1.le hmem.2)
      (hpoint _ _ hmem.1.le hmem.2) (norm_nonneg _) (Real.exp_nonneg _)

theorem uniform_factorial_estimate : UniformFactorialEstimate := by
  intro m β a Q hQ
  obtain ⟨R, hR, hroot, hseg⟩ := exists_segment_bound m β a
  have hC : 1 ≤ R * (2 * R) ^ m := by
    have hpow : 1 ≤ (2 * R) ^ m := one_le_pow₀ (by linarith : 1 ≤ 2 * R)
    exact one_le_mul_of_one_le_of_one_le hR hpow
  have hpoint (p : ℕ) (j : Fin m) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :=
    pointwise_factorial_bound m β a Q hQ R hR hroot p j t (hseg j t ht ht')
  refine ⟨R, R * (2 * R) ^ m, hR, rfl, hC, hroot, hseg,
    (fun p _ j t ht ht' => hpoint p j t ht ht'), ?_⟩
  intro p _
  exact weighted_integral_bound m β a Q p _ (by positivity) (hpoint p)

theorem factorial_decay : FactorialDecay := by
  intro A C
  apply (tendsto_add_atTop_iff_nat 1).mp
  have h := (Real.summable_pow_div_factorial C).tendsto_atTop_zero
  have hmul : Tendsto (fun n : ℕ => (A * C) * (C ^ n / (Nat.factorial n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using h.const_mul (A * C)
  convert hmul using 1
  funext n
  simp only [Nat.add_sub_cancel_right, pow_succ]
  ring

theorem integral_decay : IntegralDecay := by
  intro m β a Q hQ
  obtain ⟨R, C, hR, hCeq, hC, hroot, hseg, hpoint, hint⟩ :=
    uniform_factorial_estimate m β a Q hQ
  apply squeeze_zero_norm' _ (factorial_decay (∑ j, ‖β j‖ * Real.exp ‖β j‖) C)
  filter_upwards [eventually_ge_atTop 1] with p hp
  exact hint p hp

theorem decay_along_allowed_primes : DecayAlongAllowedPrimes := by
  intro m β a Q k hQ u hu _
  exact (integral_decay m β a Q hQ).comp hu

theorem arbitrarily_large_small_integrals : ArbitrarilyLargeSmallIntegrals := by
  intro m β a k Q ha hk hQ0 hQ ε hε B
  have hevent : ∀ᶠ p : ℕ in atTop, ‖weightedIntegralSum β a Q p‖ < ε :=
    (tendsto_order.mp ((integral_decay m β a Q hQ).norm)).2 ε (by simpa using hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  obtain ⟨p, hp, hprime, havoid⟩ :=
    (D07.Appendix.LindemannRelationIntegerScaling.arbitrarily_large_primes k a Q hk ha hQ0).2
      (max B N)
  exact ⟨p, lt_of_le_of_lt (le_max_left _ _) hp, hprime, havoid,
    hN p (le_trans (le_max_right _ _) hp.le)⟩

end D07.Appendix.LindemannRelationFactorialEstimate
