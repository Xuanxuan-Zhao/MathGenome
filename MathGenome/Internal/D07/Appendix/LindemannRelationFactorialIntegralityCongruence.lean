import MathGenome.Internal.Specs.D07.Appendix.LindemannRelationFactorialIntegralityCongruence
import MathGenome.Internal.D07.Appendix.IntegerPowerSums
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace D07.Appendix.LindemannRelationFactorialIntegralityCongruence
open Polynomial
open Specs.D07.Appendix.LindemannRelationFactorialIntegralityCongruence

lemma factorial_derivative (P : ℤ[X]) (r : ℕ) :
    derivative^[r] P = C (Nat.factorial r : ℤ) * hasseDeriv r P := by
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℤ) r) P
  change r.factorial • (hasseDeriv r P) = derivative^[r] P at h
  rw [← h]
  simp only [nsmul_eq_mul, C_eq_natCast]

lemma factorial_multiple (p r : ℕ) (hp : 0 < p) (hr : p ≤ r) :
    ∃ t : ℕ, Nat.factorial r = p * Nat.factorial (p - 1) * t := by
  obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial hr
  refine ⟨t, ?_⟩
  rw [← Nat.sub_add_cancel hp, Nat.factorial_succ] at ht
  simpa only [Nat.sub_add_cancel hp] using ht

theorem factorial_derivatives : FactorialDerivatives :=
  ⟨factorial_derivative, factorial_multiple⟩

lemma iterate_derivative_scale (P : ℂ[X]) (a : ℂ) (r : ℕ) :
    derivative^[r] (P.comp (C a * X)) =
      C (a ^ r) * (derivative^[r] P).comp (C a * X) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp]
    simp only [derivative_C_mul, derivative_X, mul_one, Function.iterate_succ_apply']
    rw [pow_succ, C_mul]
    ring

theorem derivative_substitution : DerivativeSubstitution := by
  intro a Q p r z
  rw [f, iterate_derivative_C_mul, iterate_derivative_scale, iterate_derivative_map]
  simp only [eval_mul, eval_C, eval_comp, eval_X, eval_map]
  ring

lemma derivative_eval (a : ℤ) (Q : ℤ[X]) (p r : ℕ) (z : ℂ) :
    (derivative^[r] (f a Q p)).eval z =
      (a : ℂ) ^ r * (Nat.factorial r : ℂ) / (Nat.factorial (p - 1) : ℂ) *
        (hasseDeriv r (H Q p)).eval₂ (Int.castRingHom ℂ) ((a : ℂ) * z) := by
  rw [f, iterate_derivative_C_mul, iterate_derivative_scale,
    iterate_derivative_map, factorial_derivative]
  simp only [Polynomial.map_mul, map_C, Int.coe_castRingHom, Int.cast_natCast,
    eval_mul, eval_C, eval_comp, eval_X, eval_map]
  ring

lemma high_derivative_polynomial (a : ℤ) (Q : ℤ[X]) (p r : ℕ)
    (hp : 0 < p) (hr : p ≤ r) :
    ∃ A : ℤ[X], ∀ z : ℂ,
      (derivative^[r] (f a Q p)).eval z =
        (p : ℂ) * A.eval₂ (Int.castRingHom ℂ) ((a : ℂ) * z) := by
  obtain ⟨t, ht⟩ := factorial_multiple p r hp hr
  refine ⟨C (a ^ r * (t : ℤ)) * hasseDeriv r (H Q p), ?_⟩
  intro z
  rw [derivative_eval, ht]
  simp only [Nat.cast_mul, eval₂_mul, eval₂_C, Int.coe_castRingHom,
    Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  have hf : (Nat.factorial (p - 1) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (p - 1)
  field_simp

lemma derivative_at_zero (a : ℤ) (Q : ℤ[X]) (p r : ℕ) :
    (derivative^[r] (f a Q p)).eval 0 =
      (a : ℂ) ^ r * (Nat.factorial r : ℂ) / (Nat.factorial (p - 1) : ℂ) *
        ((H Q p).coeff r : ℂ) := by
  rw [derivative_eval, mul_zero, ← eval_map, ← coeff_zero_eq_eval_zero, coeff_map, hasseDeriv_coeff]
  simp

lemma low_derivative_zero (a : ℤ) (Q : ℤ[X]) (p r : ℕ) (hr : r < p - 1) :
    (derivative^[r] (f a Q p)).eval 0 = 0 := by
  rw [derivative_at_zero]
  simp [H, coeff_X_pow_mul', Nat.not_le.mpr hr]

lemma first_derivative_zero (a : ℤ) (Q : ℤ[X]) (p : ℕ) :
    (derivative^[p - 1] (f a Q p)).eval 0 =
      ((a ^ (p - 1) * Q.coeff 0 ^ p : ℤ) : ℂ) := by
  rw [derivative_at_zero]
  have hf : (Nat.factorial (p - 1) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (p - 1)
  simp [H, coeff_X_pow_mul', mul_div_cancel_right₀ _ hf, coeff_zero_eq_eval_zero]

lemma derivative_vanish_of_power {P : ℂ[X]} {z : ℂ} {s r : ℕ}
    (hd : (X - C z) ^ s ∣ P) (hr : r < s) :
    (derivative^[r] P).eval z = 0 := by
  have hlin : X - C z ∣ (X - C z) ^ (s - r) := by
    simpa only [pow_one] using pow_dvd_pow (X - C z) (show 1 ≤ s - r by omega)
  exact dvd_iff_isRoot.mp (dvd_trans hlin
    (pow_sub_dvd_iterate_derivative_of_pow_dvd r hd))

lemma root_power_divides (m : ℕ) (β : Fin m → ℂ) (a : ℤ) (Q : ℤ[X]) (p : ℕ)
    (hQ : Q.map (Int.castRingHom ℂ) = ∏ j, (X - C ((a : ℂ) * β j))) (j : Fin m) :
    (X - C ((a : ℂ) * β j)) ^ p ∣ (H Q p).map (Int.castRingHom ℂ) := by
  classical
  rw [H, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_pow, hQ]
  exact dvd_mul_of_dvd_right
    (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) p) _

lemma low_derivative_root (m : ℕ) (β : Fin m → ℂ) (a : ℤ) (Q : ℤ[X]) (p r : ℕ)
    (hQ : Q.map (Int.castRingHom ℂ) = ∏ j, (X - C ((a : ℂ) * β j)))
    (j : Fin m) (hr : r < p) :
    (derivative^[r] (f a Q p)).eval (β j) = 0 := by
  have hd := derivative_vanish_of_power (root_power_divides m β a Q p hQ j) hr
  rw [iterate_derivative_map, factorial_derivative] at hd
  simp only [Polynomial.map_mul, map_C, Int.coe_castRingHom, Int.cast_natCast,
    eval_mul, eval_C, eval_map] at hd
  have hf : (Nat.factorial r : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hz := (mul_eq_zero.mp hd).resolve_left hf
  rw [derivative_eval, hz, mul_zero]

lemma auxiliary_degree (m : ℕ) (β : Fin m → ℂ) (a : ℤ) (Q : ℤ[X])
    (hmonic : Q.Monic) (p : ℕ) (hp : 0 < p)
    (hQ : Q.map (Int.castRingHom ℂ) = ∏ j, (X - C ((a : ℂ) * β j))) :
    (H Q p).natDegree = N m p := by
  classical
  have hdeg : Q.natDegree = m := by
    rw [← hmonic.natDegree_map (Int.castRingHom ℂ), hQ,
      natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Nat.cast_id]
  rw [H, natDegree_mul (pow_ne_zero (p - 1) (X_ne_zero : (X : ℤ[X]) ≠ 0)) (pow_ne_zero _ hmonic.ne_zero),
    natDegree_X_pow, natDegree_pow, hdeg]
  simp only [N, Nat.add_mul, Nat.one_mul, Nat.mul_comm m p]
  omega

lemma root_multiplicity_bound (m : ℕ) (β : Fin m → ℂ) (a : ℤ) (Q : ℤ[X])
    (hmonic : Q.Monic) (p : ℕ)
    (hQ : Q.map (Int.castRingHom ℂ) = ∏ j, (X - C ((a : ℂ) * β j))) (j : Fin m) :
    p ≤ ((H Q p).map (Int.castRingHom ℂ)).rootMultiplicity ((a : ℂ) * β j) := by
  have hm : (H Q p).Monic := (monic_X_pow (p - 1)).mul (hmonic.pow p)
  exact (le_rootMultiplicity_iff (hm.map (Int.castRingHom ℂ)).ne_zero).mpr
    (root_power_divides m β a Q p hQ j)

theorem derivative_arithmetic : DerivativeArithmetic := by
  intro m β a Q p _ hmonic _ hp hQ
  exact ⟨auxiliary_degree m β a Q hmonic p hp.pos hQ,
    root_power_divides m β a Q p hQ, root_multiplicity_bound m β a Q hmonic p hQ,
    low_derivative_zero a Q p,
    first_derivative_zero a Q p,
    fun j r hr => low_derivative_root m β a Q p r hQ j hr,
    fun r hr => high_derivative_polynomial a Q p r hp.pos hr⟩

lemma zero_congruence (m : ℕ) (a : ℤ) (Q : ℤ[X]) (p : ℕ) (hp : 0 < p) :
    ∃ u : ℤ, (F a Q m p).eval 0 = (u : ℂ) ∧
      (p : ℤ) ∣ u - a ^ (p - 1) * Q.coeff 0 ^ p := by
  classical
  let b : ℤ := a ^ (p - 1) * Q.coeff 0 ^ p
  have ht (r : ℕ) : ∃ z : ℤ,
      (derivative^[r] (f a Q p)).eval 0 =
        (if r = p - 1 then (b : ℂ) else 0) + (p : ℂ) * z := by
    by_cases heq : r = p - 1
    · refine ⟨0, ?_⟩
      subst r
      simpa only [ite_true, Int.cast_zero, mul_zero, add_zero] using first_derivative_zero a Q p
    · by_cases hlt : r < p - 1
      · exact ⟨0, by simp [heq, low_derivative_zero a Q p r hlt]⟩
      · have hr : p ≤ r := by omega
        obtain ⟨A, hA⟩ := high_derivative_polynomial a Q p r hp hr
        refine ⟨A.eval 0, ?_⟩
        rw [hA]
        simp only [heq, ite_false, zero_add, mul_zero]
        have he := eval₂_at_apply (p := A) (Int.castRingHom ℂ) (0 : ℤ)
        simpa using congrArg (fun x : ℂ => (p : ℂ) * x) he
  choose z hz using ht
  let v : ℤ := ∑ r ∈ Finset.range (N m p + 1), z r
  refine ⟨b + p * v, ?_, ?_⟩
  · have hbnd : p - 1 ∈ Finset.range (N m p + 1) := by
      rw [Finset.mem_range]
      have hmul : p ≤ (m + 1) * p := by nlinarith
      unfold N
      omega
    simp only [F, eval_finsetSum]
    simp_rw [hz]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left hbnd, ← Finset.mul_sum]
    simp [v]
  · dsimp [b]
    simp only [add_sub_cancel_left]
    exact dvd_mul_right _ _

lemma root_sum_multiple (m : ℕ) (β : Fin m → ℂ) (a : ℤ) (Q : ℤ[X]) (p : ℕ)
    (hp : 0 < p)
    (hQ : Q.map (Int.castRingHom ℂ) = ∏ j, (X - C ((a : ℂ) * β j))) :
    ∃ v : ℤ, ∑ j, (F a Q m p).eval (β j) = ((p : ℤ) * v : ℤ) := by
  classical
  have ht (r : ℕ) : ∃ z : ℤ,
      ∑ j, (derivative^[r] (f a Q p)).eval (β j) = (p : ℂ) * z := by
    by_cases hr : r < p
    · exact ⟨0, by simp [fun j => low_derivative_root m β a Q p r hQ j hr]⟩
    · obtain ⟨A, hA⟩ := high_derivative_polynomial a Q p r hp (Nat.le_of_not_gt hr)
      obtain ⟨z, hz⟩ := IntegerPowerSums.polynomial_sums_integral m
        (fun j => (a : ℂ) * β j) Q hQ A
      exact ⟨z, by simp_rw [hA, ← Finset.mul_sum, hz]⟩
  choose z hz using ht
  refine ⟨∑ r ∈ Finset.range (N m p + 1), z r, ?_⟩
  simp only [F, eval_finsetSum]
  rw [Finset.sum_comm]
  simp_rw [hz]
  simp only [← Finset.mul_sum, Int.cast_mul, Int.cast_natCast, Int.cast_sum]

lemma residue_nonzero (k a q : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hn : ¬ (p : ℤ) ∣ k * a * q) :
    ¬ (p : ℤ) ∣ k * a ^ (p - 1) * q ^ p := by
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro hd
  rcases hprime.dvd_mul.mp hd with hka | hq
  · rcases hprime.dvd_mul.mp hka with hk | ha
    · exact hn (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hk _) _)
    · exact hn (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hprime.dvd_of_dvd_pow ha) _) _)
  · exact hn (dvd_mul_of_dvd_right (hprime.dvd_of_dvd_pow hq) _)

theorem integrality_congruences : IntegralityCongruences := by
  intro m β k a Q p _ _ _ _ hp hn hQ
  obtain ⟨u, hu, huc⟩ := zero_congruence m a Q p hp.pos
  obtain ⟨v, hv⟩ := root_sum_multiple m β a Q p hp.pos hQ
  have hJ : J β k a Q p = ((k * u + p * v : ℤ) : ℂ) := by
    simp only [J, hu, hv, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  have hc : (p : ℤ) ∣ (k * u + p * v) - k * a ^ (p - 1) * Q.coeff 0 ^ p := by
    convert dvd_add (dvd_mul_of_dvd_right huc k) (dvd_mul_right (p : ℤ) v) using 1; ring
  have hnd : ¬ (p : ℤ) ∣ (k * u + p * v) := by
    intro hd
    apply residue_nonzero k a (Q.coeff 0) p hp hn
    convert dvd_sub hd hc using 1; ring
  have hne : k * u + (p : ℤ) * v ≠ 0 := fun hz => hnd (hz ▸ dvd_zero _)
  refine ⟨⟨u, hu, huc⟩, ⟨v, hv⟩, k * u + p * v, hJ, hc, hnd, hne, ?_⟩
  rw [hJ, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hne

end D07.Appendix.LindemannRelationFactorialIntegralityCongruence
