import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.LegendreBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Approximation.IntervalPolynomials
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Rodrigues' Legendre polynomials, paper.tex:15898–15923.

The algebraic derivative is identified with `iteratedDeriv`. Endpoint divisibility
makes every integration-by-parts boundary term zero. The resulting integral
identity proves orthogonality; the beta-integral recurrence and the leading
coefficient give the exact norm. Polynomial sequences span the polynomial ring.
Uniform approximation on the closed interval, followed by the finite-measure
L² bound and density of bounded continuous functions, proves completeness on
the open interval. The final witnesses cover both real and complex scalars.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped ENNReal Topology BoundedContinuousFunction

namespace ExpandedFA.Models.LegendreBasis
open ExpandedFA.Models.LegendreBasisSpec

lemma iteratedDeriv_eval (p : Polynomial ℝ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => p.eval x) =
      fun x => (Polynomial.derivative^[n] p).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    simp only [Function.iterate_succ_apply', Polynomial.deriv]

theorem rodrigues_formula : RodriguesFormula := by
  intro n x
  have h := congrFun (iteratedDeriv_eval ((X ^ 2 - 1) ^ n) n) x
  simpa [legendre] using congrArg ((2 ^ n * (n.factorial : ℝ))⁻¹ * ·) h.symm

/-- The endpoint vanishing needed for all n integrations by parts, including
order zero. The source's phrase "first n-1 derivatives" includes these values. -/
lemma endpoint_vanishing (n k : ℕ) (hk : k < n) (x : ℝ)
    (hx : x = -1 ∨ x = 1) :
    (Polynomial.derivative^[k] ((X ^ 2 - 1 : Polynomial ℝ) ^ n)).eval x = 0 := by
  obtain ⟨q, hq⟩ := pow_sub_dvd_iterate_derivative_pow (X ^ 2 - 1 : Polynomial ℝ) n k
  rw [hq, eval_mul, eval_pow]
  have hx' : x ^ 2 - 1 = 0 := by rcases hx with rfl | rfl <;> norm_num
  simp [hx', Nat.sub_ne_zero_of_lt hk]

/-- One integration by parts for polynomial factors. -/
lemma integral_mul_derivative (p q : Polynomial ℝ) (a b : ℝ) :
    (∫ x in a..b, p.eval x * q.derivative.eval x) =
      p.eval b * q.eval b - p.eval a * q.eval a -
        ∫ x in a..b, p.derivative.eval x * q.eval x := by
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    p.continuous.continuousOn q.continuous.continuousOn
    (fun x _ => p.hasDerivAt x) (fun x _ => q.hasDerivAt x)
    (p.derivative.continuous.intervalIntegrable a b)
    (q.derivative.continuous.intervalIntegrable a b)

/-- Repeated integration by parts, with every boundary term explicitly zero. -/
lemma integral_iterated_derivative_mul (p q : Polynomial ℝ) (n : ℕ)
    (h : ∀ k < n, (Polynomial.derivative^[k] p).eval (-1) = 0 ∧
      (Polynomial.derivative^[k] p).eval 1 = 0) :
    (∫ x in (-1 : ℝ)..1, (Polynomial.derivative^[n] p).eval x * q.eval x) =
      (-1 : ℝ)^n * ∫ x in (-1 : ℝ)..1,
        p.eval x * (Polynomial.derivative^[n] q).eval x := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    have hn := h n (Nat.lt_succ_self n)
    have hi := integral_mul_derivative q (Polynomial.derivative^[n] p) (-1) 1
    simp only [hn.1, hn.2, mul_zero, sub_self, zero_sub] at hi
    calc
      _ = -(∫ x in (-1 : ℝ)..1,
          (Polynomial.derivative^[n] p).eval x * q.derivative.eval x) := by
        simpa only [Function.iterate_succ_apply', mul_comm] using hi
      _ = -((-1 : ℝ)^n * ∫ x in (-1 : ℝ)..1,
          p.eval x * (Polynomial.derivative^[n] q.derivative).eval x) := by
        rw [ih q.derivative (fun k hk => h k (Nat.lt_succ_of_lt hk))]
      _ = _ := by
        rw [Function.iterate_succ_apply, pow_succ]
        ring

lemma legendre_mul_integral (n : ℕ) (q : Polynomial ℝ) :
    (∫ x in (-1 : ℝ)..1, (legendre n).eval x * q.eval x) =
      (2 ^ n * (n.factorial : ℝ))⁻¹ * (-1 : ℝ)^n *
        ∫ x in (-1 : ℝ)..1, (x ^ 2 - 1)^n *
          (Polynomial.derivative^[n] q).eval x := by
  simp only [legendre, eval_mul, eval_C, mul_assoc,
    intervalIntegral.integral_const_mul]
  rw [integral_iterated_derivative_mul]
  · simp [eval_pow, eval_sub, eval_X, eval_one, mul_assoc]
  · intro k hk
    exact ⟨endpoint_vanishing n k hk (-1) (Or.inl rfl),
      endpoint_vanishing n k hk 1 (Or.inr rfl)⟩

lemma integral_legendre_mul_of_degree_lt (n : ℕ) (q : Polynomial ℝ)
    (hq : q.natDegree < n) :
    (∫ x in (-1 : ℝ)..1, (legendre n).eval x * q.eval x) = 0 := by
  rw [legendre_mul_integral, iterate_derivative_eq_zero hq]
  simp

lemma base_natDegree (n : ℕ) :
    ((X ^ 2 - 1 : Polynomial ℝ) ^ n).natDegree = 2 * n := by
  rw [natDegree_pow, ← map_one C, natDegree_X_pow_sub_C, Nat.mul_comm]

lemma legendre_natDegree_le (n : ℕ) : (legendre n).natDegree ≤ n := by
  refine (natDegree_C_mul_le _ _).trans ?_
  have h := natDegree_iterate_derivative ((X ^ 2 - 1 : Polynomial ℝ) ^ n) n
  rw [base_natDegree] at h
  convert h using 1; omega

theorem orthogonality : Orthogonality := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · simpa only [mul_comm] using integral_legendre_mul_of_degree_lt n (legendre m)
      ((legendre_natDegree_le m).trans_lt h)
  · exact integral_legendre_mul_of_degree_lt m (legendre n)
      ((legendre_natDegree_le n).trans_lt h)

lemma base_top_coeff (n : ℕ) :
    ((X ^ 2 - 1 : Polynomial ℝ) ^ n).coeff (2 * n) = 1 := by
  have h := coeff_pow_mul_natDegree (X ^ 2 - 1 : Polynomial ℝ) n
  have hm : (X ^ 2 - 1 : Polynomial ℝ).Monic := monic_X_pow_sub_one (by decide)
  rw [hm.leadingCoeff, one_pow] at h
  simpa only [← map_one C, natDegree_X_pow_sub_C, Nat.mul_comm n 2] using h

lemma legendre_top_coeff (n : ℕ) :
    (legendre n).coeff n =
      (2 ^ n * (n.factorial : ℝ))⁻¹ * ((2 * n).descFactorial n : ℝ) := by
  simp only [legendre, coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul,
    ← two_mul, base_top_coeff, mul_one]

lemma legendre_top_coeff_pos (n : ℕ) : 0 < (legendre n).coeff n := by
  rw [legendre_top_coeff]
  have h : 0 < (2 * n).descFactorial n := Nat.descFactorial_pos.mpr (by omega)
  positivity

lemma legendre_degree (n : ℕ) : (legendre n).degree = n := by
  exact degree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_degree_le.mp (legendre_natDegree_le n))
    (ne_of_gt (legendre_top_coeff_pos n))

lemma derivative_top_eq_constant (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n) :
    Polynomial.derivative^[n] p = C ((n.factorial : ℝ) * p.coeff n) := by
  have hd : (Polynomial.derivative^[n] p).natDegree = 0 := by
    have := natDegree_iterate_derivative p n
    omega
  rw [eq_C_of_natDegree_eq_zero hd]
  simp [coeff_iterate_derivative, nsmul_eq_mul, Nat.descFactorial_self]

lemma integral_derivative (p : Polynomial ℝ) (a b : ℝ) :
    (∫ x in a..b, p.derivative.eval x) = p.eval b - p.eval a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => p.hasDerivAt x) (p.derivative.continuous.intervalIntegrable a b)

/-- The elementary beta integral used in the exact normalization. -/
def betaIntegral (n : ℕ) : ℝ := ∫ x in (-1 : ℝ)..1, (1 - x^2)^n

lemma betaIntegral_zero : betaIntegral 0 = 2 := by
  norm_num [betaIntegral]

lemma betaIntegral_recurrence (n : ℕ) :
    (2 * (n : ℝ) + 3) * betaIntegral (n+1) =
      (2 * ((n : ℝ) + 1)) * betaIntegral n := by
  let p : Polynomial ℝ := X * (1 - X^2)^(n+1)
  have hd : p.derivative = C (2 * (n : ℝ) + 3) * (1-X^2)^(n+1) -
      C (2 * ((n : ℝ) + 1)) * (1-X^2)^n := by
    dsimp [p]
    simp only [derivative_mul, derivative_X, one_mul, derivative_pow_succ,
      derivative_sub, derivative_one, Nat.cast_one, pow_one]
    rw [pow_succ]
    simp only [map_add, map_mul, map_ofNat, map_one]
    ring
  have hi := integral_derivative p (-1) 1
  have hzero : p.eval 1 - p.eval (-1) = 0 := by simp [p]
  rw [hzero, hd] at hi
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_one, eval_X] at hi
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hi
  · exact sub_eq_zero.mp hi
  · exact ((continuous_const.sub (continuous_id.pow 2)).pow (n+1)).const_mul _
      |>.intervalIntegrable (-1) 1
  · exact ((continuous_const.sub (continuous_id.pow 2)).pow n).const_mul _
      |>.intervalIntegrable (-1) 1

lemma betaIntegral_factorial (n : ℕ) :
    ((2*n+1).factorial : ℝ) * betaIntegral n =
      2^(2*n+1) * (n.factorial : ℝ)^2 := by
  induction n with
  | zero => norm_num [betaIntegral_zero]
  | succ n ih =>
    have hf : ((2*(n+1)+1).factorial : ℝ) =
        (2*(n : ℝ)+3) * (2*(n : ℝ)+2) * ((2*n+1).factorial : ℝ) := by
      rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [hf]
    calc
      _ = (2*(n : ℝ)+2) * ((2*n+1).factorial : ℝ) *
          ((2*(n : ℝ)+3) * betaIntegral (n+1)) := by ring
      _ = (2*(n : ℝ)+2) * ((2*n+1).factorial : ℝ) *
          (2*((n : ℝ)+1) * betaIntegral n) := by rw [betaIntegral_recurrence]
      _ = 4 * ((n : ℝ)+1)^2 *
          (((2*n+1).factorial : ℝ) * betaIntegral n) := by ring
      _ = _ := by
        rw [ih, Nat.factorial_succ,
          show 2*(n+1)+1 = (2*n+1)+2 by omega, pow_add]
        push_cast
        ring

lemma legendre_top_coeff_factorial (n : ℕ) :
    (legendre n).coeff n = ((2*n).factorial : ℝ) /
      (2^n * (n.factorial : ℝ)^2) := by
  have h := Nat.factorial_mul_descFactorial (show n ≤ 2*n by omega)
  have h' : (n.factorial : ℝ) * ((2*n).descFactorial n : ℝ) =
      ((2*n).factorial : ℝ) := by
    exact_mod_cast (show n.factorial * (2*n).descFactorial n = (2*n).factorial by
      simpa [show 2*n-n = n by omega] using h)
  rw [legendre_top_coeff]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have htwo : (2 : ℝ)^n ≠ 0 := by positivity
  field_simp
  nlinarith

lemma legendre_sq_integral_beta (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, ((legendre n).eval x)^2) =
      (legendre n).coeff n / 2^n * betaIntegral n := by
  have h := legendre_mul_integral n (legendre n)
  rw [derivative_top_eq_constant _ n (legendre_natDegree_le n)] at h
  simp only [eval_C, intervalIntegral.integral_mul_const] at h
  have hi : (∫ x in (-1 : ℝ)..1, (x^2-1)^n) = (-1 : ℝ)^n * betaIntegral n := by
    rw [betaIntegral, ← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    rw [← mul_pow]
    congr 1
    ring
  rw [hi] at h
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have htwo : (2 : ℝ)^n ≠ 0 := by positivity
  have hsign : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by
    rw [← mul_pow]; norm_num
  calc
    _ = (2^n * (n.factorial : ℝ))⁻¹ * (-1 : ℝ)^n *
        (((-1 : ℝ)^n * betaIntegral n) *
          ((n.factorial : ℝ) * (legendre n).coeff n)) := by
      simpa only [pow_two] using h
    _ = (2^n * (n.factorial : ℝ))⁻¹ * (n.factorial : ℝ) *
        (legendre n).coeff n * betaIntegral n *
        ((-1 : ℝ)^n * (-1 : ℝ)^n) := by ring
    _ = _ := by rw [hsign]; field_simp

theorem squared_norm : SquaredNorm := by
  intro n
  rw [legendre_sq_integral_beta, legendre_top_coeff_factorial]
  have hb := betaIntegral_factorial n
  rw [Nat.factorial_succ] at hb
  push_cast at hb
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hf : ((2*n).factorial : ℝ) ≠ 0 := by positivity
  have htwo : (2 : ℝ)^n ≠ 0 := by positivity
  have hodd : 2*(n : ℝ)+1 ≠ 0 := by positivity
  rw [pow_succ, show (2 : ℝ)^(2*n) = (2^n)^2 by
    rw [Nat.mul_comm 2 n, pow_mul]] at hb
  field_simp
  nlinarith [hb]

section Scalar
variable (𝕜 : Type*) [RCLike 𝕜]

lemma polynomialL2_ae (p : Polynomial 𝕜) :
    polynomialL2 𝕜 p =ᵐ[intervalMeasure] (fun x : ℝ => p.eval (x : 𝕜)) :=
  MemLp.coeFn_toLp _

lemma mapped_eval (p : Polynomial ℝ) (x : ℝ) :
    (p.map (algebraMap ℝ 𝕜)).eval (x : 𝕜) = ((p.eval x : ℝ) : 𝕜) :=
  Polynomial.eval_map_apply (algebraMap ℝ 𝕜) x

lemma polynomialL2_inner_real (p q : Polynomial ℝ) :
    inner 𝕜 (polynomialL2 𝕜 (p.map (algebraMap ℝ 𝕜)))
      (polynomialL2 𝕜 (q.map (algebraMap ℝ 𝕜))) =
      ((∫ x in (-1 : ℝ)..1, p.eval x * q.eval x) : ℝ) := by
  rw [L2.inner_def]
  have h : (∫ x : ℝ, inner 𝕜
      (polynomialL2 𝕜 (p.map (algebraMap ℝ 𝕜)) x)
      (polynomialL2 𝕜 (q.map (algebraMap ℝ 𝕜)) x) ∂intervalMeasure) =
      ∫ x : ℝ, ((p.eval x * q.eval x : ℝ) : 𝕜) ∂intervalMeasure := by
    apply integral_congr_ae
    filter_upwards [polynomialL2_ae 𝕜 (p.map (algebraMap ℝ 𝕜)),
      polynomialL2_ae 𝕜 (q.map (algebraMap ℝ 𝕜))] with x hp hq
    rw [hp, hq, mapped_eval, mapped_eval]
    simp [RCLike.inner_apply, mul_comm]
  rw [h, integral_ofReal]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]

lemma squared_l2_norm_scalar (n : ℕ) :
    ‖polynomialL2 𝕜 ((legendre n).map (algebraMap ℝ 𝕜))‖^2 =
      2/(2*(n : ℝ)+1) := by
  rw [@norm_sq_eq_re_inner 𝕜, polynomialL2_inner_real, RCLike.ofReal_re]
  simpa only [pow_two] using squared_norm n

lemma normalized_inner (m n : ℕ) :
    inner 𝕜 (normalizedL2 𝕜 m) (normalizedL2 𝕜 n) =
      if m = n then 1 else 0 := by
  simp only [normalizedL2, inner_smul_left, inner_smul_right,
    polynomialL2_inner_real, RCLike.conj_ofReal]
  split_ifs with h
  · subst n
    have hs := squared_norm m
    have hsq := Real.sq_sqrt (show 0 ≤ (((2*m+1 : ℕ) : ℝ)/2) by positivity)
    have hd : 2*(m : ℝ)+1 ≠ 0 := by positivity
    rw [show (∫ x in (-1 : ℝ)..1, (legendre m).eval x * (legendre m).eval x) =
      2/(2*(m : ℝ)+1) by simpa [pow_two] using hs]
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul]
    norm_cast
    push_cast at hsq
    push_cast
    rw [← mul_assoc, ← pow_two, hsq]
    field_simp
  · rw [orthogonality m n h]
    simp

theorem normalized_orthonormal_scalar : Orthonormal 𝕜 (normalizedL2 𝕜) := by
  exact orthonormal_iff_ite.mpr (normalized_inner 𝕜)

/-- The polynomial embedding respects the scalar vector-space operations. -/
def polynomialL2Linear : Polynomial 𝕜 →ₗ[𝕜] intervalL2 𝕜 where
  toFun := polynomialL2 𝕜
  map_add' p q := by
    apply Lp.ext
    filter_upwards [polynomialL2_ae 𝕜 (p+q), polynomialL2_ae 𝕜 p,
      polynomialL2_ae 𝕜 q, Lp.coeFn_add (polynomialL2 𝕜 p) (polynomialL2 𝕜 q)]
      with x hpq hp hq ha
    simp only [hpq, ha, Pi.add_apply, hp, hq, eval_add]
  map_smul' c p := by
    apply Lp.ext
    filter_upwards [polynomialL2_ae 𝕜 (c • p), polynomialL2_ae 𝕜 p,
      Lp.coeFn_smul c (polynomialL2 𝕜 p)] with x hcp hp hs
    simp only [RingHom.id_apply, hcp, hs, Pi.smul_apply, hp, eval_smul]

/-- Nonzero leading coefficients give a polynomial basis over either scalar field. -/
def legendreSequence : Polynomial.Sequence 𝕜 where
  elems' n := (legendre n).map (algebraMap ℝ 𝕜)
  degree_eq' n := by rw [Polynomial.degree_map, legendre_degree]

lemma polynomialL2_mem_span (p : Polynomial 𝕜) :
    polynomialL2 𝕜 p ∈ Submodule.span 𝕜 (Set.range (normalizedL2 𝕜)) := by
  let S := Submodule.span 𝕜 (Set.range (normalizedL2 𝕜))
  have hspan := (legendreSequence 𝕜).span (fun n =>
    isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr ((legendreSequence 𝕜).ne_zero n)))
  have hle : ⊤ ≤ S.comap (polynomialL2Linear 𝕜) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro q ⟨n, rfl⟩
    change polynomialL2 𝕜 ((legendre n).map (algebraMap ℝ 𝕜)) ∈ S
    have hm : normalizedL2 𝕜 n ∈ S := Submodule.subset_span ⟨n, rfl⟩
    have hc : (Real.sqrt (((2*n+1 : ℕ) : ℝ)/2) : 𝕜) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity :
        0 < (((2*n+1 : ℕ) : ℝ)/2))))
    have heq : polynomialL2 𝕜 ((legendre n).map (algebraMap ℝ 𝕜)) =
        (Real.sqrt (((2*n+1 : ℕ) : ℝ)/2) : 𝕜)⁻¹ • normalizedL2 𝕜 n := by
      simp only [normalizedL2, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [heq]
    exact S.smul_mem _ hm
  exact hle (Submodule.mem_top : p ∈ (⊤ : Submodule 𝕜 (Polynomial 𝕜)))

/-- Real and imaginary parts reduce uniform approximation to the accepted
real interval approximation theorem, also when the scalar field is ℝ. -/
lemma exists_polynomial_near (f : C(Set.Icc (-1 : ℝ) 1, 𝕜))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial 𝕜, ∀ x : Set.Icc (-1 : ℝ) 1,
      ‖p.eval (x : 𝕜) - f x‖ < ε := by
  let fr : C(Set.Icc (-1 : ℝ) 1, ℝ) :=
    ⟨fun x => RCLike.re (f x), RCLike.continuous_re.comp f.continuous⟩
  let fi : C(Set.Icc (-1 : ℝ) 1, ℝ) :=
    ⟨fun x => RCLike.im (f x), RCLike.continuous_im.comp f.continuous⟩
  obtain ⟨p, hp⟩ := ExpandedFA.Approximation.IntervalPolynomials.exists_real_polynomial_near
    (-1) 1 fr (ε/2) (half_pos hε)
  obtain ⟨q, hq⟩ := ExpandedFA.Approximation.IntervalPolynomials.exists_real_polynomial_near
    (-1) 1 fi (ε/2) (half_pos hε)
  refine ⟨p.map (algebraMap ℝ 𝕜) + q.map (algebraMap ℝ 𝕜) * C RCLike.I, fun x => ?_⟩
  simp only [eval_add, eval_mul, eval_C, mapped_eval]
  have heq : ((p.eval (x : ℝ) : ℝ) : 𝕜) +
      ((q.eval (x : ℝ) : ℝ) : 𝕜) * RCLike.I - f x =
      ((p.eval (x : ℝ) - RCLike.re (f x) : ℝ) : 𝕜) +
        ((q.eval (x : ℝ) - RCLike.im (f x) : ℝ) : 𝕜) * RCLike.I := by
    rw [RCLike.ofReal_sub, RCLike.ofReal_sub]
    linear_combination (RCLike.re_add_im (f x))
  rw [heq]
  have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by rw [RCLike.norm_I]; split_ifs <;> norm_num
  calc
    _ ≤ ‖((p.eval (x : ℝ) - RCLike.re (f x) : ℝ) : 𝕜)‖ +
        ‖((q.eval (x : ℝ) - RCLike.im (f x) : ℝ) : 𝕜) * RCLike.I‖ := norm_add_le _ _
    _ ≤ |p.eval (x : ℝ) - RCLike.re (f x)| +
        |q.eval (x : ℝ) - RCLike.im (f x)| := by
      rw [norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal]
      exact add_le_add_right (mul_le_of_le_one_right (abs_nonneg _) hI) _
    _ < ε := by
      have hr := hp x
      have hi := hq x
      simp only [Real.norm_eq_abs, fr, fi, ContinuousMap.coe_mk] at hr hi
      linarith

lemma polynomialL2_denseRange : DenseRange (polynomialL2 𝕜) := by
  have hbc : DenseRange (BoundedContinuousFunction.toLp 2 intervalMeasure 𝕜 :
      (ℝ →ᵇ 𝕜) →L[𝕜] intervalL2 𝕜) :=
    BoundedContinuousFunction.toLp_denseRange 𝕜 intervalMeasure 𝕜 (by norm_num)
  have hmem (f : ℝ →ᵇ 𝕜) : BoundedContinuousFunction.toLp 2 intervalMeasure 𝕜 f ∈
      closure (Set.range (polynomialL2 𝕜)) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let K : ℝ := (measureUnivNNReal intervalMeasure : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹
    have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
    let δ := ε/(K+1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    let fc : C(Set.Icc (-1 : ℝ) 1, 𝕜) :=
      ⟨fun x => f (x : ℝ), f.continuous.comp continuous_subtype_val⟩
    obtain ⟨p, hp⟩ := exists_polynomial_near 𝕜 fc δ hδ
    refine ⟨polynomialL2 𝕜 p, ⟨p, rfl⟩, ?_⟩
    rw [dist_comm, dist_eq_norm]
    have hnorm : ‖polynomialL2 𝕜 p - BoundedContinuousFunction.toLp 2 intervalMeasure 𝕜 f‖ ≤
        K * δ := by
      apply Lp.norm_le_of_ae_bound hδ.le
      filter_upwards [Lp.coeFn_sub (polynomialL2 𝕜 p)
        (BoundedContinuousFunction.toLp 2 intervalMeasure 𝕜 f), polynomialL2_ae 𝕜 p,
        f.coeFn_toLp 2 intervalMeasure 𝕜, ae_restrict_mem measurableSet_Ioo]
        with x hsub hp' hf hx
      rw [hsub, Pi.sub_apply, hp', hf]
      exact (hp ⟨x, hx.1.le, hx.2.le⟩).le
    apply hnorm.trans_lt
    have he : δ * (K+1) = ε := div_mul_cancel₀ ε (by positivity : K+1 ≠ 0)
    nlinarith
  intro f
  exact closure_minimal (Set.range_subset_iff.mpr hmem) isClosed_closure (hbc f)

lemma complete_span_scalar :
    (Submodule.span 𝕜 (Set.range (normalizedL2 𝕜))).topologicalClosure = ⊤ := by
  apply top_unique
  intro f _
  exact closure_minimal
    (Set.range_subset_iff.mpr (fun p =>
      (Submodule.span 𝕜 (Set.range (normalizedL2 𝕜))).le_topologicalClosure
        (polynomialL2_mem_span 𝕜 p)))
    (Submodule.isClosed_topologicalClosure _) (polynomialL2_denseRange 𝕜 f)

end Scalar

theorem normalized_orthonormal : NormalizedOrthonormal := by
  intro 𝕜 _
  exact normalized_orthonormal_scalar 𝕜

theorem complete_span : CompleteSpan := by
  intro 𝕜 _
  exact complete_span_scalar 𝕜

theorem squared_l2_norm : SquaredL2Norm := by
  intro 𝕜 _ n
  exact squared_l2_norm_scalar 𝕜 n

theorem complete_basis : HilbertBasisExistence := by
  intro 𝕜 _
  let hv := normalized_orthonormal_scalar 𝕜
  have hsp := (complete_span_scalar 𝕜).ge
  refine ⟨HilbertBasis.mk hv hsp, ?_⟩
  intro n
  exact congrFun (HilbertBasis.coe_mk hv hsp) n

end ExpandedFA.Models.LegendreBasis
