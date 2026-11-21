import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.HermiteBasis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.L1FourierUniqueness

noncomputable section
open MeasureTheory Polynomial
open scoped ContDiff
namespace ExpandedFA.Models.HermiteBasis

@[simp] theorem physicistsHermite_zero : physicistsHermite 0 = 1 := rfl
@[simp] theorem physicistsHermite_succ (n : ℕ) :
    physicistsHermite (n+1) = 2 * X * physicistsHermite n - derivative (physicistsHermite n) := rfl

lemma gaussian_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y^2)))
      (-2 * x * Real.exp (-(x^2))) x := by
  convert (((hasDerivAt_id x).pow 2).neg.exp) using 1 <;> simp [Pi.pow_apply, Pi.neg_apply, id_eq] ; ring

lemma gaussian_deriv (x : ℝ) :
    deriv (fun y : ℝ => Real.exp (-(y^2))) x =
      -2 * x * Real.exp (-(x^2)) := (gaussian_hasDerivAt x).deriv

lemma iterated_deriv_gaussian (n : ℕ) :
    deriv^[n] (fun y : ℝ => Real.exp (-(y^2))) =
      fun x => (-1 : ℝ)^n * (physicistsHermite n).eval x * Real.exp (-(x^2)) := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    have hp := (physicistsHermite n).hasDerivAt x
    have hh := ((hp.const_mul ((-1 : ℝ)^n)).mul (gaussian_hasDerivAt x)).deriv
    change deriv ((fun y => (-1 : ℝ)^n * (physicistsHermite n).eval y) *
      fun y => Real.exp (-(y^2))) x = _
    rw [hh]
    simp only [physicistsHermite_succ, eval_sub, eval_mul, eval_ofNat, eval_X, pow_succ]
    ring

theorem rodrigues_identification : Spec.RodriguesIdentification := by
  intro n x
  unfold H
  rw [iterated_deriv_gaussian]
  have he : Real.exp (x^2) * Real.exp (-(x^2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hs : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by rw [← mul_pow]; simp
  calc
    _ = ((-1 : ℝ)^n * (-1 : ℝ)^n) *
        (Real.exp (x^2) * Real.exp (-(x^2))) * (physicistsHermite n).eval x := by ring
    _ = _ := by rw [he, hs]; ring

theorem normalization_positive : Spec.NormalizationPositive := by
  intro n
  exact Real.sqrt_pos.mpr (mul_pos (mul_pos (pow_pos (by norm_num) _)
    (by exact_mod_cast Nat.factorial_pos n)) (Real.sqrt_pos.mpr Real.pi_pos))

/-- The Appell derivative identity, in the physicists' convention. -/
lemma polynomial_derivative_succ (n : ℕ) :
    derivative (physicistsHermite (n+1)) =
      C (2 * (n+1 : ℝ)) * physicistsHermite n := by
  induction n with
  | zero => simp; exact (Polynomial.C_ofNat 2).symm
  | succ n ih =>
    rw [physicistsHermite_succ (n+1), derivative_sub, derivative_mul,
      derivative_mul, derivative_ofNat, derivative_X, ih]
    simp only [zero_mul, mul_one, zero_add]
    rw [derivative_mul, derivative_C, zero_mul, zero_add,
      physicistsHermite_succ n]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_ofNat, map_one]
    ring

lemma polynomial_differential_equation (n : ℕ) :
    derivative (derivative (physicistsHermite n)) -
      2 * X * derivative (physicistsHermite n) +
      C (2 * (n : ℝ)) * physicistsHermite n = 0 := by
  have hd := polynomial_derivative_succ n
  rw [physicistsHermite_succ, derivative_sub, derivative_mul,
    derivative_mul, derivative_ofNat, derivative_X] at hd
  simp only [zero_mul, mul_one, zero_add] at hd
  have hc : C (2 * (n+1 : ℝ)) = C (2 * (n : ℝ)) + 2 := by
    simp only [map_add, map_mul, map_ofNat, map_one]
    ring
  rw [hc] at hd
  linear_combination -hd

lemma h_polynomial (n : ℕ) :
    h n = fun x => Real.exp (-(x^2)/2) * (physicistsHermite n).eval x / normalization n := by
  funext x
  simp only [h]
  rw [rodrigues_identification n x]

theorem smooth : Spec.Smooth := by
  intro n
  rw [h_polynomial]
  exact ((Real.contDiff_exp.comp (((contDiff_id.pow 2).neg).div_const 2)).mul
    (by simpa only [Polynomial.coe_aeval_eq_eval] using
      (physicistsHermite n).contDiff_aeval (𝕜 := ℝ) (∞ : WithTop ℕ∞))).div_const _

lemma half_gaussian_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y^2)/2))
      (-x * Real.exp (-(x^2)/2)) x := by
  convert ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp) using 1 <;>
    simp [Pi.pow_apply, Pi.neg_apply, id_eq] ; ring

/-- Differentiating a polynomial times the half-scale Gaussian. -/
lemma gaussian_polynomial_hasDerivAt (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => Real.exp (-(y^2)/2) * P.eval y)
      (Real.exp (-(x^2)/2) * (P.derivative.eval x - x * P.eval x)) x := by
  convert (half_gaussian_hasDerivAt x).mul (P.hasDerivAt x) using 1; ring

lemma gaussian_polynomial_second_deriv (P : ℝ[X]) (x : ℝ) :
    deriv (deriv (fun y => Real.exp (-(y^2)/2) * P.eval y)) x =
      Real.exp (-(x^2)/2) *
        (P.derivative.derivative.eval x - 2*x*P.derivative.eval x + (x^2-1)*P.eval x) := by
  have hd : deriv (fun y => Real.exp (-(y^2)/2) * P.eval y) =
      fun y => Real.exp (-(y^2)/2) * (P.derivative - X * P).eval y := by
    funext y
    simpa only [eval_sub, eval_mul, eval_X] using (gaussian_polynomial_hasDerivAt P y).deriv
  rw [hd, (gaussian_polynomial_hasDerivAt (P.derivative - X * P) x).deriv]
  simp only [derivative_sub, derivative_mul, derivative_X, one_mul,
    eval_sub, eval_add, eval_mul, eval_X]
  ring

theorem differential_equation : Spec.DifferentialEquation := by
  intro n x
  rw [h_polynomial]
  have hdiff : Differentiable ℝ (fun y => Real.exp (-(y^2)/2) * (physicistsHermite n).eval y) :=
    fun y => (gaussian_polynomial_hasDerivAt (physicistsHermite n) y).differentiableAt
  have hdiff' : Differentiable ℝ (deriv (fun y =>
      Real.exp (-(y^2)/2) * (physicistsHermite n).eval y)) := by
    have hd : deriv (fun y => Real.exp (-(y^2)/2) * (physicistsHermite n).eval y) =
        fun y => Real.exp (-(y^2)/2) * ((physicistsHermite n).derivative - X * physicistsHermite n).eval y := by
      funext y
      simpa only [eval_sub, eval_mul, eval_X] using
        (gaussian_polynomial_hasDerivAt (physicistsHermite n) y).deriv
    rw [hd]
    exact fun y => (gaussian_polynomial_hasDerivAt _ y).differentiableAt
  have hd (y : ℝ) := (hdiff y).hasDerivAt.div_const (normalization n)
  have hd' : deriv (fun y => Real.exp (-(y^2)/2) * (physicistsHermite n).eval y / normalization n) =
      fun y => deriv (fun z => Real.exp (-(z^2)/2) * (physicistsHermite n).eval z) y / normalization n :=
    funext fun y => (hd y).deriv
  rw [hd', (hdiff' x).hasDerivAt.div_const (normalization n) |>.deriv,
    gaussian_polynomial_second_deriv]
  have he := congrArg (Polynomial.eval x) (polynomial_differential_equation n)
  simp only [eval_add, eval_sub, eval_mul, eval_ofNat, eval_X, eval_C, eval_zero] at he
  linear_combination -(Real.exp (-(x^2)/2) / normalization n) * he

/-- All polynomial Gaussian weights are integrable. -/
lemma polynomial_gaussian_integrable (P : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => P.eval x * Real.exp (-b*x^2)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    convert hP.add hQ using 1
    funext x
    simp [add_mul]
  | monomial k a =>
    have hi : Integrable (fun x : ℝ => x^k * Real.exp (-b*x^2)) := by
      simpa only [Real.rpow_natCast] using
        (integrable_rpow_mul_exp_neg_mul_sq hb (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (-1 : ℝ) < (k : ℝ)))
    simpa only [eval_monomial, mul_assoc] using hi.const_mul a

lemma polynomial_half_gaussian_memLp (P : ℝ[X]) :
    MemLp (fun x : ℝ => Real.exp (-(x^2)/2) * P.eval x) 2 volume := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert polynomial_gaussian_integrable (P*P) (b := 1) (by norm_num) using 1
  funext x
  simp only [eval_mul, neg_mul, one_mul]
  have he : Real.exp (-(x^2)/2)^2 = Real.exp (-(x^2)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, he]
  ring

theorem square_integrable : Spec.SquareIntegrable := by
  intro n
  rw [h_polynomial]
  simpa only [div_eq_mul_inv, mul_comm (normalization n)⁻¹] using
    (polynomial_half_gaussian_memLp (physicistsHermite n)).const_mul (normalization n)⁻¹

lemma weighted_integrable (P : ℝ[X]) :
    Integrable (fun x : ℝ => P.eval x * Real.exp (-(x^2))) := by
  simpa only [neg_mul, one_mul] using polynomial_gaussian_integrable P (b := 1) (by norm_num)

/-- The raising operator is the adjoint of polynomial differentiation in Gaussian weight. -/
lemma weighted_raising (P Q : ℝ[X]) :
    (∫ x : ℝ, P.eval x * (2*X*Q-Q.derivative).eval x * Real.exp (-(x^2))) =
      ∫ x : ℝ, P.derivative.eval x * Q.eval x * Real.exp (-(x^2)) := by
  have hv (x : ℝ) : HasDerivAt (fun y => Q.eval y * Real.exp (-(y^2)))
      (-(2*X*Q-Q.derivative).eval x * Real.exp (-(x^2))) x := by
    convert (Q.hasDerivAt x).mul (gaussian_hasDerivAt x) using 1
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    ring
  have h1 : Integrable (fun x : ℝ => P.eval x *
      (-(2*X*Q-Q.derivative).eval x * Real.exp (-(x^2)))) := by
    convert weighted_integrable (P * -(2*X*Q-Q.derivative)) using 1
    ext x
    simp only [eval_mul, eval_neg]
    ring
  have h2 : Integrable (fun x : ℝ => P.derivative.eval x *
      (Q.eval x * Real.exp (-(x^2)))) := by
    simpa only [eval_mul, mul_assoc] using weighted_integrable (P.derivative*Q)
  have h3 : Integrable (fun x : ℝ => P.eval x * (Q.eval x * Real.exp (-(x^2)))) := by
    simpa only [eval_mul, mul_assoc] using weighted_integrable (P*Q)
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => P.eval x) (v := fun x : ℝ => Q.eval x * Real.exp (-(x^2)))
    (u' := fun x : ℝ => P.derivative.eval x)
    (v' := fun x : ℝ => -(2*X*Q-Q.derivative).eval x * Real.exp (-(x^2)))
    (fun x _ => P.hasDerivAt x) (fun x _ => hv x) h1 h2 h3
  simp only [mul_neg, neg_mul, integral_neg, ← mul_assoc] at hi
  exact neg_injective hi

lemma weighted_hermite_zero_succ (m : ℕ) :
    (∫ x : ℝ, (physicistsHermite 0).eval x *
      (physicistsHermite (m+1)).eval x * Real.exp (-(x^2))) = 0 := by
  rw [physicistsHermite_succ, weighted_raising]
  simp

lemma weighted_hermite_succ_succ (n m : ℕ) :
    (∫ x : ℝ, (physicistsHermite (n+1)).eval x *
      (physicistsHermite (m+1)).eval x * Real.exp (-(x^2))) =
    (2 * (n+1 : ℝ)) * ∫ x : ℝ, (physicistsHermite n).eval x *
      (physicistsHermite m).eval x * Real.exp (-(x^2)) := by
  rw [physicistsHermite_succ m, weighted_raising, polynomial_derivative_succ]
  simp only [eval_mul, eval_C, mul_assoc, integral_const_mul]

/-- Exact Gaussian-weighted Gram matrix, including the diagonal constant. -/
theorem gaussian_orthogonality : Spec.GaussianOrthogonality := by
  intro n m
  simp_rw [rodrigues_identification n, rodrigues_identification m]
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa using integral_gaussian (1 : ℝ)
    | succ m => simpa using weighted_hermite_zero_succ m
  | succ n ih =>
    cases m with
    | zero =>
      have hi := weighted_hermite_zero_succ n
      simpa only [physicistsHermite_zero, eval_one, one_mul, mul_one,
        Nat.succ_ne_zero, ite_false] using hi
    | succ m =>
      rw [weighted_hermite_succ_succ, ih]
      by_cases hnm : n = m
      · subst m
        simp only [ite_true, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
          Nat.cast_one]
        ring
      · simp [hnm]

lemma normalization_sq (n : ℕ) :
    normalization n ^ 2 = (2 : ℝ)^n * (n.factorial : ℝ) * Real.sqrt Real.pi := by
  apply Real.sq_sqrt
  exact (mul_pos (mul_pos (pow_pos (by norm_num) _)
    (by exact_mod_cast Nat.factorial_pos n)) (Real.sqrt_pos.mpr Real.pi_pos)).le

lemma h_product (n m : ℕ) (x : ℝ) :
    h n x * h m x = (H n x * H m x * Real.exp (-(x^2))) /
      (normalization n * normalization m) := by
  unfold h
  have he : Real.exp (-(x^2)/2) * Real.exp (-(x^2)/2) = Real.exp (-(x^2)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc
    _ = (H n x * H m x * (Real.exp (-(x^2)/2) * Real.exp (-(x^2)/2))) /
      (normalization n * normalization m) := by ring
    _ = _ := by rw [he]

theorem normalized_orthogonality : Spec.NormalizedOrthogonality := by
  intro n m
  simp_rw [h_product]
  rw [integral_div, gaussian_orthogonality n m]
  by_cases hnm : n = m
  · subst m
    rw [ite_eq_left rfl, ite_eq_left rfl, ← sq, normalization_sq]
    exact div_self (ne_of_gt (by positivity))
  · simp [hnm]

/-- The polynomial factors span every polynomial; no completeness of L² is assumed. -/
lemma polynomial_span : Submodule.span ℝ (Set.range physicistsHermite) = ⊤ := by
  let S := Submodule.span ℝ (Set.range physicistsHermite)
  have hmem (n : ℕ) : physicistsHermite n ∈ S := Submodule.subset_span ⟨n, rfl⟩
  have hderiv (n : ℕ) : (physicistsHermite n).derivative ∈ S := by
    cases n with
    | zero => simp [S]
    | succ n =>
      rw [polynomial_derivative_succ, ← smul_eq_C_mul]
      exact S.smul_mem _ (hmem n)
  have hraise (n : ℕ) : X * physicistsHermite n ∈ S := by
    have he : X * physicistsHermite n = (1/2 : ℝ) •
        (physicistsHermite (n+1) + (physicistsHermite n).derivative) := by
      rw [physicistsHermite_succ, smul_eq_C_mul]
      have hc : C (1/2 : ℝ) * (2 : ℝ[X]) = 1 := by
        rw [← Polynomial.C_ofNat 2, ← map_mul]
        norm_num
      linear_combination -(X * physicistsHermite n) * hc
    rw [he]
    exact S.smul_mem _ (S.add_mem (hmem _) (hderiv _))
  have hX (P : ℝ[X]) (hP : P ∈ S) : X * P ∈ S := by
    induction hP using Submodule.span_induction with
    | mem P hP => obtain ⟨n, rfl⟩ := hP; exact hraise n
    | zero => simpa using S.zero_mem
    | add P Q hP hQ ihP ihQ => simpa only [mul_add] using S.add_mem ihP ihQ
    | smul a P hP ih => simpa only [mul_smul_comm] using S.smul_mem a ih
  apply top_unique
  intro P hP
  clear hP
  change P ∈ S
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => exact S.add_mem hP hQ
  | monomial k a =>
    have hp : ∀ k, X^k ∈ S := by
      intro k
      induction k with
      | zero => simpa using hmem 0
      | succ k ih => simpa only [pow_succ', pow_one] using hX _ ih
    simpa only [smul_eq_C_mul, C_mul_X_pow_eq_monomial] using S.smul_mem a (hp k)

/-- The canonical L² representatives. Their membership has already been proved. -/
def hLp (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) : Lp 𝕜 2 (volume : Measure ℝ) :=
  ((square_integrable n).ofReal (K := 𝕜)).toLp (fun x => (h n x : 𝕜))

lemma hLp_coe (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    (fun x => hLp 𝕜 n x) =ᵐ[volume] fun x => (h n x : 𝕜) :=
  MemLp.coeFn_toLp _

lemma hLp_orthonormal (𝕜 : Type*) [RCLike 𝕜] : Orthonormal 𝕜 (hLp 𝕜) := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [L2.inner_def]
  calc
    _ = ∫ x : ℝ, ((h n x * h m x : ℝ) : 𝕜) := by
      apply integral_congr_ae
      filter_upwards [hLp_coe 𝕜 n, hLp_coe 𝕜 m] with x hn hm
      rw [hn, hm]
      simp [RCLike.inner_apply, RCLike.algebraMap_eq_ofReal, mul_comm]
    _ = ((∫ x : ℝ, h n x * h m x : ℝ) : 𝕜) := integral_ofReal
    _ = _ := by rw [normalized_orthogonality n m]; split_ifs <;> simp

lemma gaussian_memLp {b : ℝ} (hb : 0 < b) :
    MemLp (fun x : ℝ => Real.exp (-b*x^2)) 2 volume := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert integrable_exp_neg_mul_sq (b := 2*b) (by positivity) using 1
  funext x
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- Gaussian damping supplies every exponential absolute moment, by Cauchy--Schwarz. -/
lemma exponential_damping_integrable (g : ℝ → ℂ) (hg : MemLp g 2 volume) (a : ℝ) :
    Integrable (fun x : ℝ => ‖g x‖ * Real.exp (-(x^2)/2) * Real.exp |a*x|) := by
  have hm : MemLp (fun x : ℝ => Real.exp (-(x^2)/2) * Real.exp |a*x|) 2 volume := by
    apply ((gaussian_memLp (b := 1/4) (by norm_num)).const_mul (Real.exp (a^2))).mono'
      (by fun_prop)
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (|x|/2 - |a|), sq_abs x, sq_abs a]
  convert hg.norm.integrable_mul hm using 1
  ext x
  simp only [Pi.mul_apply]
  ring

/-- Vanishing Gaussian moments make the entire Fourier--Laplace transform vanish.
We use a dominated exponential series, avoiding an assumed analyticity certificate. -/
lemma exponential_integral_zero (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (hm : ∀ n : ℕ, (∫ x : ℝ, g x * (x : ℂ)^n * (Real.exp (-(x^2)/2) : ℂ)) = 0)
    (z : ℂ) :
    (∫ x : ℝ, g x * (Real.exp (-(x^2)/2) : ℂ) * Complex.exp (z*x)) = 0 := by
  let F (n : ℕ) (x : ℝ) := g x * (Real.exp (-(x^2)/2) : ℂ) * (z*x)^n / (n.factorial : ℂ)
  let B (n : ℕ) (x : ℝ) := ‖g x‖ * Real.exp (-(x^2)/2) *
    (‖z*(x : ℂ)‖^n / (n.factorial : ℝ))
  have hs (x : ℝ) : HasSum (fun n => B n x)
      (‖g x‖ * Real.exp (-(x^2)/2) * Real.exp ‖z*(x : ℂ)‖) := by
    simpa only [B, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ‖z*(x : ℂ)‖).mul_left
        (‖g x‖ * Real.exp (-(x^2)/2))
  have hi : Integrable (fun x => ∑' n, B n x) := by
    simp_rw [(hs _).tsum_eq]
    convert exponential_damping_integrable g hg ‖z‖ using 1
    ext x
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (norm_nonneg z)]
  have hseries : HasSum (fun n => ∫ x : ℝ, F n x)
      (∫ x : ℝ, g x * (Real.exp (-(x^2)/2) : ℂ) * Complex.exp (z*x)) := by
    apply hasSum_integral_of_dominated_convergence B
    · intro n
      dsimp only [F]
      simp only [div_eq_mul_inv]
      exact ((hg.aestronglyMeasurable.mul
        (by fun_prop : AEStronglyMeasurable (fun x : ℝ => (Real.exp (-(x^2)/2) : ℂ)) volume)).mul
        (by fun_prop : AEStronglyMeasurable (fun x : ℝ => (z*x)^n) volume)).mul_const _
    · intro n
      filter_upwards [] with x
      dsimp only [F, B]
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_natCast]
      exact le_of_eq (by ring)
    · exact Filter.Eventually.of_forall fun x => (hs x).summable
    · exact hi
    · filter_upwards [] with x
      simpa only [F, mul_div_assoc, ← Complex.exp_eq_exp_ℂ] using
        (NormedSpace.expSeries_div_hasSum_exp (z*x)).mul_left
          (g x * (Real.exp (-(x^2)/2) : ℂ))
  have hzero (n : ℕ) : (∫ x : ℝ, F n x) = 0 := by
    calc
      _ = (z^n / (n.factorial : ℂ)) *
          ∫ x : ℝ, g x * (x : ℂ)^n * (Real.exp (-(x^2)/2) : ℂ) := by
        rw [← integral_const_mul]
        congr 1
        ext x
        dsimp only [F]
        rw [mul_pow]
        ring
      _ = 0 := by rw [hm, mul_zero]
  have hs0 : HasSum (fun n : ℕ => (0 : ℂ)) 0 := hasSum_zero
  have hs1 : HasSum (fun _n : ℕ => (0 : ℂ))
      (∫ x : ℝ, g x * (Real.exp (-(x^2)/2) : ℂ) * Complex.exp (z*x)) := by
    simpa only [hzero] using hseries
  exact hs1.unique hs0

/-- Transport the accepted Fourier uniqueness theorem to the ordinary real line.
The pushed measure avoids assuming an unproved normalization of this coordinate map. -/
lemma real_line_fourier_unique (v : ℝ → ℂ) (hv : Integrable v)
    (hF : ∀ z : ℂ, (∫ x : ℝ, v x * Complex.exp (z*x)) = 0) :
    v =ᵐ[volume] 0 := by
  let eL := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let e : EuclideanSpace ℝ (Fin 1) ≃ᵐ ℝ := eL.toHomeomorph.toMeasurableEquiv
  let μ := (volume : Measure ℝ).map e.symm
  let : SigmaFinite μ := e.symm.sigmaFinite_map
  have hw : Integrable (fun x => v (e x)) μ := by
    rw [integrable_map_equiv e.symm]
    simpa only [Function.comp_def, e.apply_symm_apply] using hv
  have hzero := ExpandedFA.Fourier.Uniqueness.weighted_uniqueness 1 μ
    (fun x => v (e x)) hw ?_
  · have hh := ae_of_ae_map e.symm.measurable.aemeasurable hzero
    filter_upwards [hh] with x hx
    simpa only [e.apply_symm_apply, Pi.zero_apply] using hx
  · intro ξ
    unfold ExpandedFA.Fourier.weightedIntegralFourier
    rw [integral_map_equiv e.symm]
    convert hF (-2 * (Real.pi : ℂ) * Complex.I * (ξ 0 : ℂ)) using 1
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [e.apply_symm_apply]
    rw [mul_comm (v x)]
    congr 2
    simp [e, eL, PiLp.inner_apply]
    ring

lemma gaussian_moments_unique (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (hm : ∀ n : ℕ, (∫ x : ℝ, g x * (x : ℂ)^n * (Real.exp (-(x^2)/2) : ℂ)) = 0) :
    g =ᵐ[volume] 0 := by
  have hg0 : Integrable (fun x : ℝ => g x * (Real.exp (-(x^2)/2) : ℂ)) := by
    have he : MemLp (fun x : ℝ => Real.exp (-(x^2)/2)) 2 volume := by
      simpa only [eval_one, mul_one] using polynomial_half_gaussian_memLp (1 : ℝ[X])
    exact hg.integrable_mul (he.ofReal (K := ℂ))
  have hzero := real_line_fourier_unique _ hg0 (exponential_integral_zero g hg hm)
  filter_upwards [hzero] with x hx
  exact (mul_eq_zero.mp hx).resolve_right (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

/-- Completeness test for a function taking values in either scalar field. -/
lemma hermite_orthogonal_unique (𝕜 : Type*) [RCLike 𝕜] (g : ℝ → 𝕜)
    (hg : MemLp g 2 volume) (hz : ∀ n : ℕ, (∫ x : ℝ, h n x • g x) = 0) :
    g =ᵐ[volume] 0 := by
  have hi (P : ℝ[X]) : Integrable (fun x : ℝ =>
      (Real.exp (-(x^2)/2) * P.eval x) • g x) :=
    memLp_one_iff_integrable.mp ((polynomial_half_gaussian_memLp P).smul hg)
  let L : ℝ[X] →ₗ[ℝ] 𝕜 :=
    { toFun := fun P => ∫ x : ℝ, (Real.exp (-(x^2)/2) * P.eval x) • g x
      map_add' := by
        intro P Q
        simp only [eval_add, mul_add, add_smul]
        exact integral_add (hi P) (hi Q)
      map_smul' := by
        intro r P
        change (∫ x : ℝ, (Real.exp (-(x^2)/2) * (r • P).eval x) • g x) = _
        calc
          _ = ∫ x : ℝ, r • ((Real.exp (-(x^2)/2) * P.eval x) • g x) := by
            congr 1
            ext x
            simp only [eval_smul, smul_eq_mul, smul_smul]
            congr 1
            ring
          _ = _ := integral_smul r _ }
  have hLn (n : ℕ) : L (physicistsHermite n) = 0 := by
    have he (x : ℝ) : Real.exp (-(x^2)/2) * (physicistsHermite n).eval x =
        normalization n * h n x := by
      rw [congrFun (h_polynomial n) x]
      field_simp [(normalization_positive n).ne']
    change (∫ x : ℝ, (Real.exp (-(x^2)/2) * (physicistsHermite n).eval x) • g x) = 0
    simp_rw [he, mul_smul, integral_smul, hz, smul_zero]
  have hk : Submodule.span ℝ (Set.range physicistsHermite) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact hLn n
  rw [polynomial_span] at hk
  have hL (P : ℝ[X]) : L P = 0 := hk (Submodule.mem_top)
  let C : 𝕜 →L[ℝ] ℂ :=
    (Complex.ofRealCLM.comp RCLike.reCLM) +
      Complex.I • (Complex.ofRealCLM.comp RCLike.imCLM)
  have hCinj : Function.Injective C := by
    intro a b hab
    apply RCLike.ext
    · have hre := congrArg Complex.re hab
      simpa [C] using hre
    · have him := congrArg Complex.im hab
      simpa [C] using him
  have hCg : MemLp (fun x => C (g x)) 2 volume := C.comp_memLp' hg
  have hCm (n : ℕ) :
      (∫ x : ℝ, C (g x) * (x : ℂ)^n * (Real.exp (-(x^2)/2) : ℂ)) = 0 := by
    calc
      _ = ∫ x : ℝ, C ((Real.exp (-(x^2)/2) * (X^n : ℝ[X]).eval x) • g x) := by
        congr 1
        ext x
        simp only [map_smul, eval_pow, eval_X, Complex.real_smul, Complex.ofReal_mul,
          Complex.ofReal_pow]
        ring
      _ = C (L (X^n)) := C.integral_comp_comm (hi (X^n))
      _ = 0 := by rw [hL, map_zero]
  have hzero := gaussian_moments_unique _ hCg hCm
  filter_upwards [hzero] with x hx
  change g x = 0
  apply hCinj
  simpa only [map_zero, Pi.zero_apply] using hx

/-- The complete orthonormal basis, established by a trivial orthogonal complement. -/
theorem complete_orthonormal_basis : Spec.CompleteOrthonormalBasis := by
  intro 𝕜 _
  have horth : (Submodule.span 𝕜 (Set.range (hLp 𝕜)))ᗮ = ⊥ := by
    apply le_antisymm
    · intro g hg
      change g = 0
      apply Lp.ext
      have hz (n : ℕ) : (∫ x : ℝ, h n x • g x) = 0 := by
        have hin := (Submodule.mem_orthogonal _ _).mp hg (hLp 𝕜 n)
          (Submodule.subset_span ⟨n, rfl⟩)
        rw [L2.inner_def] at hin
        convert hin using 1
        apply integral_congr_ae
        filter_upwards [hLp_coe 𝕜 n] with x hx
        rw [hx]
        simp [RCLike.inner_apply, RCLike.real_smul_eq_coe_mul, mul_comm]
      exact (hermite_orthogonal_unique 𝕜 g (Lp.memLp g) hz).trans (Lp.coeFn_zero 𝕜 2 volume).symm
    · exact bot_le
  refine ⟨HilbertBasis.mkOfOrthogonalEqBot (hLp_orthonormal 𝕜) horth, ?_⟩
  intro n
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  simpa only [RCLike.algebraMap_eq_ofReal] using hLp_coe 𝕜 n

end ExpandedFA.Models.HermiteBasis
