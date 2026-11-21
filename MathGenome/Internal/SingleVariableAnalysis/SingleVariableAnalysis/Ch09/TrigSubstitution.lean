import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.TrigSubstitution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Substitution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.TrigInverses
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.Tan
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.TrigProperties
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

noncomputable section
namespace SingleVariableAnalysis.TrigSubstitution
open Set
open Specs.SingleVariableAnalysis.Ch09.TrigSubstitution

theorem source_compatibility : sourceCompatibility :=
  ⟨sinCosSeries_eq_real, PiPeriod.analyticPi_eq_pi, rfl⟩

private lemma reduced_mem {k : ℤ} {x : ℝ} (hx : x ∈ branch k) :
    x / 2 - k * Real.pi ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  rcases hx with ⟨hl, hr⟩
  constructor <;> linarith

private lemma forward_reduced (k : ℤ) (x : ℝ) :
    forward x = Real.tan (x / 2 - k * Real.pi) :=
  (Real.tan_sub_int_mul_pi (x / 2) k).symm

lemma inverse_mem (k : ℤ) (t : ℝ) : inverse k t ∈ branch k := by
  have h := Real.arctan_mem_Ioo t
  dsimp [inverse, branch]
  constructor <;> linarith [h.1, h.2]

lemma inverse_forward {k : ℤ} {x : ℝ} (hx : x ∈ branch k) :
    inverse k (forward x) = x := by
  rw [inverse, forward_reduced k x, Real.arctan_tan (reduced_mem hx).1 (reduced_mem hx).2]
  ring

lemma forward_inverse (k : ℤ) (t : ℝ) : forward (inverse k t) = t := by
  dsimp [forward, inverse]
  rw [show (2 * Real.arctan t + 2 * k * Real.pi) / 2 = Real.arctan t + k * Real.pi by ring,
    Real.tan_add_int_mul_pi, Real.tan_arctan]

lemma forward_strictMono (k : ℤ) : StrictMonoOn forward (branch k) := by
  intro x hx y hy hxy
  rw [forward_reduced k x, forward_reduced k y]
  exact Real.strictMonoOn_tan (reduced_mem hx) (reduced_mem hy) (by linarith)

lemma cos_half_ne {k : ℤ} {x : ℝ} (hx : x ∈ branch k) : Real.cos (x / 2) ≠ 0 := by
  have h := (Real.cos_pos_of_mem_Ioo (reduced_mem hx)).ne'
  rw [Real.cos_sub_int_mul_pi] at h
  exact (mul_ne_zero_iff.mp h).2

lemma forward_smooth (k : ℤ) : ContDiffOn ℝ 1 forward (branch k) := by
  intro x hx
  exact ((Real.contDiffAt_tan.mpr (cos_half_ne hx)).comp x
    (contDiffAt_id.div_const 2)).contDiffWithinAt

lemma inverse_smooth (k : ℤ) : ContDiff ℝ 1 (inverse k) := by
  change ContDiff ℝ 1 (fun t => 2 * Real.arctan t + 2 * k * Real.pi)
  exact (contDiff_const.mul Real.contDiff_arctan).add contDiff_const

theorem branch_bijection : branchBijection := by
  intro k
  refine ⟨forward_strictMono k, ?_, fun t _ => inverse_mem k t,
    fun _ hx => inverse_forward hx, forward_inverse k, forward_smooth k, inverse_smooth k⟩
  exact ⟨fun _ _ => mem_univ _, (forward_strictMono k).injOn,
    fun t _ => ⟨inverse k t, inverse_mem k t, forward_inverse k t⟩⟩

lemma inverse_hasDerivAt (k : ℤ) (t : ℝ) :
    HasDerivAt (inverse k) (jacobian t) t := by
  change HasDerivAt (fun u => 2 * Real.arctan u + 2 * k * Real.pi) _ t
  convert ((Real.hasDerivAt_arctan t).const_mul 2).add_const (2 * k * Real.pi) using 1
  dsimp [jacobian]
  ring

lemma forward_hasDerivAt {k : ℤ} {x : ℝ} (hx : x ∈ branch k) :
    HasDerivAt forward (1 / (2 * Real.cos (x / 2) ^ 2)) x := by
  convert (Real.hasDerivAt_tan (cos_half_ne hx)).comp x ((hasDerivAt_id x).div_const 2) using 1
  · funext u; simp [forward]
  · ring

lemma half_angle_formulas {k : ℤ} {x : ℝ} (hx : x ∈ branch k) :
    Real.sin x = rationalSin (forward x) ∧ Real.cos x = rationalCos (forward x) := by
  have hc := cos_half_ne hx
  have hp := Real.sin_sq_add_cos_sq (x / 2)
  have hdouble : 2 * (x / 2) = x := by ring
  have hs := Real.sin_two_mul (x / 2)
  have hcos := Real.cos_two_mul (x / 2)
  rw [hdouble] at hs hcos
  dsimp [rationalSin, rationalCos, forward]
  rw [Real.tan_eq_sin_div_cos]
  constructor
  · field_simp
    nlinarith [congrArg (fun z : ℝ => Real.sin x * z) hp]
  · field_simp
    nlinarith [congrArg (fun z : ℝ => Real.cos x * z) hp]

theorem formulas_proved : formulas :=
  ⟨fun _ _ hx => ⟨cos_half_ne hx, (half_angle_formulas hx).1,
    (half_angle_formulas hx).2, forward_hasDerivAt hx⟩, inverse_hasDerivAt⟩

lemma inverse_formulas (k : ℤ) (t : ℝ) :
    Real.sin (inverse k t) = rationalSin t ∧ Real.cos (inverse k t) = rationalCos t := by
  simpa only [forward_inverse] using half_angle_formulas (inverse_mem k t)

lemma inverse_strictMono (k : ℤ) : StrictMono (inverse k) := by
  intro s t hst
  dsimp [inverse]
  linarith [Real.arctan_strictMono hst]

private lemma inverse_maps {k : ℤ} {a b : ℝ}
    (ha : a ∈ branch k) (hb : b ∈ branch k) :
    MapsTo (inverse k) (Icc (forward a) (forward b)) (Icc a b) := by
  intro t ht
  have h1 := (inverse_strictMono k).monotone ht.1
  have h2 := (inverse_strictMono k).monotone ht.2
  rw [inverse_forward ha] at h1
  rw [inverse_forward hb] at h2
  exact ⟨h1, h2⟩

private lemma jacobian_continuous : Continuous jacobian :=
  continuous_const.div (continuous_const.add (continuous_id.pow 2))
    (fun t => by positivity)

lemma bivarEval_continuous {K : Type*} [NormedField K] (P : Polynomial (Polynomial K))
    {s c : ℝ → K} (hs : Continuous s) (hc : Continuous c) :
    Continuous (fun x => bivarEval P (s x) (c x)) := by
  induction P using Polynomial.induction_on with
  | C p => simpa [bivarEval, Function.comp_def] using p.continuous.comp hc
  | add p q hp hq =>
    convert hp.add hq using 1
    funext x
    simp [bivarEval, Polynomial.eval₂_add]
  | monomial n p hp =>
    have he : Polynomial.C p * Polynomial.X ^ (n + 1) =
        (Polynomial.C p * Polynomial.X ^ n) * Polynomial.X := by ring
    convert hp.mul hs using 1
    funext x
    simp only [he, bivarEval, Polynomial.eval₂_mul, Polynomial.eval₂_X]
    rfl

private lemma real_substitution_continuous {f : ℝ → ℝ} {k : ℤ} {a b : ℝ}
    (hab : a ≤ b) (hbranch : Icc a b ⊆ branch k) (hf : ContinuousOn f (Icc a b)) :
    ∃ hi : Riemann.RealIntegrable f a b,
    ∃ ht : Riemann.RealIntegrable (fun t => f (inverse k t) * jacobian t) (forward a) (forward b),
      Riemann.realIntegral f hi = Riemann.realIntegral _ ht := by
  have ha := hbranch (left_mem_Icc.mpr hab)
  have hb := hbranch (right_mem_Icc.mpr hab)
  have hle := (forward_strictMono k).monotoneOn ha hb hab
  have h := Riemann.real_substitution (inverse k) jacobian f
    (forward a) (forward b) (Icc a b) hle (inverse_smooth k).continuous.continuousOn
    jacobian_continuous.continuousOn
    (fun t _ => (inverse_hasDerivAt k t).hasDerivWithinAt)
    ordConnected_Icc hf (inverse_maps ha hb)
  simp only [inverse_forward ha, inverse_forward hb] at h
  obtain ⟨ht, hi, he⟩ := h
  have hi' : Riemann.RealIntegrable f a b := by
    simpa [Riemann.OrientedRealIntegrable, Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue,
      min_eq_left hab, max_eq_right hab] using hi
  refine ⟨hi', ht, ?_⟩
  rw [Riemann.oriented_real_agreement f hab hi hi'] at he
  exact he.symm

private lemma complex_substitution_continuous {f : ℝ → ℂ} {k : ℤ} {a b : ℝ}
    (hab : a ≤ b) (hbranch : Icc a b ⊆ branch k) (hf : ContinuousOn f (Icc a b)) :
    ∃ hi : Riemann.ComplexIntegrable f a b,
    ∃ ht : Riemann.ComplexIntegrable (fun t => f (inverse k t) * (jacobian t : ℂ)) (forward a) (forward b),
      Riemann.complexIntegral f hi = Riemann.complexIntegral _ ht := by
  have ha := hbranch (left_mem_Icc.mpr hab)
  have hb := hbranch (right_mem_Icc.mpr hab)
  have hle := (forward_strictMono k).monotoneOn ha hb hab
  have h := Riemann.complex_substitution (inverse k) jacobian f
    (forward a) (forward b) (Icc a b) hle (inverse_smooth k).continuous.continuousOn
    jacobian_continuous.continuousOn
    (fun t _ => (inverse_hasDerivAt k t).hasDerivWithinAt)
    ordConnected_Icc hf (inverse_maps ha hb)
  simp only [inverse_forward ha, inverse_forward hb] at h
  obtain ⟨ht, hi, he⟩ := h
  have hi' : Riemann.ComplexIntegrable f a b := by
    simpa [Riemann.OrientedComplexIntegrable, Specs.SingleVariableAnalysis.Ch08.Oriented.complexIntegrableValue,
      min_eq_left hab, max_eq_right hab] using hi
  refine ⟨hi', ht, ?_⟩
  rw [Riemann.oriented_complex_agreement f hab hi hi'] at he
  exact he.symm

theorem real_rational_substitution : realRationalSubstitution := by
  intro P Q k a b hab hbranch hQ
  have hc : ContinuousOn (fun x => bivarEval P (Real.sin x) (Real.cos x) /
      bivarEval Q (Real.sin x) (Real.cos x)) (Icc a b) :=
    (bivarEval_continuous P Real.continuous_sin Real.continuous_cos).continuousOn.div
      (bivarEval_continuous Q Real.continuous_sin Real.continuous_cos).continuousOn hQ
  have h := real_substitution_continuous hab hbranch hc
  simpa only [(inverse_formulas k _).1, (inverse_formulas k _).2] using h

theorem complex_rational_substitution : complexRationalSubstitution := by
  intro P Q k a b hab hbranch hQ
  have hs := Complex.continuous_ofReal.comp Real.continuous_sin
  have hc := Complex.continuous_ofReal.comp Real.continuous_cos
  have hf : ContinuousOn (fun x => bivarEval P (Real.sin x : ℂ) (Real.cos x : ℂ) /
      bivarEval Q (Real.sin x : ℂ) (Real.cos x : ℂ)) (Icc a b) :=
    (bivarEval_continuous P hs hc).continuousOn.div
      (bivarEval_continuous Q hs hc).continuousOn hQ
  have h := complex_substitution_continuous hab hbranch hf
  simpa only [(inverse_formulas k _).1, (inverse_formulas k _).2] using h

section RationalAlgebra
variable {K : Type*} [Field K] [Algebra ℝ K]

/-- A polynomial quotient with an everywhere nonzero evaluation denominator. -/
private def PolynomialQuotient (f : ℝ → K) : Prop :=
  ∃ p q : Polynomial K, (∀ t : ℝ, q.eval (algebraMap ℝ K t) ≠ 0) ∧
    ∀ t : ℝ, f t = p.eval (algebraMap ℝ K t) / q.eval (algebraMap ℝ K t)

private lemma quotient_const (c : K) : PolynomialQuotient (fun _ : ℝ => c) := by
  refine ⟨Polynomial.C c, 1, by simp, ?_⟩
  simp

private lemma quotient_add {f g : ℝ → K} (hf : PolynomialQuotient f)
    (hg : PolynomialQuotient g) : PolynomialQuotient (fun t => f t + g t) := by
  obtain ⟨p, q, hq, hp⟩ := hf
  obtain ⟨r, s, hs, hr⟩ := hg
  refine ⟨p * s + r * q, q * s, ?_, ?_⟩
  · intro t; simpa using mul_ne_zero (hq t) (hs t)
  · intro t
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hp, hr]
    rw [div_add_div _ _ (hq t) (hs t)]
    congr 1; ring

private lemma quotient_mul {f g : ℝ → K} (hf : PolynomialQuotient f)
    (hg : PolynomialQuotient g) : PolynomialQuotient (fun t => f t * g t) := by
  obtain ⟨p, q, hq, hp⟩ := hf
  obtain ⟨r, s, hs, hr⟩ := hg
  refine ⟨p * r, q * s, ?_, ?_⟩
  · intro t; simpa using mul_ne_zero (hq t) (hs t)
  · intro t
    simp only [Polynomial.eval_mul, hp, hr, div_mul_div_comm]

private lemma quotient_polynomial (P : Polynomial K) {f : ℝ → K}
    (hf : PolynomialQuotient f) : PolynomialQuotient (fun t => P.eval (f t)) := by
  induction P using Polynomial.induction_on with
  | C c => simpa using quotient_const c
  | add p q hp hq => simpa only [Polynomial.eval_add] using quotient_add hp hq
  | monomial n c hp =>
    have he : Polynomial.C c * Polynomial.X ^ (n + 1) =
        (Polynomial.C c * Polynomial.X ^ n) * Polynomial.X := by ring
    simpa only [he, Polynomial.eval_mul, Polynomial.eval_X] using quotient_mul hp hf

private lemma mapped_denominator_ne (t : ℝ) : algebraMap ℝ K (1 + t ^ 2) ≠ 0 := by
  exact (map_ne_zero (algebraMap ℝ K)).mpr (by positivity)

private lemma quotient_sine : PolynomialQuotient (fun t : ℝ => algebraMap ℝ K (rationalSin t)) := by
  refine ⟨Polynomial.C 2 * Polynomial.X, 1 + Polynomial.X ^ 2, ?_, ?_⟩
  · intro t
    simpa only [map_add, map_one, map_pow, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_X] using mapped_denominator_ne (K := K) t
  · intro t
    simp only [rationalSin, map_div₀, map_mul, map_add, map_pow, map_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_pow]
    rw [show algebraMap ℝ K (2 : ℝ) = 2 by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, map_add, map_one]; ring]

private lemma quotient_cosine : PolynomialQuotient (fun t : ℝ => algebraMap ℝ K (rationalCos t)) := by
  refine ⟨1 - Polynomial.X ^ 2, 1 + Polynomial.X ^ 2, ?_, ?_⟩
  · intro t
    simpa only [map_add, map_one, map_pow, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_X] using mapped_denominator_ne (K := K) t
  · intro t
    simp [rationalCos, map_div₀]

private lemma quotient_bivariate (P : Polynomial (Polynomial K)) :
    PolynomialQuotient (fun t : ℝ => bivarEval P
      (algebraMap ℝ K (rationalSin t)) (algebraMap ℝ K (rationalCos t))) := by
  induction P using Polynomial.induction_on with
  | C p => simpa [bivarEval] using quotient_polynomial p (quotient_cosine (K := K))
  | add p q hp hq => simpa only [bivarEval, Polynomial.eval₂_add] using quotient_add hp hq
  | monomial n p hp =>
    have he : Polynomial.C p * Polynomial.X ^ (n + 1) =
        (Polynomial.C p * Polynomial.X ^ n) * Polynomial.X := by ring
    simpa only [he, bivarEval, Polynomial.eval₂_mul, Polynomial.eval₂_X] using
      quotient_mul hp (quotient_sine (K := K))

lemma rational_form_for : rationalFormFor K := by
  intro P Q
  obtain ⟨p, q, hq, hp⟩ := quotient_bivariate P
  obtain ⟨r, s, hs, hr⟩ := quotient_bivariate Q
  refine ⟨p * s * Polynomial.C 2, q * r * (1 + Polynomial.X ^ 2), ?_⟩
  intro t
  have hd := mapped_denominator_ne (K := K) t
  simp only [map_add, map_one, map_pow] at hd
  have hj : algebraMap ℝ K (jacobian t) = (2 : K) / (1 + algebraMap ℝ K t ^ 2) := by
    simp only [jacobian, map_div₀, map_add, map_one, map_pow]
    rw [show algebraMap ℝ K (2 : ℝ) = 2 by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, map_add, map_one]; ring]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, hp t, hr t, hj]
  constructor
  · simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  · simp only [ne_eq, mul_eq_zero, not_or, hq t, hd, false_or,
      div_eq_zero_iff, hs t]

end RationalAlgebra

theorem rational_form : rationalForm := ⟨rational_form_for, rational_form_for⟩

end SingleVariableAnalysis.TrigSubstitution
