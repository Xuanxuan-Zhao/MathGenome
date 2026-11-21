import MathGenome.Internal.FourierSobolev.P102.Approximation.BernsteinDerivative
import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.MarkovDerivative
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

noncomputable section
open scoped Polynomial ComplexConjugate
open Polynomial Set

namespace P102.Approximation

abbrev polynomialOnInterval := @Expected.polynomialOnInterval

@[simp] theorem polynomialOnInterval_apply {𝕜 : Type*} [RCLike 𝕜]
    (a b : ℝ) (p : 𝕜[X]) (x : Set.Icc a b) :
    polynomialOnInterval a b p x = p.eval (algebraMap ℝ 𝕜 x) := rfl

/-- The formal derivative in the specification is the ordinary derivative
of the real polynomial function, including at both interval endpoints. -/
theorem hasDerivAt_realPolynomial (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun t : ℝ => p.eval t) (p.derivative.eval x) x :=
  p.hasDerivAt x

/-- Complex polynomial evaluation along the real line has the same derivative. -/
theorem hasDerivAt_complexPolynomial (p : ℂ[X]) (x : ℝ) :
    HasDerivAt (fun t : ℝ => p.eval (t : ℂ)) (p.derivative.eval (x : ℂ)) x :=
  (p.hasDerivAt (x : ℂ)).comp_ofReal

/-- Degree zero, including the zero polynomial, has zero derivative. -/
theorem markov_zero {𝕜 : Type*} [RCLike 𝕜] (a b : ℝ) (p : 𝕜[X])
    (hp : p.natDegree ≤ 0) :
    ‖polynomialOnInterval a b p.derivative‖ ≤
      (2 * (0 : ℝ) ^ 2 / (b - a)) * ‖polynomialOnInterval a b p‖ := by
  have hd : p.derivative = 0 :=
    Polynomial.derivative_of_natDegree_zero (Nat.eq_zero_of_le_zero hp)
  have hz : polynomialOnInterval a b (0 : 𝕜[X]) = 0 := by ext; simp
  simp [hd, hz]

/-- Coefficientwise real projection after multiplication by a fixed phase. -/
def realProjection (u : ℂ) (p : ℂ[X]) : ℝ[X] :=
  .ofFinsupp ⟨p.toFinsupp.coeff.mapRange (fun z => (u * z).re) (by simp)⟩

@[simp] theorem coeff_realProjection (u : ℂ) (p : ℂ[X]) (k : ℕ) :
    (realProjection u p).coeff k = (u * p.coeff k).re := rfl

theorem natDegree_realProjection_le (u : ℂ) (p : ℂ[X]) :
    (realProjection u p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hk]

theorem derivative_realProjection (u : ℂ) (p : ℂ[X]) :
    (realProjection u p).derivative = realProjection u p.derivative := by
  ext k
  simp only [Polynomial.coeff_derivative, coeff_realProjection]
  simp [Complex.mul_re]
  ring

theorem eval_realProjection (u : ℂ) (p : ℂ[X]) (x : ℝ) :
    (realProjection u p).eval x = (u * p.eval (x : ℂ)).re := by
  rw [Polynomial.eval_eq_sum_range' (n := p.natDegree + 1)
    (by have := natDegree_realProjection_le u p; omega), Polynomial.eval_eq_sum_range]
  simp only [coeff_realProjection, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [← Complex.ofReal_pow, Complex.mul_re]
  ring

/-- A unit phase makes a nonzero complex number real and positive. -/
theorem exists_phase (z : ℂ) (hz : z ≠ 0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ (u * z).re = ‖z‖ := by
  refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
  · simp [Complex.norm_real, norm_ne_zero_iff.mpr hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    have he : conj z / (‖z‖ : ℂ) * z = (‖z‖ : ℂ) := by
      rw [div_mul_eq_mul_div, div_eq_iff hn, Complex.conj_mul', pow_two]
    simpa using congrArg Complex.re he

/-- Complex applicability follows pointwise from the real estimate; the bound
uses the actual complex norm and does not split into two separate component bounds. -/
theorem complex_bound_of_real_bound
    (hreal : ∀ (n : ℕ) (p : ℝ[X]) (M : ℝ), p.natDegree ≤ n → 0 ≤ M →
      (∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) →
      ∀ x ∈ Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ (n : ℝ)^2 * M)
    (n : ℕ) (p : ℂ[X]) (M : ℝ) (hp : p.natDegree ≤ n) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖ ≤ M)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖p.derivative.eval (x : ℂ)‖ ≤ (n : ℝ)^2 * M := by
  by_cases hz : p.derivative.eval (x : ℂ) = 0
  · simp only [hz, norm_zero]
    positivity
  obtain ⟨u, hu, huz⟩ := exists_phase _ hz
  have hb : ∀ y ∈ Icc (-1 : ℝ) 1, |(realProjection u p).eval y| ≤ M := by
    intro y hy
    rw [eval_realProjection]
    calc
      _ ≤ ‖u * p.eval (y : ℂ)‖ := Complex.abs_re_le_norm _
      _ = ‖p.eval (y : ℂ)‖ := by rw [norm_mul, hu, one_mul]
      _ ≤ M := hbound y hy
  have h := hreal n (realProjection u p) M
    ((natDegree_realProjection_le u p).trans hp) hM hb x hx
  rw [derivative_realProjection, eval_realProjection, huz,
    abs_of_nonneg (norm_nonneg _)] at h
  exact h

/-- Affine substitution does not raise polynomial degree. -/
theorem natDegree_comp_affine_le {𝕜 : Type*} [RCLike 𝕜]
    (p : 𝕜[X]) (c d : 𝕜) :
    (p.comp (C c + C d * X)).natDegree ≤ p.natDegree := by
  calc
    _ ≤ p.natDegree * (C c + C d * X).natDegree := Polynomial.natDegree_comp_le
    _ ≤ p.natDegree * 1 := by
      gcongr
      apply Polynomial.natDegree_add_le_of_degree_le
      · simp
      · exact (Polynomial.natDegree_mul_le).trans (by simp)
    _ = _ := mul_one _

/-- The inverse coordinate of the affine map from [-1,1] to [a,b]. -/
theorem normalized_mem {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    (2 * x - a - b) / (b - a) ∈ Icc (-1 : ℝ) 1 := by
  constructor
  · apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
    linarith [hx.1]
  · apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
    linarith [hx.2]

theorem affine_mem {a b y : ℝ} (hab : a < b) (hy : y ∈ Icc (-1 : ℝ) 1) :
    (a + b) / 2 + (b - a) / 2 * y ∈ Icc a b := by
  constructor <;> nlinarith [hy.1, hy.2]

theorem affine_normalized {a b x : ℝ} (hab : a < b) :
    (a + b) / 2 + (b - a) / 2 * ((2 * x - a - b) / (b - a)) = x := by
  field_simp [(sub_pos.mpr hab).ne']
  ring

/-- All interval-length factors follow from the real unit-interval estimate.
This is an assembly lemma; its hypothesis remains a separate proof obligation. -/
theorem interval_bound_of_unit_bound {𝕜 : Type*} [RCLike 𝕜]
    (hunit : ∀ (n : ℕ) (p : 𝕜[X]) (M : ℝ), p.natDegree ≤ n → 0 ≤ M →
      (∀ x ∈ Icc (-1 : ℝ) 1, ‖p.eval (algebraMap ℝ 𝕜 x)‖ ≤ M) →
      ∀ x ∈ Icc (-1 : ℝ) 1, ‖p.derivative.eval (algebraMap ℝ 𝕜 x)‖ ≤ (n : ℝ)^2 * M)
    (a b : ℝ) (hab : a < b) (n : ℕ) (p : 𝕜[X]) (hp : p.natDegree ≤ n) :
    ‖polynomialOnInterval a b p.derivative‖ ≤
      (2 * (n : ℝ)^2 / (b-a)) * ‖polynomialOnInterval a b p‖ := by
  let c : ℝ := (a + b) / 2
  let d : ℝ := (b - a) / 2
  let q : 𝕜[X] := p.comp (C (algebraMap ℝ 𝕜 c) + C (algebraMap ℝ 𝕜 d) * X)
  have hd : 0 < d := by dsimp [d]; linarith
  have hqdeg : q.natDegree ≤ n := (natDegree_comp_affine_le p _ _).trans hp
  have hqeval (y : ℝ) : q.eval (algebraMap ℝ 𝕜 y) =
      p.eval (algebraMap ℝ 𝕜 (c + d * y)) := by simp [q]
  have hqderiv (y : ℝ) : q.derivative.eval (algebraMap ℝ 𝕜 y) =
      p.derivative.eval (algebraMap ℝ 𝕜 (c + d * y)) * algebraMap ℝ 𝕜 d := by
    simp [q, Polynomial.derivative_comp]
    ring
  have hqb : ∀ y ∈ Icc (-1 : ℝ) 1, ‖q.eval (algebraMap ℝ 𝕜 y)‖ ≤
      ‖polynomialOnInterval a b p‖ := by
    intro y hy
    rw [hqeval]
    exact (polynomialOnInterval a b p).norm_coe_le_norm
      ⟨c + d * y, affine_mem hab hy⟩
  apply ((polynomialOnInterval a b p.derivative).norm_le (by positivity)).mpr
  intro x
  let y : ℝ := (2 * (x : ℝ) - a - b) / (b - a)
  have hy : y ∈ Icc (-1 : ℝ) 1 := normalized_mem hab x.property
  have heq : c + d * y = x := affine_normalized hab
  have h := hunit n q ‖polynomialOnInterval a b p‖ hqdeg (norm_nonneg _) hqb y hy
  rw [hqderiv, heq, norm_mul] at h
  have hnorm : ‖algebraMap ℝ 𝕜 d‖ = d := by
    simpa only [RCLike.algebraMap_eq_ofReal] using
      (RCLike.norm_ofReal (K := 𝕜) d).trans (abs_of_pos hd)
  rw [hnorm] at h
  rw [polynomialOnInterval_apply]
  calc
    _ ≤ (n : ℝ)^2 * ‖polynomialOnInterval a b p‖ / d := (le_div_iff₀ hd).mpr h
    _ = _ := by
      dsimp [d]
      field_simp

/-- The real and complex general-interval conclusions from a real unit bound. -/
theorem markov_real_of_unit_bound
    (hunit : ∀ (n : ℕ) (p : ℝ[X]) (M : ℝ), p.natDegree ≤ n → 0 ≤ M →
      (∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) →
      ∀ x ∈ Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ (n : ℝ)^2 * M) :
    Expected.markovRealStatement := by
  intro a b hab n p hp
  apply interval_bound_of_unit_bound (𝕜 := ℝ) ?_ a b hab n p hp
  simpa only [Algebra.algebraMap_self, RingHom.id_apply, Real.norm_eq_abs] using hunit

theorem markov_complex_of_unit_bound
    (hunit : ∀ (n : ℕ) (p : ℝ[X]) (M : ℝ), p.natDegree ≤ n → 0 ≤ M →
      (∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) →
      ∀ x ∈ Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ (n : ℝ)^2 * M) :
    Expected.markovComplexStatement := by
  intro a b hab n p hp
  apply interval_bound_of_unit_bound (𝕜 := ℂ) ?_ a b hab n p hp
  exact complex_bound_of_real_bound hunit

/-- A zero bound on a nondegenerate real interval forces the polynomial to vanish. -/
theorem eq_zero_of_unit_bound_zero (p : ℝ[X])
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ 0) : p = 0 := by
  apply p.eq_zero_of_infinite_isRoot
  apply (Set.Icc_infinite (show (-1 : ℝ) < 1 by norm_num)).mono
  intro x hx
  exact abs_nonpos_iff.mp (hb x hx)

/-- The library's Chebyshev comparison at the normalized right endpoint.
The stronger endpoint-zone estimate is proved below. -/
theorem real_derivative_endpoint_le_one (n : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ n)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    |p.derivative.eval 1| ≤ (n : ℝ)^2 := by
  have hd : p.degree ≤ n := Polynomial.degree_le_of_natDegree_le hp
  have hpos := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := 1) (x := (1 : ℝ)) le_rfl hd hb
  have hneg := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := 1) (x := (1 : ℝ)) le_rfl (P := -p) (by simpa using hd)
    (by simpa using hb)
  simp only [Function.iterate_one, Polynomial.Chebyshev.derivative_T_eval_one,
    Int.cast_natCast, Polynomial.derivative_neg, Polynomial.eval_neg] at hpos hneg
  exact abs_le.mpr ⟨by linarith, hpos⟩

/-- Bernstein's weight is at least 1/n throughout the central interval. -/
theorem central_weight_lower (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : |x| ≤ Real.cos (Real.pi / (2 * n))) :
    1 ≤ (n : ℝ) * Real.sqrt (1 - x^2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let θ : ℝ := Real.pi / (2 * n)
  have hθ0 : 0 ≤ θ := by positivity
  have hθ : θ ≤ Real.pi / 2 := by
    dsimp [θ]
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hsin : 1 / (n : ℝ) ≤ Real.sin θ := by
    have h := Real.mul_le_sin hθ0 hθ
    convert h using 1
    dsimp [θ]
    field_simp
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith) hθ
  have hxx : x^2 ≤ (Real.cos θ)^2 := by
    have h := (sq_le_sq₀ (abs_nonneg x) hc0).mpr hx
    simpa only [sq_abs] using h
  have hrad : 0 ≤ 1 - x^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsqrt : Real.sin θ ≤ Real.sqrt (1 - x^2) := by
    apply (sq_le_sq₀ hs0 (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hrad]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have h1 : 1 ≤ (n : ℝ) * Real.sin θ := by
    have := (div_le_iff₀ hnR).mp hsin
    nlinarith
  exact h1.trans (mul_le_mul_of_nonneg_left hsqrt hnR.le)

/-- Inclusion of the finite Fourier degree spaces. -/
theorem complexTrigDegree_mono {T : ℝ} [Fact (0 < T)] {m n : ℕ} (hmn : m ≤ n) :
    P102.Periodic.complexTrigDegree T m ≤ P102.Periodic.complexTrigDegree T n := by
  apply Submodule.map_mono
  apply Finsupp.supported_mono
  intro k hk
  simp only [Set.mem_Icc] at hk ⊢
  constructor <;> omega

theorem mode_mem_complexTrigDegree {T : ℝ} [Fact (0 < T)] (n : ℕ) (k : ℤ)
    (hk : k ∈ Set.Icc (-(n : ℤ)) n) :
    P102.Periodic.mode T k ∈ P102.Periodic.complexTrigDegree T n := by
  refine ⟨Finsupp.single k 1, ?_, ?_⟩
  · exact (Finsupp.mem_supported ℂ _).mpr (by simpa using hk)
  · ext x
    simp [P102.Periodic.synthesis, Finsupp.linearCombination_apply]

/-- Multiplication by a Fourier mode shifts every frequency by its index. -/
theorem mul_mode_mem_complexTrigDegree {T : ℝ} [Fact (0 < T)] {m n : ℕ}
    (P : C(P102.Periodic.Circle T, ℂ))
    (hP : P ∈ P102.Periodic.complexTrigDegree T n) (k : ℤ)
    (hk : k ∈ Set.Icc (-(m : ℤ)) m) :
    P * P102.Periodic.mode T k ∈ P102.Periodic.complexTrigDegree T (n + m) := by
  obtain ⟨c, hc, rfl⟩ := hP
  have heq : P102.Periodic.synthesis T c * P102.Periodic.mode T k =
      ∑ j ∈ c.support, c j • P102.Periodic.mode T (j + k) := by
    ext x
    simp only [ContinuousMap.mul_apply, P102.Periodic.synth_sum, Finset.sum_mul,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
      P102.Periodic.mode, fourier_add, mul_assoc]
  rw [heq]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  apply mode_mem_complexTrigDegree
  have hj' := (Finsupp.mem_supported ℂ c).mp hc hj
  simp only [Set.mem_Icc] at hj' hk ⊢
  push_cast
  constructor <;> omega

/-- A cosine on the angular circle, expressed using exactly the modes ±1. -/
def angularCosine : C(P102.Periodic.Circle (2 * Real.pi), ℂ) :=
  (1 / 2 : ℂ) • (P102.Periodic.mode (2 * Real.pi) 1 +
    P102.Periodic.mode (2 * Real.pi) (-1))

@[simp] theorem angularCosine_coe (t : ℝ) :
    angularCosine (t : P102.Periodic.Circle (2 * Real.pi)) = (Real.cos t : ℂ) := by
  simp only [angularCosine, ContinuousMap.smul_apply, ContinuousMap.add_apply,
    smul_eq_mul, P102.Periodic.angular_mode, Int.cast_one, Int.cast_neg,
    mul_one, mul_neg_one]
  rw [show -(Complex.I) * (t : ℂ) = -(Complex.I * t) by ring,
    mul_comm Complex.I (t : ℂ), show -(↑t * Complex.I) = -(t : ℂ) * Complex.I by ring, ← Complex.two_cos]
  rw [← Complex.ofReal_cos]
  ring

theorem pow_angularCosine_mem (k : ℕ) :
    angularCosine ^ k ∈ P102.Periodic.complexTrigDegree (2 * Real.pi) k := by
  induction k with
  | zero =>
    convert mode_mem_complexTrigDegree (T := 2 * Real.pi) 0 0 (by simp) using 1
    ext x
    simp [P102.Periodic.mode]
  | succ k ih =>
    rw [pow_succ, angularCosine, mul_smul_comm, mul_add]
    apply Submodule.smul_mem
    apply Submodule.add_mem
    · exact mul_mode_mem_complexTrigDegree _ ih 1 (by simp)
    · exact mul_mode_mem_complexTrigDegree _ ih (-1) (by simp)

/-- The pullback of a real algebraic polynomial under cosine. -/
def polynomialCosine (p : ℝ[X]) : C(P102.Periodic.Circle (2 * Real.pi), ℂ) :=
  ∑ k ∈ Finset.range (p.natDegree + 1), (p.coeff k : ℂ) • angularCosine ^ k

@[simp] theorem polynomialCosine_coe (p : ℝ[X]) (t : ℝ) :
    polynomialCosine p (t : P102.Periodic.Circle (2 * Real.pi)) =
      ((p.eval (Real.cos t) : ℝ) : ℂ) := by
  simp only [polynomialCosine, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    ContinuousMap.pow_apply, angularCosine_coe, smul_eq_mul,
    Polynomial.eval_eq_sum_range, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]

/-- In particular, the cosine substitution preserves the required degree bound.
This supplies the finite-frequency bridge needed to apply Bernstein. -/
theorem polynomialCosine_mem (p : ℝ[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    polynomialCosine p ∈ P102.Periodic.complexTrigDegree (2 * Real.pi) n := by
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  exact complexTrigDegree_mono (by have := Finset.mem_range.mp hk; omega)
    (pow_angularCosine_mem k)

/-- The affine cosine substitution used when transporting Markov's inequality
from [-1,1] to [a,b] has the same finite Fourier degree bound. -/
theorem affine_polynomial_cosine (p : ℝ[X]) (c d : ℝ) (n : ℕ)
    (hp : p.natDegree ≤ n) :
    ∃ P : C(P102.Periodic.Circle (2 * Real.pi), ℂ),
      P ∈ P102.Periodic.complexTrigDegree (2 * Real.pi) n ∧
      ∀ t : ℝ, P (t : P102.Periodic.Circle (2 * Real.pi)) =
        ((p.eval (c + d * Real.cos t) : ℝ) : ℂ) := by
  let q := p.comp (C c + C d * X)
  refine ⟨polynomialCosine q, polynomialCosine_mem q n
    ((natDegree_comp_affine_le p c d).trans hp), ?_⟩
  intro t
  simp [q]

/-- The sharp weighted algebraic Bernstein estimate on the entire closed unit
interval; the endpoint weight is zero. -/
theorem real_weighted_bernstein (n : ℕ) (p : ℝ[X]) (M : ℝ)
    (hp : p.natDegree ≤ n) (hM : 0 ≤ M)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |p.derivative.eval x| * Real.sqrt (1 - x ^ 2) ≤ (n : ℝ) * M := by
  obtain ⟨Q, hQ, hnorm⟩ := bernstein_complex (2 * Real.pi) n (polynomialCosine p)
    (polynomialCosine_mem p n hp)
  have hPnorm : ‖polynomialCosine p‖ ≤ M := by
    apply ((polynomialCosine p).norm_le hM).mpr
    intro z
    induction z using QuotientAddGroup.induction_on with
    | H t =>
      simpa using hb (Real.cos t) ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  let t := Real.arccos x
  have hcos : Real.cos t = x := Real.cos_arccos hx.1 hx.2
  have hderiv : HasDerivAt (fun s : ℝ => ((p.eval (Real.cos s) : ℝ) : ℂ))
      ((p.derivative.eval x * (-Real.sin t) : ℝ) : ℂ) t := by
    simpa only [hcos, Function.comp_apply] using
      ((p.hasDerivAt (Real.cos t)).comp t (Real.hasDerivAt_cos t)).ofReal_comp
  have heq : Q (t : P102.Periodic.Circle (2 * Real.pi)) =
      ((p.derivative.eval x * (-Real.sin t) : ℝ) : ℂ) := by
    have hQ' : HasDerivAt (fun s : ℝ => ((p.eval (Real.cos s) : ℝ) : ℂ))
        (Q (t : P102.Periodic.Circle (2 * Real.pi))) t := by
      simpa only [polynomialCosine_coe] using hQ t
    exact hQ'.unique hderiv
  have hsin : Real.sin t = Real.sqrt (1 - x ^ 2) := Real.sin_arccos x
  calc
    _ = ‖Q (t : P102.Periodic.Circle (2 * Real.pi))‖ := by
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, hsin,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ ‖Q‖ := Q.norm_coe_le_norm _
    _ ≤ (n : ℝ) * ‖polynomialCosine p‖ := by
      simpa [Real.pi_ne_zero] using hnorm
    _ ≤ (n : ℝ) * M := mul_le_mul_of_nonneg_left hPnorm (Nat.cast_nonneg _)

/-- On the right endpoint zone, both Chebyshev factors have nonnegative
values. The assertion includes x = 1. -/
theorem chebyshev_nonneg_endpoint (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x ∈ Icc (Real.cos (Real.pi / (2 * n))) 1) :
    0 ≤ (Polynomial.Chebyshev.T ℝ n).eval x ∧
      0 ≤ (Polynomial.Chebyshev.U ℝ (n - 1 : ℕ)).eval x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let θ := Real.pi / (2 * n : ℝ)
  have hθpos : 0 < θ := by dsimp [θ]; positivity
  have hθle : θ ≤ Real.pi / 2 := by
    dsimp [θ]
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hx0 : 0 ≤ x := (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith : -(Real.pi / 2) ≤ θ) hθle).trans hx.1
  let t := Real.arccos x
  have ht0 : 0 ≤ t := Real.arccos_nonneg x
  have hcos : Real.cos t = x := Real.cos_arccos (by linarith) hx.2
  have htθ : t ≤ θ := by
    apply (Real.strictAntiOn_cos.le_iff_ge
      ⟨hθpos.le, by linarith⟩ ⟨ht0, Real.arccos_le_pi x⟩).mp
    simpa only [hcos] using hx.1
  have hnt : (n : ℝ) * t ≤ Real.pi / 2 := by
    have := mul_le_mul_of_nonneg_left htθ hnR.le
    have heq : (n : ℝ) * θ = Real.pi / 2 := by dsimp [θ]; field_simp
    linarith
  constructor
  · rw [← hcos, Polynomial.Chebyshev.T_real_cos]
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · push_cast
      nlinarith [Real.pi_pos]
    · simpa using hnt
  · by_cases ht : t = 0
    · have hx1 : x = 1 := by simpa [ht] using hcos.symm
      simp only [hx1, Polynomial.Chebyshev.U_eval_one, Int.cast_natCast]
      positivity
    have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
      (lt_of_le_of_ne ht0 (Ne.symm ht)) (by linarith)
    have h := Polynomial.Chebyshev.U_real_cos (θ := t) (n := ((n - 1 : ℕ) : ℤ))
    have hcast : (((n - 1 : ℕ) : ℤ) : ℝ) + 1 = n := by
      norm_cast
      omega
    rw [hcast, hcos] at h
    have hs : 0 ≤ Real.sin ((n : ℝ) * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (hnt.trans (by linarith : Real.pi / 2 ≤ Real.pi))
    exact nonneg_of_mul_nonneg_left (h.symm ▸ hs) hsin

/-- The polynomial with the Chebyshev extrema as simple zeros. -/
theorem chebyshev_nodal_identity (n : ℕ) (hn : 0 < n) :
    (X ^ 2 - 1) * Polynomial.Chebyshev.U ℝ (n - 1 : ℕ) =
      C ((2 : ℝ) ^ (n - 1)) *
        Lagrange.nodal (Finset.range (n + 1)) (Polynomial.Chebyshev.node n) := by
  let F : ℝ[X] := (X ^ 2 - 1) * Polynomial.Chebyshev.U ℝ (n - 1 : ℕ)
  have hd : F.degree = (n + 1 : ℕ) := by
    dsimp [F]
    rw [Polynomial.degree_mul,
      Polynomial.degree_sub_eq_left_of_degree_lt (by simp),
      Polynomial.degree_X_pow, Polynomial.Chebyshev.degree_U_natCast]
    norm_cast
    omega
  have hlc : F.leadingCoeff = (2 : ℝ) ^ (n - 1) := by
    dsimp [F]
    rw [Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_sub_of_degree_lt (by simp)]
    simp
  apply Polynomial.eq_of_degree_le_of_eval_index_eq (Finset.range (n + 1))
    (Polynomial.Chebyshev.strictAntiOn_node n).injOn
  · simpa only [Finset.card_range] using hd.le
  · change F.degree = _
    rw [Polynomial.degree_C_mul (by positivity), Lagrange.degree_nodal,
      Finset.card_range]
    exact hd
  · change F.leadingCoeff = _
    calc
      F.leadingCoeff = (2 : ℝ) ^ (n - 1) := hlc
      _ = _ := by
        rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
          Lagrange.nodal_monic, mul_one]
  · intro k hk
    simp only [Polynomial.eval_mul, Lagrange.eval_nodal_at_node hk, mul_zero]
    by_cases hk0 : k = 0
    · simp [hk0, Polynomial.Chebyshev.node_eq_one]
    by_cases hkn : k = n
    · simp [hkn, Polynomial.Chebyshev.node_eq_neg_one (Nat.ne_zero_of_lt hn)]
    have hklt : k < n := by have := Finset.mem_range.mp hk; omega
    have hderiv := (Polynomial.Chebyshev.isLocalExtr_T_real (Nat.ne_zero_of_lt hn)
      (Nat.pos_of_ne_zero hk0) hklt).deriv_eq_zero
    rw [Polynomial.deriv, Polynomial.Chebyshev.T_derivative_eq_U,
      Polynomial.eval_mul] at hderiv
    have hcast : (n : ℤ) - 1 = (n - 1 : ℕ) := by omega
    simp only [Int.cast_natCast, Polynomial.eval_natCast, hcast] at hderiv
    have hu : (Polynomial.Chebyshev.U ℝ (n - 1 : ℕ)).eval
        (Polynomial.Chebyshev.node n k) = 0 :=
      (mul_eq_zero.mp hderiv).resolve_left (by exact_mod_cast hn.ne')
    simp only [hu, mul_zero]

/-- The derivative of the full node polynomial is nonnegative in the endpoint
zone. This gives the signs of the Lagrange derivatives without estimating a
logarithmic sum. -/
theorem chebyshev_nodal_derivative_nonneg (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x ∈ Icc (Real.cos (Real.pi / (2 * n))) 1) :
    0 ≤ (Lagrange.nodal (Finset.range (n + 1))
      (Polynomial.Chebyshev.node n)).derivative.eval x := by
  have hnonneg := chebyshev_nonneg_endpoint n hn x hx
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let u := Polynomial.Chebyshev.U ℝ (n - 1 : ℕ)
  have hcast : ((n - 1 : ℕ) : ℤ) + 1 = n := by omega
  have h := congrArg (fun p : ℝ[X] => p.eval x)
    (Polynomial.Chebyshev.add_one_mul_T_eq_poly_in_U (R := ℝ) ((n - 1 : ℕ) : ℤ))
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_intCast,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_pow,
    hcast] at h
  have hcoef : (((n - 1 : ℕ) : ℤ) : ℝ) + 1 = n := by exact_mod_cast hcast
  rw [hcoef] at h
  have hF : ((X ^ 2 - 1) * u).derivative.eval x =
      x * u.eval x + (n : ℝ) * (Polynomial.Chebyshev.T ℝ n).eval x := by
    simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_X_pow, Polynomial.derivative_one, sub_zero,
      Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
    dsimp [u] at *
    norm_num
    nlinarith [h]
  have hx0 : 0 ≤ x := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hθ : Real.pi / (2 * n : ℝ) ≤ Real.pi / 2 := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
      linarith
    exact (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by
      have : (0 : ℝ) ≤ Real.pi / (2 * n) := by positivity
      linarith) hθ).trans hx.1
  have hFnonneg : 0 ≤ ((X ^ 2 - 1) * u).derivative.eval x := by
    rw [hF]
    exact add_nonneg (mul_nonneg hx0 hnonneg.2) (mul_nonneg hnR.le hnonneg.1)
  dsimp [u] at hFnonneg
  rw [chebyshev_nodal_identity n hn, Polynomial.derivative_C_mul,
    Polynomial.eval_mul, Polynomial.eval_C] at hFnonneg
  exact nonneg_of_mul_nonneg_right hFnonneg (by positivity : 0 < (2 : ℝ) ^ (n - 1))

theorem chebyshev_node_lt_endpoint_zone (n k : ℕ) (hn : 0 < n)
    (hk0 : 0 < k) (hk : k ≤ n) :
    Polynomial.Chebyshev.node n k < Real.cos (Real.pi / (2 * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
  apply Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity)
  · apply (div_le_iff₀ hnR).mpr
    nlinarith [Real.pi_pos]
  · have hhalf : Real.pi / (2 * n : ℝ) < Real.pi / n :=
      div_lt_div_of_pos_left Real.pi_pos hnR (by linarith)
    apply hhalf.trans_le
    apply div_le_div_of_nonneg_right ?_ hnR.le
    nlinarith [Real.pi_pos]

/-- Delete any one Chebyshev extremum: the derivative of the remaining node
product is nonnegative throughout the right endpoint zone. -/
theorem chebyshev_nodal_erase_derivative_nonneg (n : ℕ) (hn : 0 < n)
    (k : ℕ) (hk : k ∈ Finset.range (n + 1)) (x : ℝ)
    (hx : x ∈ Icc (Real.cos (Real.pi / (2 * n))) 1) :
    0 ≤ (Lagrange.nodal ((Finset.range (n + 1)).erase k)
      (Polynomial.Chebyshev.node n)).derivative.eval x := by
  let s := Finset.range (n + 1)
  let v := Polynomial.Chebyshev.node n
  have hsub (j : ℕ) (hj : j ∈ s) (hj0 : j ≠ 0) : 0 < x - v j := by
    apply sub_pos.mpr
    exact (chebyshev_node_lt_endpoint_zone n j hn (Nat.pos_of_ne_zero hj0)
      (by have := Finset.mem_range.mp hj; omega)).trans_le hx.1
  change 0 ≤ (Lagrange.nodal (s.erase k) v).derivative.eval x
  by_cases hk0 : k = 0
  · subst k
    rw [Lagrange.derivative_nodal, Polynomial.eval_finsetSum]
    apply Finset.sum_nonneg
    intro i hi
    rw [Lagrange.eval_nodal]
    apply Finset.prod_nonneg
    intro j hj
    have hj' := Finset.mem_erase.mp ((Finset.mem_erase.mp hj).2)
    exact (hsub j hj'.2 hj'.1).le
  have hzero : 0 ∈ s.erase k := Finset.mem_erase.mpr ⟨Ne.symm hk0, by simp [s]⟩
  have hN : (Lagrange.nodal (s.erase k) v).eval x ≤ 0 := by
    rw [Lagrange.nodal_eq_mul_nodal_erase hzero,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply mul_nonpos_of_nonpos_of_nonneg
    · simpa [v, Polynomial.Chebyshev.node_eq_one] using sub_nonpos.mpr hx.2
    · rw [Lagrange.eval_nodal]
      apply Finset.prod_nonneg
      intro j hj
      have hj' := Finset.mem_erase.mp hj
      exact (hsub j (Finset.mem_erase.mp hj'.2).2 hj'.1).le
  have hderiv := chebyshev_nodal_derivative_nonneg n hn x hx
  change 0 ≤ (Lagrange.nodal s v).derivative.eval x at hderiv
  rw [Lagrange.nodal_eq_mul_nodal_erase hk, Polynomial.derivative_mul,
    Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
    sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at hderiv
  apply nonneg_of_mul_nonneg_right (a := x - v k) ?_ (hsub k hk hk0)
  nlinarith

/-- The Lagrange derivative signs match the alternating values of Tₙ. -/
theorem chebyshev_lagrange_derivative_sign (n : ℕ) (hn : 0 < n)
    (k : ℕ) (hk : k ∈ Finset.range (n + 1)) (x : ℝ)
    (hx : x ∈ Icc (Real.cos (Real.pi / (2 * n))) 1) :
    0 ≤ (-1 : ℝ) ^ k * (Lagrange.basis (Finset.range (n + 1))
      (Polynomial.Chebyshev.node n) k).derivative.eval x := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hk,
    ← Lagrange.nodal_erase_eq_nodal_div hk, Polynomial.derivative_C_mul,
    Polynomial.eval_mul, Polynomial.eval_C, ← mul_assoc]
  apply mul_nonneg ?_ (chebyshev_nodal_erase_derivative_nonneg n hn k hk x hx)
  have hw := inv_pos.mpr (Polynomial.Chebyshev.zero_lt_prod_node_sub_node
    (show k ≤ n by have := Finset.mem_range.mp hk; omega))
  rw [mul_inv, ← inv_pow, inv_neg_one] at hw
  simpa [Lagrange.nodalWeight, Finset.prod_inv_distrib] using hw.le

/-- Interpolation differentiated once, with the original polynomial degree
bound. -/
theorem eval_derivative_eq_lagrange_sum (n : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ n) (x : ℝ) :
    p.derivative.eval x = ∑ k ∈ Finset.range (n + 1),
      p.eval (Polynomial.Chebyshev.node n k) *
        (Lagrange.basis (Finset.range (n + 1)) (Polynomial.Chebyshev.node n) k).derivative.eval x := by
  have hd : p.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    exact (Polynomial.degree_le_of_natDegree_le hp).trans_lt (by exact_mod_cast Nat.lt_succ_self n)
  nth_rewrite 1 [Lagrange.eq_interpolate (Polynomial.Chebyshev.strictAntiOn_node n).injOn hd]
  simp only [Lagrange.interpolate_apply, Polynomial.derivative_sum,
    Polynomial.derivative_C_mul, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]

/-- Chebyshev interpolation proves the unweighted n² estimate on the entire
right endpoint zone, including the endpoint itself. -/
theorem real_endpoint_zone_bound (n : ℕ) (hn : 0 < n) (p : ℝ[X]) (M : ℝ)
    (hp : p.natDegree ≤ n) (hM : 0 ≤ M)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M)
    (x : ℝ) (hx : x ∈ Icc (Real.cos (Real.pi / (2 * n))) 1) :
    |p.derivative.eval x| ≤ (n : ℝ) ^ 2 * M := by
  let s := Finset.range (n + 1)
  let v := Polynomial.Chebyshev.node n
  let d := fun k => (Lagrange.basis s v k).derivative.eval x
  have hd (k : ℕ) (hk : k ∈ s) : |d k| = (-1 : ℝ) ^ k * d k := by
    have hsign := chebyshev_lagrange_derivative_sign n hn k hk x hx
    have habs : |(-1 : ℝ) ^ k * d k| = |d k| := by rw [abs_mul, abs_neg_one_pow, one_mul]
    exact habs.symm.trans (abs_of_nonneg hsign)
  have hsum : ∑ k ∈ s, |d k| = (Polynomial.Chebyshev.T ℝ n).derivative.eval x := by
    rw [eval_derivative_eq_lagrange_sum n _ (by simp)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hd k hk, Polynomial.Chebyshev.eval_T_real_node
      (Finset.mem_Iic.mpr (by have := Finset.mem_range.mp hk; omega))]
  have hxunit : x ∈ Icc (-1 : ℝ) 1 :=
    ⟨(Real.neg_one_le_cos _).trans hx.1, hx.2⟩
  have hT := Polynomial.Chebyshev.abs_iterate_derivative_T_real_le (n : ℤ) 1
    (abs_le.mpr hxunit)
  simp only [Function.iterate_one, Polynomial.Chebyshev.derivative_T_eval_one,
    Int.cast_natCast] at hT
  calc
    |p.derivative.eval x| = |∑ k ∈ s, p.eval (v k) * d k| := by
      rw [eval_derivative_eq_lagrange_sum n p hp x]
    _ ≤ ∑ k ∈ s, |p.eval (v k) * d k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, M * |d k| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (hb (v k) Polynomial.Chebyshev.node_mem_Icc) (abs_nonneg _)
    _ = M * (Polynomial.Chebyshev.T ℝ n).derivative.eval x := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ M * (n : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact (le_abs_self _).trans hT
    _ = (n : ℝ) ^ 2 * M := mul_comm _ _

/-- Assembly of the two substantive estimates: weighted Bernstein in the
center and Chebyshev interpolation in the endpoint zone. The hypotheses here
are explicit obligations; neither is assumed by a public Markov theorem. -/
theorem unit_real_bound_of_weighted_and_endpoint
    (hweighted : ∀ (n : ℕ) (p : ℝ[X]) (M : ℝ), p.natDegree ≤ n → 0 ≤ M →
      (∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) →
      ∀ x ∈ Icc (-1 : ℝ) 1,
        |p.derivative.eval x| * Real.sqrt (1 - x^2) ≤ (n : ℝ) * M)
    (hendpoint : ∀ (n : ℕ), 0 < n → ∀ (p : ℝ[X]) (M : ℝ),
      p.natDegree ≤ n → 0 ≤ M →
      (∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) →
      ∀ x ∈ Icc (Real.cos (Real.pi / (2 * n))) 1,
        |p.derivative.eval x| ≤ (n : ℝ)^2 * M)
    (n : ℕ) (p : ℝ[X]) (M : ℝ) (hp : p.natDegree ≤ n) (hM : 0 ≤ M)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |p.derivative.eval x| ≤ (n : ℝ)^2 * M := by
  by_cases hn : n = 0
  · subst n
    rw [Polynomial.derivative_of_natDegree_zero (Nat.eq_zero_of_le_zero hp)]
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let y : ℝ := Real.cos (Real.pi / (2 * n))
  by_cases hr : y ≤ x
  · exact hendpoint n hnpos p M hp hM hb x ⟨hr, hx.2⟩
  by_cases hl : x ≤ -y
  · let q : ℝ[X] := p.comp (-X)
    have hq : q.natDegree ≤ n := by
      calc
        _ ≤ p.natDegree * (-X : ℝ[X]).natDegree := Polynomial.natDegree_comp_le
        _ = p.natDegree := by simp
        _ ≤ n := hp
    have hqb : ∀ z ∈ Icc (-1 : ℝ) 1, |q.eval z| ≤ M := by
      intro z hz
      simpa [q] using hb (-z) ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have h := hendpoint n hnpos q M hq hM hqb (-x) ⟨by linarith, by linarith [hx.1]⟩
    simpa [q, Polynomial.derivative_comp] using h
  have hc : |x| ≤ y := abs_le.mpr ⟨by linarith, by linarith⟩
  have hw := hweighted n p M hp hM hb x hx
  have hlow := central_weight_lower n hnpos x hc
  have hmul := mul_le_mul_of_nonneg_left hlow (abs_nonneg (p.derivative.eval x))
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hw' := mul_le_mul_of_nonneg_left hw hnR
  nlinarith

/-- Both upstream Bernstein estimates are retained in the final assembly. -/
theorem bernstein_markov_of_unit_real_bound
    (hunit : ∀ (n : ℕ) (p : ℝ[X]) (M : ℝ), p.natDegree ≤ n → 0 ≤ M →
      (∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) →
      ∀ x ∈ Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ (n : ℝ)^2 * M) :
    Expected.bernsteinMarkovStatement :=
  ⟨bernstein_real, bernstein_complex,
    markov_real_of_unit_bound hunit, markov_complex_of_unit_bound hunit⟩

/-- Markov's sharp real estimate on [-1,1], with an arbitrary nonnegative
pointwise bound and with both endpoints included. -/
theorem real_unit_markov_bound (n : ℕ) (p : ℝ[X]) (M : ℝ)
    (hp : p.natDegree ≤ n) (hM : 0 ≤ M)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |p.derivative.eval x| ≤ (n : ℝ) ^ 2 * M :=
  unit_real_bound_of_weighted_and_endpoint real_weighted_bernstein
    real_endpoint_zone_bound n p M hp hM hb x hx

/-- The closed-interval Markov estimate for real coefficients. -/
theorem markov_real : Expected.markovRealStatement :=
  markov_real_of_unit_bound real_unit_markov_bound

/-- The same sharp closed-interval estimate for the actual complex norm. -/
theorem markov_complex : Expected.markovComplexStatement :=
  markov_complex_of_unit_bound real_unit_markov_bound

/-- Both inequalities of Theorem 1.14, for real and complex coefficients,
with the arbitrary-period and arbitrary-interval normalizations. -/
theorem bernstein_markov : Expected.bernsteinMarkovStatement :=
  ⟨bernstein_real, bernstein_complex, markov_real, markov_complex⟩

end P102.Approximation
