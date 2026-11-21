import MathGenome.Internal.FourierSobolev.P102.Approximation.JacksonInverse
import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.JacksonInterval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

noncomputable section
open Set
open scoped Real ComplexConjugate

namespace P102.Approximation.JacksonInterval

open P102.Periodic
open P102.Approximation.JacksonInterval.Expected (Interval polynomialMap)

abbrev modulus := @Expected.modulusValue
abbrev bestError := @Expected.bestErrorValue

section IntervalBounds
variable {E : Type*} [NormedAddCommGroup E] (a b : ℝ) (f : C(Interval a b, E))

theorem increments_bddAbove (δ : ℝ) :
    BddAbove {r : ℝ | ∃ x y : Interval a b, dist x y ≤ δ ∧ r = ‖f x - f y‖} := by
  refine ⟨2 * ‖f‖, ?_⟩
  rintro r ⟨x, y, hxy, rfl⟩
  exact (norm_sub_le _ _).trans (by linarith [f.norm_coe_le_norm x, f.norm_coe_le_norm y])

theorem norm_sub_le_modulus {δ : ℝ} {x y : Interval a b} (hxy : dist x y ≤ δ) :
    ‖f x - f y‖ ≤ modulus a b f δ :=
  le_csSup (increments_bddAbove a b f δ) ⟨x, y, hxy, rfl⟩

theorem modulus_nonnegative (hab : a ≤ b) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ modulus a b f δ := by
  let x : Interval a b := ⟨a, le_rfl, hab⟩
  simpa using norm_sub_le_modulus a b f (x := x) (y := x) (by simpa using hδ)

end IntervalBounds

section BestError
variable {𝕜 : Type*} [RCLike 𝕜] (a b : ℝ) (f : C(Interval a b, 𝕜))

theorem errorSet_bddBelow (n : ℕ) :
    BddBelow {r : ℝ | ∃ p : Polynomial 𝕜, p.natDegree ≤ n ∧
      r = ‖f - polynomialMap a b p‖} := by
  refine ⟨0, ?_⟩
  rintro r ⟨p, hp, rfl⟩
  exact norm_nonneg _

theorem bestError_le_error {n : ℕ} (p : Polynomial 𝕜) (hp : p.natDegree ≤ n) :
    bestError a b f n ≤ ‖f - polynomialMap a b p‖ :=
  csInf_le (errorSet_bddBelow a b f n) ⟨p, hp, rfl⟩

theorem bestError_nonnegative (n : ℕ) : 0 ≤ bestError a b f n := by
  apply le_csInf (show {r : ℝ | ∃ p : Polynomial 𝕜, p.natDegree ≤ n ∧
    r = ‖f - polynomialMap a b p‖}.Nonempty from
    ⟨_, 0, by simp, rfl⟩)
  rintro r ⟨p, hp, rfl⟩
  exact norm_nonneg _

theorem singleton_error (a : ℝ) (n : ℕ) (f : C(Interval a a, 𝕜)) :
    bestError a a f n = 0 := by
  let x : Interval a a := ⟨a, le_rfl, le_rfl⟩
  have heq : f = polynomialMap a a (Polynomial.C (f x)) := by
    ext y
    have hy : y = x := Subtype.ext (le_antisymm y.2.2 y.2.1)
    simp [polynomialMap, hy]
  apply le_antisymm
  · have h := bestError_le_error a a f (Polynomial.C (f x)) (n := n) (by simp)
    simpa [← heq] using h
  · exact bestError_nonnegative a a f n

end BestError

theorem singleton_exact : Expected.singletonStatement := by
  intro a n
  exact ⟨singleton_error a n, singleton_error a n⟩

abbrev AngularCircle := Circle (2 * Real.pi)

/-- Cosine as a continuous function on the angular circle. -/
def cosine : C(AngularCircle, ℝ) :=
  ⟨fun x => (mode (2 * Real.pi) 1 x).re, by fun_prop⟩

def sine : C(AngularCircle, ℝ) :=
  ⟨fun x => (mode (2 * Real.pi) 1 x).im, by fun_prop⟩

@[simp] theorem cosine_coe (v : ℝ) : cosine (v : AngularCircle) = Real.cos v := by
  change (mode (2 * Real.pi) 1 (v : AngularCircle)).re = _
  rw [angular_mode]
  simp [Complex.exp_re]

@[simp] theorem sine_coe (v : ℝ) : sine (v : AngularCircle) = Real.sin v := by
  change (mode (2 * Real.pi) 1 (v : AngularCircle)).im = _
  rw [angular_mode]
  simp [Complex.exp_im]

@[simp] theorem cosine_neg (x : AngularCircle) : cosine (-x) = cosine x := by
  induction x using QuotientAddGroup.induction_on with
  | H v => simpa only [← QuotientAddGroup.mk_neg, cosine_coe] using Real.cos_neg v

theorem cosine_bounds (x : AngularCircle) : -1 ≤ cosine x ∧ cosine x ≤ 1 := by
  induction x using QuotientAddGroup.induction_on with
  | H v => simpa only [cosine_coe, mem_Icc] using Real.cos_mem_Icc v

theorem cosine_increment (x y : AngularCircle) :
    ‖cosine x - cosine y‖ ≤ dist x y := by
  have hq : ∀ t : ℝ, HasDerivAt (fun s : ℝ => cosine (s : AngularCircle))
      ((-sine) (t : AngularCircle)) t := by
    intro t
    simpa only [cosine_coe, ContinuousMap.neg_apply, sine_coe] using Real.hasDerivAt_cos t
  have hb : ‖-sine‖ ≤ (1 : ℝ) := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H v => simpa [Real.norm_eq_abs] using Real.abs_sin_le_one v
  simpa using JacksonInverse.circle_increment_of_derivative (2 * Real.pi)
    cosine (-sine) hq 1 zero_le_one hb x y

/-- The cosine parametrization of the entire compact interval. -/
def cosineInterval (a b : ℝ) (hab : a ≤ b) : C(AngularCircle, Interval a b) :=
  ⟨fun v => ⟨(a + b) / 2 + ((b - a) / 2) * cosine v, by
    have hc := cosine_bounds v
    have hd : 0 ≤ (b - a) / 2 := by linarith
    constructor <;> nlinarith [mul_nonneg hd (by linarith : 0 ≤ cosine v + 1),
      mul_nonneg hd (by linarith : 0 ≤ 1 - cosine v)]⟩, by fun_prop⟩

theorem cosineInterval_neg (a b : ℝ) (hab : a ≤ b) (v : AngularCircle) :
    cosineInterval a b hab (-v) = cosineInterval a b hab v := by
  apply Subtype.ext
  simp [cosineInterval]

theorem cosineInterval_distance (a b : ℝ) (hab : a ≤ b) (x y : AngularCircle) :
    dist (cosineInterval a b hab x) (cosineInterval a b hab y) ≤
      ((b - a) / 2) * dist x y := by
  have hd : 0 ≤ (b - a) / 2 := by linarith
  calc
    _ = ((b - a) / 2) * ‖cosine x - cosine y‖ := by
      simp only [Subtype.dist_eq, Real.dist_eq, cosineInterval, ContinuousMap.coe_mk]
      rw [show (a + b) / 2 + (b - a) / 2 * cosine x -
        ((a + b) / 2 + (b - a) / 2 * cosine y) =
        (b - a) / 2 * (cosine x - cosine y) by ring, abs_mul, abs_of_nonneg hd,
        Real.norm_eq_abs]
    _ ≤ _ := mul_le_mul_of_nonneg_left (cosine_increment x y) hd

theorem cosineLift_modulus {E : Type*} [NormedAddCommGroup E]
    (a b : ℝ) (hab : a ≤ b) (f : C(Interval a b, E)) {δ : ℝ} (hδ : 0 ≤ δ) :
    JacksonPeriodic.modulus (2 * Real.pi) (f.comp (cosineInterval a b hab)) δ ≤
      modulus a b f (((b - a) / 2) * δ) := by
  apply JacksonPeriodic.modulus_le _ _ hδ
  intro x y hxy
  apply norm_sub_le_modulus a b f
  exact (cosineInterval_distance a b hab x y).trans
    (mul_le_mul_of_nonneg_left hxy (by linarith))

/-- Averaging a Fourier mode and its reflection removes its sine part. -/
theorem average_mode (k : ℤ) (v : ℝ) :
    (mode (2 * Real.pi) k (v : AngularCircle) +
      mode (2 * Real.pi) k ((-v : ℝ) : AngularCircle)) / 2 =
      (Real.cos ((k : ℝ) * v) : ℂ) := by
  rw [angular_mode, angular_mode, Complex.ofReal_cos]
  push_cast
  rw [show Complex.I * (k : ℂ) * v = ((k : ℂ) * v) * Complex.I by ring,
    show Complex.I * (k : ℂ) * -(v : ℂ) = -((k : ℂ) * v) * Complex.I by ring,
    ← Complex.two_cos]
  ring

/-- The algebraic polynomial representing the even part of a finite Fourier sum. -/
def cosinePolynomial (c : ℤ →₀ ℂ) : Polynomial ℂ :=
  ∑ k ∈ c.support, Polynomial.C (c k) * Polynomial.Chebyshev.T ℂ k

def realCosinePolynomial (c : ℤ →₀ ℂ) : Polynomial ℝ :=
  ∑ k ∈ c.support, Polynomial.C (c k).re * Polynomial.Chebyshev.T ℝ k

theorem cosinePolynomial_degree {n : ℕ} (c : ℤ →₀ ℂ)
    (hc : c ∈ Finsupp.supported ℂ ℂ (Icc (-(n : ℤ)) (n : ℤ))) :
    (cosinePolynomial c).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [Polynomial.Chebyshev.natDegree_T]
  obtain ⟨hk₁, hk₂⟩ := (Finsupp.mem_supported ℂ c).mp hc hk
  omega

theorem realCosinePolynomial_degree {n : ℕ} (c : ℤ →₀ ℂ)
    (hc : c ∈ Finsupp.supported ℂ ℂ (Icc (-(n : ℤ)) (n : ℤ))) :
    (realCosinePolynomial c).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [Polynomial.Chebyshev.natDegree_T]
  obtain ⟨hk₁, hk₂⟩ := (Finsupp.mem_supported ℂ c).mp hc hk
  omega

theorem cosinePolynomial_eval (c : ℤ →₀ ℂ) (v : ℝ) :
    (cosinePolynomial c).eval (Real.cos v : ℂ) =
      (synthesis (2 * Real.pi) c (v : AngularCircle) +
        synthesis (2 * Real.pi) c ((-v : ℝ) : AngularCircle)) / 2 := by
  classical
  rw [synth_sum, synth_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  simp only [cosinePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, ← Polynomial.Chebyshev.complex_ofReal_eval_T,
    Polynomial.Chebyshev.T_real_cos]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← average_mode]
  ring

theorem realCosinePolynomial_eval (c : ℤ →₀ ℂ) (v : ℝ) :
    (realCosinePolynomial c).eval (Real.cos v) =
      (realSynthesis (2 * Real.pi) c (v : AngularCircle) +
        realSynthesis (2 * Real.pi) c ((-v : ℝ) : AngularCircle)) / 2 := by
  have heq : (realCosinePolynomial c).eval (Real.cos v) =
      ((cosinePolynomial c).eval (Real.cos v : ℂ)).re := by
    simp only [cosinePolynomial, realCosinePolynomial, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C,
      ← Polynomial.Chebyshev.complex_ofReal_eval_T, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [heq, cosinePolynomial_eval]
  simp [realSynthesis]

section AffinePolynomial
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Change from the cosine coordinate to the original interval coordinate. -/
def intervalPolynomial (a b : ℝ) (p : Polynomial 𝕜) : Polynomial 𝕜 :=
  p.comp (Polynomial.C (algebraMap ℝ 𝕜 (((b - a) / 2)⁻¹)) *
    (Polynomial.X - Polynomial.C (algebraMap ℝ 𝕜 ((a + b) / 2))))

theorem intervalPolynomial_degree (a b : ℝ) {n : ℕ} (p : Polynomial 𝕜)
    (hp : p.natDegree ≤ n) : (intervalPolynomial a b p).natDegree ≤ n := by
  have hlinear : (Polynomial.C (algebraMap ℝ 𝕜 (((b - a) / 2)⁻¹)) *
      (Polynomial.X - Polynomial.C (algebraMap ℝ 𝕜 ((a + b) / 2)))).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  exact Polynomial.natDegree_comp_le.trans
    ((Nat.mul_le_mul hp hlinear).trans_eq (Nat.mul_one n))

theorem intervalPolynomial_eval (a b : ℝ) (hab : a < b) (p : Polynomial 𝕜) (v : ℝ) :
    (intervalPolynomial a b p).eval
        (algebraMap ℝ 𝕜 ((a + b) / 2 + ((b - a) / 2) * Real.cos v)) =
      p.eval (algebraMap ℝ 𝕜 (Real.cos v)) := by
  have hd : (b - a) / 2 ≠ 0 := by linarith
  simp only [intervalPolynomial, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    ← map_sub, ← map_mul]
  congr 2
  field_simp
  ring

/-- Averaging reflected approximants preserves a bound for an even function. -/
theorem norm_sub_average_le (F p : C(AngularCircle, 𝕜))
    (hF : ∀ x, F (-x) = F x) (x : AngularCircle) :
    ‖F x - (p x + p (-x)) / 2‖ ≤ ‖F - p‖ := by
  have hx := (F - p).norm_coe_le_norm x
  have hy := (F - p).norm_coe_le_norm (-x)
  change ‖F x - p x‖ ≤ ‖F - p‖ at hx
  change ‖F (-x) - p (-x)‖ ≤ ‖F - p‖ at hy
  rw [show F x - (p x + p (-x)) / 2 =
    ((F x - p x) + (F (-x) - p (-x))) / 2 by rw [hF]; ring,
    norm_div]
  have hn : ‖(2 : 𝕜)‖ = (2 : ℝ) := by norm_num
  rw [hn]
  have h := norm_add_le (F x - p x) (F (-x) - p (-x))
  linarith

end AffinePolynomial

/-- Every interval point has a cosine preimage; this also preserves sup errors. -/
theorem cosineInterval_surjective (a b : ℝ) (hab : a < b) (x : Interval a b) :
    ∃ v : ℝ, cosineInterval a b hab.le (v : AngularCircle) = x := by
  let z := ((x : ℝ) - (a + b) / 2) / ((b - a) / 2)
  have hd : 0 < (b - a) / 2 := by linarith
  have hz : -1 ≤ z ∧ z ≤ 1 := by
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith [x.2.1]
    · apply (div_le_iff₀ hd).mpr
      linarith [x.2.2]
  refine ⟨Real.arccos z, Subtype.ext ?_⟩
  change (a + b) / 2 + ((b - a) / 2) * cosine ((Real.arccos z : ℝ) : AngularCircle) = _
  rw [cosine_coe, Real.cos_arccos hz.1 hz.2]
  dsimp [z]
  rw [mul_div_cancel₀ _ hd.ne']
  ring

/-- The even part of a complex trigonometric approximant gives an algebraic
approximant of the same degree, with no increase in uniform error. -/
theorem complex_polynomial_bridge (a b : ℝ) (hab : a < b)
    (f : C(Interval a b, ℂ)) (n : ℕ) (p : C(AngularCircle, ℂ))
    (hp : p ∈ complexTrigDegree (2 * Real.pi) n) :
    ∃ q : Polynomial ℂ, q.natDegree ≤ n ∧
      ‖f - polynomialMap a b q‖ ≤ ‖f.comp (cosineInterval a b hab.le) - p‖ := by
  obtain ⟨c, hc, hcp⟩ := hp
  let q := intervalPolynomial a b (cosinePolynomial c)
  refine ⟨q, intervalPolynomial_degree a b _ (cosinePolynomial_degree c hc), ?_⟩
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  obtain ⟨v, hv⟩ := cosineInterval_surjective a b hab x
  have hval : polynomialMap a b q x =
      (p (v : AngularCircle) + p ((-v : ℝ) : AngularCircle)) / 2 := by
    rw [← hv]
    change q.eval (( (a + b) / 2 + ((b - a) / 2) * cosine (v : AngularCircle) : ℝ) : ℂ) = _
    rw [cosine_coe]
    change (intervalPolynomial a b (cosinePolynomial c)).eval
      (algebraMap ℝ ℂ ((a + b) / 2 + ((b - a) / 2) * Real.cos v)) = _
    rw [intervalPolynomial_eval (𝕜 := ℂ) a b hab]
    change (cosinePolynomial c).eval (Real.cos v : ℂ) = _
    rw [cosinePolynomial_eval, hcp]
  change ‖f x - polynomialMap a b q x‖ ≤ _
  rw [hval, ← hv]
  simpa only [ContinuousMap.comp_apply, ← QuotientAddGroup.mk_neg] using
    norm_sub_average_le (f.comp (cosineInterval a b hab.le)) p
      (by intro y; simp only [ContinuousMap.comp_apply, cosineInterval_neg])
      (v : AngularCircle)

/-- Real coefficients are retained by taking the real part of each Fourier
coefficient in the Chebyshev expansion. -/
theorem real_polynomial_bridge (a b : ℝ) (hab : a < b)
    (f : C(Interval a b, ℝ)) (n : ℕ) (p : C(AngularCircle, ℝ))
    (hp : p ∈ realTrigDegree (2 * Real.pi) n) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ n ∧
      ‖f - polynomialMap a b q‖ ≤ ‖f.comp (cosineInterval a b hab.le) - p‖ := by
  obtain ⟨c, ⟨hc, hsym⟩, hcp⟩ := hp
  let q := intervalPolynomial a b (realCosinePolynomial c)
  refine ⟨q, intervalPolynomial_degree a b _ (realCosinePolynomial_degree c hc), ?_⟩
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  obtain ⟨v, hv⟩ := cosineInterval_surjective a b hab x
  have hval : polynomialMap a b q x =
      (p (v : AngularCircle) + p ((-v : ℝ) : AngularCircle)) / 2 := by
    rw [← hv]
    change q.eval ((a + b) / 2 + ((b - a) / 2) * cosine (v : AngularCircle)) = _
    rw [cosine_coe]
    change (intervalPolynomial a b (realCosinePolynomial c)).eval
      (algebraMap ℝ ℝ ((a + b) / 2 + ((b - a) / 2) * Real.cos v)) = _
    rw [intervalPolynomial_eval (𝕜 := ℝ) a b hab]
    change (realCosinePolynomial c).eval (Real.cos v) = _
    rw [realCosinePolynomial_eval, hcp]
  change ‖f x - polynomialMap a b q x‖ ≤ _
  rw [hval, ← hv]
  simpa only [ContinuousMap.comp_apply, ← QuotientAddGroup.mk_neg] using
    norm_sub_average_le (f.comp (cosineInterval a b hab.le)) p
      (by intro y; simp only [ContinuousMap.comp_apply, cosineInterval_neg])
      (v : AngularCircle)

theorem interval_scale_bound (a b : ℝ) (hab : a ≤ b) (n : ℕ) (hn : 1 ≤ n) :
    ((b - a) / 2) * (1 / ((n / 2 + 1 : ℕ) : ℝ)) ≤ (b - a) / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hnm : (n : ℝ) ≤ 2 * ((n / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * (n / 2 + 1) by omega)
  calc
    _ = (b - a) / (2 * ((n / 2 + 1 : ℕ) : ℝ)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hnpos hnm

theorem cosineLift_modulus_at_degree {E : Type*} [NormedAddCommGroup E]
    (a b : ℝ) (hab : a ≤ b) (f : C(Interval a b, E)) (n : ℕ) (hn : 1 ≤ n) :
    JacksonPeriodic.modulus (2 * Real.pi) (f.comp (cosineInterval a b hab))
        (1 / ((n / 2 + 1 : ℕ) : ℝ)) ≤
      modulus a b f ((b - a) / (n : ℝ)) := by
  apply JacksonPeriodic.modulus_le _ _ (by positivity)
  intro x y hxy
  apply norm_sub_le_modulus a b f
  exact (cosineInterval_distance a b hab x y).trans
    ((mul_le_mul_of_nonneg_left hxy (by linarith)).trans (interval_scale_bound a b hab n hn))

/-- Algebraic Jackson estimate, with one absolute constant for both fields and
all nondegenerate real intervals. -/
theorem direct_estimate : Expected.directStatement := by
  obtain ⟨C, hC, happrox⟩ := JacksonPeriodic.angular_approximation
  refine ⟨C, hC, ?_⟩
  intro a b hab n hn
  let m := n / 2 + 1
  have hm : 1 ≤ m := by omega
  have hdeg : 2 * m - 2 ≤ n := by omega
  constructor
  · intro f
    let F := f.comp (cosineInterval a b hab.le)
    obtain ⟨p, hp, herr⟩ := (happrox m hm).1 F
    obtain ⟨q, hq, hbridge⟩ := real_polynomial_bridge a b hab f (2 * m - 2) p hp
    exact (bestError_le_error a b f q (hq.trans hdeg)).trans
      (hbridge.trans (herr.trans (mul_le_mul_of_nonneg_left
        (cosineLift_modulus_at_degree a b hab.le f n hn) hC)))
  · intro f
    let F := f.comp (cosineInterval a b hab.le)
    obtain ⟨p, hp, herr⟩ := (happrox m hm).2 F
    obtain ⟨q, hq, hbridge⟩ := complex_polynomial_bridge a b hab f (2 * m - 2) p hp
    exact (bestError_le_error a b f q (hq.trans hdeg)).trans
      (hbridge.trans (herr.trans (mul_le_mul_of_nonneg_left
        (cosineLift_modulus_at_degree a b hab.le f n hn) hC)))

/-- All assertions of Theorem 1.15, including the periodic inverse and the
singleton boundary case. -/
theorem jackson_estimates : Expected.jacksonStatement :=
  ⟨JacksonPeriodic.direct_estimate, JacksonInverse.equivalence,
    direct_estimate, singleton_exact⟩

end P102.Approximation.JacksonInterval
