import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.AlgebraicSubstitution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.HyperbolicInverses
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.TrigInverses
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Substitution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.ElementaryPrimitives
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The branch substitutions of K03.09.algebraic_substitution.
We use the established identifications of the manuscript's series functions
with the canonical real functions. All root equalities are proved with the
sign of the chosen branch; positive radicands are classified separately.
-/
noncomputable section
namespace SingleVariableAnalysis.AlgebraicSubstitution
open Set
open Specs.SingleVariableAnalysis.Ch09.AlgebraicSubstitution

private theorem sine_eq : Specs.SingleVariableAnalysis.Ch07.SinCos.realSeriesSinValue =
    Real.sin := funext fun x => (sinCosSeries_eq_real x).1
private theorem cosine_eq : Specs.SingleVariableAnalysis.Ch07.SinCos.realSeriesCosValue =
    Real.cos := funext fun x => (sinCosSeries_eq_real x).2
private theorem pi_eq : Specs.SingleVariableAnalysis.Ch07.PiPeriod.analyticPiValue =
    Real.pi := PiPeriod.analyticPi_eq_pi
private theorem sinh_eq : Specs.SingleVariableAnalysis.Ch07.Hyperbolic.realSinhValue =
    Real.sinh := funext realSinh_eq_sinh
private theorem cosh_eq : Specs.SingleVariableAnalysis.Ch07.Hyperbolic.realCoshValue =
    Real.cosh := funext realCosh_eq_cosh

/-- Multiplication by a nonzero scalar transports a branch bijection. -/
theorem bijOn_scale {f : ℝ → ℝ} {D T : Set ℝ} (hf : BijOn f D T)
    {A : ℝ} (hA : A ≠ 0) :
    BijOn (fun u => A * f u) D {x | x / A ∈ T} := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    simpa only [mem_ofPred_eq, mul_div_cancel_left₀ _ hA] using hf.mapsTo hu
  · intro u hu v hv huv
    exact hf.injOn hu hv (mul_left_cancel₀ hA huv)
  · intro x hx
    obtain ⟨u, hu, he⟩ := hf.surjOn hx
    exact ⟨u, hu, by change A * f u = x; rw [he, mul_div_cancel₀ _ hA]⟩

theorem sine_change : sineChange := by
  intro A hA
  simp only [sine_eq, cosine_eq, pi_eq]
  have hb : BijOn (fun u => A * Real.sin u)
      (Ioo (-(Real.pi / 2)) (Real.pi / 2)) (Ioo (-A) A) := by
    have hs : BijOn Real.sin (Ioo (-(Real.pi / 2)) (Real.pi / 2)) (Ioo (-1) 1) :=
      Real.sinPartialHomeomorph.bijOn
    convert bijOn_scale hs hA.ne' using 1
    ext x
    change (-A < x ∧ x < A) ↔ (-1 < x / A ∧ x / A < 1)
    simp only [lt_div_iff₀ hA, div_lt_iff₀ hA, neg_one_mul, one_mul]
  refine ⟨⟨hb, ?_, ?_, ?_⟩, ?_⟩
  · exact (continuous_const.mul Real.continuous_sin).continuousOn
  · exact (continuous_const.mul Real.continuous_cos).continuousOn
  · intro u _
    exact (Real.hasDerivAt_sin u).const_mul A
  · intro u hu
    have hp := mul_pos hA (Real.cos_pos_of_mem_Ioo hu)
    refine ⟨?_, hp⟩
    have he : A ^ 2 - (A * Real.sin u) ^ 2 = (A * Real.cos u) ^ 2 := by
      rw [mul_pow, mul_pow, Real.cos_sq']
      ring
    rw [he, Real.sqrt_sq hp.le]

theorem cosh_change : coshChange := by
  intro A hA
  simp only [cosh_eq, sinh_eq]
  have hb : BijOn (fun u => A * Real.cosh u) (Ioi 0) (Ioi A) := by
    have hc : BijOn Real.cosh (Ioi 0) (Ioi 1) := Real.coshOpenPartialHomeomorph.bijOn
    convert bijOn_scale hc hA.ne' using 1
    ext x
    change A < x ↔ 1 < x / A
    simp only [lt_div_iff₀ hA, one_mul]
  refine ⟨⟨hb, ?_, ?_, ?_⟩, ?_⟩
  · exact (continuous_const.mul Real.continuous_cosh).continuousOn
  · exact (continuous_const.mul Real.continuous_sinh).continuousOn
  · intro u _
    exact (Real.hasDerivAt_cosh u).const_mul A
  · intro u hu
    have hp := mul_pos hA (Real.sinh_pos_iff.mpr hu)
    refine ⟨?_, hp⟩
    have he : (A * Real.cosh u) ^ 2 - A ^ 2 = (A * Real.sinh u) ^ 2 := by
      rw [mul_pow, mul_pow, Real.cosh_sq']
      ring
    rw [he, Real.sqrt_sq hp.le]

theorem sinh_change : sinhChange := by
  intro A hA
  simp only [sinh_eq, cosh_eq]
  have hb : BijOn (fun u => A * Real.sinh u) univ univ := by
    have hsin : BijOn Real.sinh univ univ :=
      ⟨fun _ _ => mem_univ _, fun _ _ _ _ he => Real.sinh_injective he,
        fun x _ => by obtain ⟨u, hu⟩ := Real.sinh_surjective x; exact ⟨u, mem_univ _, hu⟩⟩
    convert bijOn_scale hsin hA.ne' using 1
    ext x
    simp
  refine ⟨⟨hb, ?_, ?_, ?_⟩, ?_⟩
  · exact (continuous_const.mul Real.continuous_sinh).continuousOn
  · exact (continuous_const.mul Real.continuous_cosh).continuousOn
  · intro u _
    exact (Real.hasDerivAt_sinh u).const_mul A
  · intro u
    have hp := mul_pos hA (Real.cosh_pos u)
    refine ⟨?_, hp⟩
    have he : (A * Real.sinh u) ^ 2 + A ^ 2 = (A * Real.cosh u) ^ 2 := by
      rw [mul_pow, mul_pow, Real.cosh_sq']
      ring
    rw [he, Real.sqrt_sq hp.le]


theorem linear_root_change : linearRootChange := by
  intro α β hα
  have hid (y : ℝ) : α * ((y ^ 2 - β) / α) + β = y ^ 2 := by
    field_simp
    <;> ring
  have hinv (x : ℝ) (hx : 0 < α * x + β) :
      (Real.sqrt (α * x + β) ^ 2 - β) / α = x := by
    rw [Real.sq_sqrt hx.le]
    field_simp
    <;> ring
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro y hy
    change 0 < α * ((y ^ 2 - β) / α) + β
    rw [hid]
    exact sq_pos_of_pos hy
  · intro y hy z hz he
    have heq := congrArg (fun x => α * x + β) he
    rw [hid, hid] at heq
    exact (sq_eq_sq₀ (le_of_lt hy) (le_of_lt hz)).mp heq
  · intro x hx
    exact ⟨Real.sqrt (α * x + β), Real.sqrt_pos.mpr hx, hinv x hx⟩
  · fun_prop
  · fun_prop
  · intro y _
    convert ((hasDerivAt_pow 2 y).sub_const β).div_const α using 1 <;> simp
  · intro y hy
    rw [hid, Real.sqrt_sq hy.le]
  · intro x hx
    exact ⟨Real.sqrt_pos.mpr hx, hinv x hx⟩

theorem completing_square : completingSquare := by
  intro a b c ha x
  field_simp
  <;> ring

theorem positive_positive_quadratic : positivePositiveQuadratic := by
  intro a h r ha hr
  have hratio : 0 < r / a := div_pos hr ha
  refine ⟨Real.sqrt (r / a), Real.sqrt_pos.mpr hratio, ?_⟩
  intro x
  have he : a * (x - h) ^ 2 + r = a * ((x - h) ^ 2 + Real.sqrt (r / a) ^ 2) := by
    rw [Real.sq_sqrt hratio.le]
    field_simp
    <;> ring
  refine ⟨he, by positivity, ?_⟩
  rw [he, Real.sqrt_mul ha.le]

theorem positive_negative_quadratic : positiveNegativeQuadratic := by
  intro a h r ha hr
  have hratio : 0 < -r / a := div_pos (neg_pos.mpr hr) ha
  let A := Real.sqrt (-r / a)
  have hA : 0 < A := Real.sqrt_pos.mpr hratio
  have he (x : ℝ) : a * (x - h) ^ 2 + r = a * ((x - h) ^ 2 - A ^ 2) := by
    dsimp [A]
    rw [Real.sq_sqrt hratio.le]
    field_simp
    <;> ring
  refine ⟨A, hA, fun x => ⟨he x, ?_, ?_⟩⟩
  · rw [he x, mul_pos_iff_of_pos_left ha]
    constructor
    · intro hx
      by_contra hn
      push Not at hn
      nlinarith [sq_nonneg (x - h - A), sq_nonneg (x - h + A),
        mul_nonneg (by linarith : 0 ≤ x - h + A) (by linarith : 0 ≤ A - (x - h))]
    · rintro (hx | hx)
      · nlinarith [mul_pos (by linarith : 0 < h - x - A) (by linarith : 0 < h - x + A)]
      · nlinarith [mul_pos (by linarith : 0 < x - h - A) (by linarith : 0 < x - h + A)]
  · rw [he x, Real.sqrt_mul ha.le]

theorem negative_positive_quadratic : negativePositiveQuadratic := by
  intro a h r ha hr
  have hratio : 0 < r / (-a) := div_pos hr (neg_pos.mpr ha)
  let A := Real.sqrt (r / (-a))
  have hA : 0 < A := Real.sqrt_pos.mpr hratio
  have he (x : ℝ) : a * (x - h) ^ 2 + r = (-a) * (A ^ 2 - (x - h) ^ 2) := by
    dsimp [A]
    rw [Real.sq_sqrt hratio.le]
    field_simp [ha.ne]
    <;> ring
  refine ⟨A, hA, fun x => ⟨he x, ?_, ?_⟩⟩
  · rw [he x, mul_pos_iff_of_pos_left (neg_pos.mpr ha)]
    constructor
    · intro hx
      constructor <;> nlinarith [sq_nonneg (x - h - A), sq_nonneg (x - h + A)]
    · rintro ⟨hl, hu⟩
      nlinarith [mul_pos (by linarith : 0 < A - (x - h)) (by linarith : 0 < A + (x - h))]
  · rw [he x, Real.sqrt_mul (neg_nonneg.mpr ha.le)]

theorem negative_nonpositive_quadratic : negativeNonpositiveQuadratic := by
  intro a h r ha hr x
  exact add_nonpos (mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg _)) hr

theorem zero_residual_quadratic : zeroResidualQuadratic := by
  intro a h ha x
  have he : Real.sqrt (a * (x - h) ^ 2) = Real.sqrt a * |x - h| := by
    rw [Real.sqrt_mul ha.le, Real.sqrt_sq_eq_abs]
  refine ⟨he, ?_, ?_, ?_⟩
  · rw [mul_pos_iff_of_pos_left ha, sq_pos_iff, sub_ne_zero]
  · intro hx
    rw [he, abs_of_neg (sub_neg.mpr hx)]
    ring
  · intro hx
    rw [he, abs_of_pos (sub_pos.mpr hx)]

theorem arsinh_primitive : arsinhPrimitive := by
  intro A hA
  apply ElementaryPrimitives.formulaOn_of_hasDerivAt
  intro x _
  have hd := (realArsinh_hasDerivAt (x / A)).comp x ((hasDerivAt_id x).div_const A)
  have he : Real.sqrt (x ^ 2 + A ^ 2) = A * Real.sqrt (1 + (x / A) ^ 2) := by
    calc
      Real.sqrt (x ^ 2 + A ^ 2) = Real.sqrt (A ^ 2 * (1 + (x / A) ^ 2)) := by
        congr 1
        field_simp
        <;> ring
      _ = A * Real.sqrt (1 + (x / A) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA.le]
  convert hd using 1
  · rfl
  · rw [he]
    ring

theorem compact_substitution : compactSubstitution := by
  intro φ dφ D T hreg a b hab hsub I hI hmap
  have hc := hreg.2.1.mono hsub
  have hdc := hreg.2.2.1.mono hsub
  have hd : ∀ u ∈ Icc a b, HasDerivWithinAt φ (dφ u) (Icc a b) u :=
    fun u hu => (hreg.2.2.2 u (hsub hu)).hasDerivWithinAt
  exact ⟨fun f hf => Riemann.real_substitution φ dφ f a b I hab hc hdc hd hI hf hmap,
    fun f hf => Riemann.complex_substitution φ dφ f a b I hab hc hdc hd hI hf hmap⟩

end SingleVariableAnalysis.AlgebraicSubstitution
