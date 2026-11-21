import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.PartialFractions
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.PartialFractionInterface
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.QuadraticPrimitives
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.ElementaryPrimitives
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
K03.09.partial_fractions, paper.tex:2676–2703. The real algebraic output
comes from the upstream interface; each summand is differentiated explicitly.
The constant quadratic numerator uses the upstream finite arctangent recurrence.
For complex coefficients, polynomial component identities give a real
sum-of-squares denominator with exactly the original real zero set.
-/
noncomputable section
namespace SingleVariableAnalysis.PartialFractions
open Polynomial
open scoped BigOperators
open Specs.SingleVariableAnalysis.Ch09.PartialFractions

theorem polynomial_primitive_formula : polynomialPrimitiveFormula := by
  intro A
  apply ElementaryPrimitives.formulaOn_of_hasDerivAt
  intro x _
  have h := HasDerivAt.fun_sum (u := Finset.range (A.natDegree + 1))
    (fun j _ => ((ElementaryPrimitives.natural_power_primitive j).1 x (Set.mem_univ x)).const_mul
      (A.coeff j))
  convert h using 1
  · funext y; rfl
  · exact Polynomial.eval_eq_sum_range x

theorem completing_square : completingSquare := by
  intro b c u v h
  refine ⟨by linarith, fun x => ⟨by ring, by ring⟩⟩

/-- The reciprocal form of the negative-integer power rule, with a general
inner function. No positivity of the inner function is required. -/
lemma inverse_power_primitive_hasDerivAt {g : ℝ → ℝ} {g' x : ℝ}
    (a : ℝ) (n : ℕ) (hg : HasDerivAt g g' x) (hx : g x ≠ 0) :
    HasDerivAt (fun t => -a / (((n : ℝ) + 1) * g t ^ (n + 1)))
      (a * g' / g x ^ (n + 2)) x := by
  have hc : (n : ℝ) + 1 ≠ 0 := by positivity
  have h := (hasDerivAt_const x (-a)).div
    ((hg.pow (n + 1)).const_mul ((n : ℝ) + 1)) (mul_ne_zero hc (pow_ne_zero _ hx))
  apply h.congr_deriv
  simp only [Pi.pow_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp [hx, hc]
  ring

lemma linear_primitive_hasDerivAt (a r : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (x : ℝ) (hx : x ≠ r) :
    HasDerivAt (linearPrimitive a r k) (a / (x - r) ^ k) x := by
  have hxr : x - r ≠ 0 := sub_ne_zero.mpr hx
  match k with
  | 0 => omega
  | 1 =>
    have h := ((Real.hasDerivAt_log hxr).comp x ((hasDerivAt_id x).sub_const r)).const_mul a
    simpa only [linearPrimitive, Real.log_abs, Function.comp_def, mul_one, pow_one,
      div_eq_mul_inv, id_eq] using h
  | n + 2 =>
    simpa only [linearPrimitive, mul_one, id_eq] using
      inverse_power_primitive_hasDerivAt a n ((hasDerivAt_id x).sub_const r) hxr

theorem linear_primitive_formula : linearPrimitiveFormula := by
  intro a r k hk
  apply ElementaryPrimitives.formulaOn_of_hasDerivAt
  intro x hx
  exact linear_primitive_hasDerivAt a r k hk x hx

lemma odd_quadratic_primitive_hasDerivAt (B d : ℝ) (k : ℕ) (hd : 0 < d)
    (hk : 1 ≤ k) (y : ℝ) :
    HasDerivAt (oddQuadraticPrimitive B d k) (B * y / (y ^ 2 + d) ^ k) y := by
  have hq : y ^ 2 + d ≠ 0 := ne_of_gt (by positivity)
  have hg : HasDerivAt (fun t : ℝ => t ^ 2 + d) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).add_const d
  match k with
  | 0 => omega
  | 1 =>
    have h := ((Real.hasDerivAt_log hq).comp y hg).const_mul (B / 2)
    apply h.congr_deriv
    simp only [pow_one]
    field_simp
  | n + 2 =>
    have h := inverse_power_primitive_hasDerivAt (B / 2) n hg hq
    convert h using 1
    · funext t
      dsimp [oddQuadraticPrimitive]
      have ht : t ^ 2 + d ≠ 0 := ne_of_gt (by positivity)
      have hc : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [ht, hc]
    · ring

theorem centered_quadratic_primitive_formula : centeredQuadraticPrimitiveFormula := by
  intro B C d k hd hk
  apply ElementaryPrimitives.formulaOn_of_hasDerivAt
  intro y _
  have h := (odd_quadratic_primitive_hasDerivAt B d k hd hk y).add
    ((QuadraticPrimitives.quadratic_primitive_hasDerivAt d k hd hk y).const_mul C)
  convert h using 1
  · rfl
  · ring

theorem shifted_quadratic_primitive_formula : shiftedQuadraticPrimitiveFormula := by
  intro b c u v k hdisc hk
  obtain ⟨hd, heq⟩ := completing_square b c u v hdisc
  apply ElementaryPrimitives.formulaOn_of_hasDerivAt
  intro x _
  have h := ((centered_quadratic_primitive_formula b (c - b * u / 2)
    (v - u ^ 2 / 4) k hd hk).1 (x + u / 2) (Set.mem_univ _)).comp x
    ((hasDerivAt_id x).add_const (u / 2))
  convert h using 1
  · rfl
  · simp only [mul_one, ← (heq x).1, ← (heq x).2]

/-- The polynomial factorization keeps every linear primitive away from its
pole at each point of the original denominator domain. -/
lemma valid_factor_ne_zero (T : RealData) (P Q : ℝ[X]) (hv : T.Valid P Q)
    (x : ℝ) (hx : Q.eval x ≠ 0) (i : Fin T.n) : (T.p i).eval x ≠ 0 := by
  have hfac := hv.2.2.2.2.1
  have hprod : (∏ i, (T.p i).eval x ^ T.e i) ≠ 0 := by
    intro hz
    apply hx
    rw [hfac, eval_mul, eval_C, eval_prod]
    simp only [eval_pow]
    rw [hz, mul_zero]
  have hi := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  exact fun hz => hi (by rw [hz, zero_pow (Nat.ne_of_gt (hv.2.2.2.1 i))])

lemma real_data_hasDerivAt (T : RealData) (P Q : ℝ[X]) (hv : T.Valid P Q)
    (x : ℝ) (hx : Q.eval x ≠ 0) :
    HasDerivAt T.primitive (P.eval x / Q.eval x) x := by
  classical
  have hL : HasDerivAt (fun t =>
      ∑ i ∈ Finset.univ.filter (fun i => (T.p i).natDegree = 1),
        ∑ k : Fin (T.e i), linearPrimitive (T.a i k) (-(T.p i).coeff 0) (k.val + 1) t)
      (∑ i ∈ Finset.univ.filter (fun i => (T.p i).natDegree = 1),
        ∑ k : Fin (T.e i), T.a i k / (x - (-(T.p i).coeff 0)) ^ (k.val + 1)) x := by
    apply HasDerivAt.fun_sum
    intro i hi
    have hdeg := (Finset.mem_filter.mp hi).2
    have hp : T.p i = X - C (-(T.p i).coeff 0) := by
      rcases hv.2.2.2.2.2.1 i with h | h
      · exact h.2
      · omega
    have hxr : x ≠ -(T.p i).coeff 0 := by
      have hh := valid_factor_ne_zero T P Q hv x hx i
      have heval := congrArg (eval x) hp
      simp only [eval_sub, eval_X, eval_C] at heval
      rw [heval] at hh
      exact sub_ne_zero.mp hh
    apply HasDerivAt.fun_sum
    intro k _
    exact linear_primitive_hasDerivAt _ _ _ (by omega) x hxr
  have hR : HasDerivAt (fun t =>
      ∑ i ∈ Finset.univ.filter (fun i => (T.p i).natDegree = 2),
        ∑ k : Fin (T.e i), shiftedQuadraticPrimitive (T.b i k) (T.c i k)
          ((T.p i).coeff 1) ((T.p i).coeff 0) (k.val + 1) t)
      (∑ i ∈ Finset.univ.filter (fun i => (T.p i).natDegree = 2),
        ∑ k : Fin (T.e i), (T.b i k * x + T.c i k) /
          (x ^ 2 + (T.p i).coeff 1 * x + (T.p i).coeff 0) ^ (k.val + 1)) x := by
    apply HasDerivAt.fun_sum
    intro i hi
    have hdeg := (Finset.mem_filter.mp hi).2
    have hd : (T.p i).coeff 1 ^ 2 - 4 * (T.p i).coeff 0 < 0 := by
      rcases hv.2.2.2.2.2.1 i with h | h
      · omega
      · exact h.2.2
    apply HasDerivAt.fun_sum
    intro k _
    exact (shifted_quadratic_primitive_formula _ _ _ _ _ hd (by omega)).1 x (Set.mem_univ x)
  have h := (((polynomial_primitive_formula T.A).1 x (Set.mem_univ x)).add hL).add hR
  change HasDerivAt T.primitive (T.integrand x) x at h
  rw [← hv.2.2.2.2.2.2 x hx] at h
  exact h

theorem real_rational_primitive : realRationalPrimitive := by
  intro P Q hQ
  obtain ⟨n, p, e, A, a, b, c, hm, hi, hinj, he, hfac, hclass, heq⟩ :=
    PartialFractionInterface.real_partial_fractions P Q hQ
  let T : RealData := ⟨n, p, e, A, a, b, c⟩
  have hv : T.Valid P Q := ⟨hm, hi, hinj, he, hfac, hclass, heq⟩
  refine ⟨T, hv, ?_⟩
  apply ElementaryPrimitives.formulaOn_of_hasDerivAt
  intro x hx
  exact real_data_hasDerivAt T P Q hv x hx

lemma complex_polynomial_components (P : ℂ[X]) :
    ∃ A B : ℝ[X], P = A.map Complex.ofRealHom + B.map Complex.ofRealHom * C Complex.I := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨A, B, hP⟩ := hP
    obtain ⟨D, E, hQ⟩ := hQ
    refine ⟨A + D, B + E, ?_⟩
    simp only [Polynomial.map_add, hP, hQ]
    ring
  | monomial n z =>
    refine ⟨monomial n z.re, monomial n z.im, ?_⟩
    ext j
    simp only [coeff_add, coeff_map, coeff_mul_C, coeff_monomial]
    split_ifs <;> simp [Complex.re_add_im]

lemma components_eval {P : ℂ[X]} {A B : ℝ[X]}
    (h : P = A.map Complex.ofRealHom + B.map Complex.ofRealHom * C Complex.I) (x : ℝ) :
    P.eval (x : ℂ) = ((A.eval x : ℝ) : ℂ) + ((B.eval x : ℝ) : ℂ) * Complex.I := by
  rw [h, eval_add, eval_mul, eval_C, eval_map, eval_map]
  have hA : A.eval₂ Complex.ofRealHom (x : ℂ) = ((A.eval x : ℝ) : ℂ) :=
    Polynomial.eval₂_at_apply Complex.ofRealHom x
  have hB : B.eval₂ Complex.ofRealHom (x : ℂ) = ((B.eval x : ℝ) : ℂ) :=
    Polynomial.eval₂_at_apply Complex.ofRealHom x
  rw [hA, hB]

lemma component_denominator_nonzero {Q : ℂ[X]} {A B : ℝ[X]}
    (hQ : Q ≠ 0) (h : Q = A.map Complex.ofRealHom + B.map Complex.ofRealHom * C Complex.I) :
    A ^ 2 + B ^ 2 ≠ 0 := by
  intro hz
  have he (x : ℝ) : (A.eval x) ^ 2 + (B.eval x) ^ 2 = 0 := by
    simpa only [eval_add, eval_pow, eval_zero] using congrArg (eval x) hz
  have hA : A = 0 := Polynomial.funext fun x => by
    simp only [eval_zero]
    nlinarith [he x, sq_nonneg (A.eval x), sq_nonneg (B.eval x)]
  have hB : B = 0 := Polynomial.funext fun x => by
    simp only [eval_zero]
    nlinarith [he x, sq_nonneg (A.eval x), sq_nonneg (B.eval x)]
  exact hQ (by simpa [hA, hB] using h)

lemma component_denominator_eval {Q : ℂ[X]} {A B : ℝ[X]}
    (h : Q = A.map Complex.ofRealHom + B.map Complex.ofRealHom * C Complex.I) (x : ℝ) :
    (A ^ 2 + B ^ 2).eval x = Complex.normSq (Q.eval (x : ℂ)) := by
  rw [components_eval h x]
  simp [Complex.normSq_apply, pow_two]

lemma component_quotient_eval {P Q : ℂ[X]} {A B C D : ℝ[X]}
    (hP : P = A.map Complex.ofRealHom + B.map Complex.ofRealHom * Polynomial.C Complex.I)
    (hQ : Q = C.map Complex.ofRealHom + D.map Complex.ofRealHom * Polynomial.C Complex.I)
    (x : ℝ) :
    (P.eval (x : ℂ) / Q.eval (x : ℂ)).re = (A * C + B * D).eval x / (C ^ 2 + D ^ 2).eval x ∧
    (P.eval (x : ℂ) / Q.eval (x : ℂ)).im = (B * C - A * D).eval x / (C ^ 2 + D ^ 2).eval x := by
  rw [components_eval hP x, components_eval hQ x]
  constructor <;> simp [Complex.div_re, Complex.div_im, Complex.normSq_apply, pow_two,
    add_div, sub_eq_add_neg, add_comm, neg_div]

/-- Multiply by the conjugate denominator in real coordinates, apply the
real reduction twice, and lift both real derivatives with real increments. -/
theorem complex_rational_primitive : complexRationalPrimitive := by
  intro P Q hQ
  obtain ⟨A, B, hP⟩ := complex_polynomial_components P
  obtain ⟨C, E, hQc⟩ := complex_polynomial_components Q
  let D : ℝ[X] := C ^ 2 + E ^ 2
  let R : ℝ[X] := A * C + B * E
  let S : ℝ[X] := B * C - A * E
  have hD : D ≠ 0 := component_denominator_nonzero hQ hQc
  have hdom (x : ℝ) : Q.eval (x : ℂ) ≠ 0 ↔ D.eval x ≠ 0 := by
    rw [component_denominator_eval hQc x]
    exact not_congr Complex.normSq_eq_zero.symm
  have hparts (x : ℝ) :
      (P.eval (x : ℂ) / Q.eval (x : ℂ)).re = R.eval x / D.eval x ∧
      (P.eval (x : ℂ) / Q.eval (x : ℂ)).im = S.eval x / D.eval x :=
    component_quotient_eval hP hQc x
  obtain ⟨U, hU, hUF⟩ := real_rational_primitive R D hD
  obtain ⟨V, hV, hVF⟩ := real_rational_primitive S D hD
  refine ⟨R, S, D, U, V, hD, hU, hV, hdom, fun x _ => hparts x, hUF, hVF, ?_⟩
  apply ElementaryPrimitives.complexFormulaOn_of_hasDerivAt
  intro x hx
  have hdx := (hdom x).mp hx
  have h := ((hUF.1 x hdx).ofReal_comp).add (((hVF.1 x hdx).ofReal_comp).mul_const Complex.I)
  apply h.congr_deriv
  apply Complex.ext
  · simpa using (hparts x).1.symm
  · simpa using (hparts x).2.symm

end SingleVariableAnalysis.PartialFractions
