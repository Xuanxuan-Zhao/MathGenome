import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.Weierstrass
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Higher
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.SmoothDensity

/-!
K03.16.smooth_density. Choose polynomials with errors < 1/(n+1).
Their evaluations are globally smooth with respect to real increments,
so their restrictions give smooth approximation on a neighborhood of the
whole interval. The converse is the continuity theorem for uniform limits;
smoothness on any open neighborhood supplies continuity on the interval.
-/
noncomputable section
namespace SingleVariableAnalysis
open scoped ContDiff

/-- Every real polynomial is smooth on the whole real line, in the shared
iterated-real-derivative definition. -/
theorem realPolynomial_smooth (p : Polynomial ℝ) :
    SmoothOn (fun x : ℝ => p.eval x) Set.univ := by
  apply (smoothOn_iff_contDiffOn _ _ isOpen_univ).mpr
  have h : ContDiff ℝ ∞ (fun x : ℝ => p.eval x) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
    | monomial n a =>
        simpa only [Polynomial.eval_monomial] using
          (contDiff_const.mul (contDiff_id.pow n) :
            ContDiff ℝ ∞ (fun x : ℝ => a * x ^ n))
  exact h.contDiffOn

/-- Complex polynomial evaluation at real arguments has derivatives of all
orders with respect to ℝ. -/
theorem complexPolynomial_smooth (p : Polynomial ℂ) :
    SmoothOn (fun x : ℝ => p.eval (x : ℂ)) Set.univ := by
  apply (smoothOn_iff_contDiffOn _ _ isOpen_univ).mpr
  have h : ContDiff ℝ ∞ (fun x : ℝ => p.eval (x : ℂ)) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
    | monomial n a =>
        simpa only [Polynomial.eval_monomial, Complex.ofRealCLM_apply] using
          (contDiff_const.mul (Complex.ofRealCLM.contDiff.pow n) :
            ContDiff ℝ ∞ (fun x : ℝ => a * Complex.ofRealCLM x ^ n))
  exact h.contDiffOn

theorem real_smooth_polynomial_density (a b : ℝ) (hab : a ≤ b)
    (f : C(Set.Icc a b, ℝ)) :
    ∃ p : ℕ → Polynomial ℝ,
      (∀ n, SmoothOn (fun x : ℝ => (p n).eval x) Set.univ) ∧
      RealUniformConverges (fun n (x : Set.Icc a b) => (p n).eval (x : ℝ)) f := by
  have happ (n : ℕ) := real_weierstrass_approximation a b hab f
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose p hp using happ
  refine ⟨p, fun n => realPolynomial_smooth (p n), ?_⟩
  intro ε hε
  obtain ⟨N, _, hN⟩ := reciprocal_tail ε hε
  refine ⟨N, fun n hn x => ?_⟩
  have hpoint := (ContinuousMap.norm_lt_iff _ (by positivity :
    0 < 1 / ((n : ℝ) + 1))).mp (hp n) x
  have herror : |(p n).eval (x : ℝ) - f x| < 1 / ((n : ℝ) + 1) := by
    simpa only [ContinuousMap.sub_apply, ContinuousMap.coe_mk, Real.norm_eq_abs,
      abs_sub_comm] using hpoint
  have htail := hN (n + 1) (by omega)
  have hrecip : 1 / ((n : ℝ) + 1) < ε := by
    simpa only [Nat.cast_add, Nat.cast_one, abs_of_pos (by positivity :
      0 < 1 / ((n : ℝ) + 1))] using htail
  exact herror.trans hrecip

theorem complex_smooth_polynomial_density (a b : ℝ) (hab : a ≤ b)
    (f : C(Set.Icc a b, ℂ)) :
    ∃ p : ℕ → Polynomial ℂ,
      (∀ n, SmoothOn (fun x : ℝ => (p n).eval (x : ℂ)) Set.univ) ∧
      ComplexUniformConverges
        (fun n (x : Set.Icc a b) => (p n).eval ((x : ℝ) : ℂ)) f := by
  have happ (n : ℕ) := complex_weierstrass_approximation a b hab f
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose p hp using happ
  refine ⟨p, fun n => complexPolynomial_smooth (p n), ?_⟩
  intro ε hε
  obtain ⟨N, _, hN⟩ := reciprocal_tail ε hε
  refine ⟨N, fun n hn x => ?_⟩
  have hpoint := (ContinuousMap.norm_lt_iff _ (by positivity :
    0 < 1 / ((n : ℝ) + 1))).mp (hp n) x
  have herror : ‖(p n).eval ((x : ℝ) : ℂ) - f x‖ < 1 / ((n : ℝ) + 1) := by
    simpa only [ContinuousMap.sub_apply, ContinuousMap.coe_mk, norm_sub_rev] using hpoint
  have htail := hN (n + 1) (by omega)
  have hrecip : 1 / ((n : ℝ) + 1) < ε := by
    simpa only [Nat.cast_add, Nat.cast_one, abs_of_pos (by positivity :
      0 < 1 / ((n : ℝ) + 1))] using htail
  exact herror.trans hrecip

theorem real_discontinuous_no_continuous_limit (a b : ℝ) (f : Set.Icc a b → ℝ)
    (hf : ¬ Continuous f) :
    ¬ ∃ F : ℕ → Set.Icc a b → ℝ,
      (∀ n, Continuous (F n)) ∧ RealUniformConverges F f := by
  rintro ⟨F, hF, hlim⟩
  exact hf (realUniformLimit_continuous F f hF hlim)

theorem complex_discontinuous_no_continuous_limit (a b : ℝ) (f : Set.Icc a b → ℂ)
    (hf : ¬ Continuous f) :
    ¬ ∃ F : ℕ → Set.Icc a b → ℂ,
      (∀ n, Continuous (F n)) ∧ ComplexUniformConverges F f := by
  rintro ⟨F, hF, hlim⟩
  exact hf (complexUniformLimit_continuous F f hF hlim)

theorem real_discontinuous_no_smooth_limit (a b : ℝ) (f : Set.Icc a b → ℝ)
    (hf : ¬ Continuous f) :
    ¬ ∃ F : ℕ → ℝ → ℝ,
      (∀ n, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc a b ⊆ U ∧ SmoothOn (F n) U) ∧
      RealUniformConverges (fun n (x : Set.Icc a b) => F n x) f := by
  rintro ⟨F, hF, hlim⟩
  apply real_discontinuous_no_continuous_limit a b f hf
  refine ⟨fun n (x : Set.Icc a b) => F n x, ?_, hlim⟩
  intro n
  obtain ⟨U, _, hsub, hsmooth⟩ := hF n
  exact continuousOn_iff_continuous_domRestrict.mp
    (((ckOn_zero_iff (F n) U).mp (hsmooth 0)).mono hsub)

theorem complex_discontinuous_no_smooth_limit (a b : ℝ) (f : Set.Icc a b → ℂ)
    (hf : ¬ Continuous f) :
    ¬ ∃ F : ℕ → ℝ → ℂ,
      (∀ n, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc a b ⊆ U ∧ SmoothOn (F n) U) ∧
      ComplexUniformConverges (fun n (x : Set.Icc a b) => F n x) f := by
  rintro ⟨F, hF, hlim⟩
  apply complex_discontinuous_no_continuous_limit a b f hf
  refine ⟨fun n (x : Set.Icc a b) => F n x, ?_, hlim⟩
  intro n
  obtain ⟨U, _, hsub, hsmooth⟩ := hF n
  exact continuousOn_iff_continuous_domRestrict.mp
    (((ckOn_zero_iff (F n) U).mp (hsmooth 0)).mono hsub)

end SingleVariableAnalysis
