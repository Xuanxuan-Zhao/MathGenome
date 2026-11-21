import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Approximation.IntervalPolynomials
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-! Polynomial approximation on a compact real interval (paper.tex, 6470–6487).
The real result uses Mathlib's Bernstein-based interval theorem. For complex
functions, approximate the two components within ε/2 and combine their polynomials.
Choosing approximants with errors below 1/(n+1) gives the required uniform limits. -/

namespace ExpandedFA.Approximation.IntervalPolynomials

open Filter Polynomial

lemma exists_real_polynomial_near (a b : ℝ) (f : C(Set.Icc a b, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x : Set.Icc a b, ‖p.eval (x : ℝ) - f x‖ < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b f ε hε
  refine ⟨p, fun x => ?_⟩
  exact lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (p.toContinuousMapOn _ - f) x) hp

lemma exists_complex_polynomial_near (a b : ℝ) (f : C(Set.Icc a b, ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ x : Set.Icc a b, ‖p.eval (x : ℂ) - f x‖ < ε := by
  let fr : C(Set.Icc a b, ℝ) := ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
  let fi : C(Set.Icc a b, ℝ) := ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩
  obtain ⟨p, hp⟩ := exists_real_polynomial_near a b fr (ε / 2) (half_pos hε)
  obtain ⟨q, hq⟩ := exists_real_polynomial_near a b fi (ε / 2) (half_pos hε)
  refine ⟨p.map Complex.ofRealHom + C Complex.I * q.map Complex.ofRealHom, fun x => ?_⟩
  have hev (r : Polynomial ℝ) :
      (r.map Complex.ofRealHom).eval (x : ℂ) = ((r.eval (x : ℝ) : ℝ) : ℂ) :=
    Polynomial.eval_map_apply Complex.ofRealHom (x : ℝ)
  simp only [eval_add, eval_mul, eval_C, hev]
  have hr := hp x
  have hi := hq x
  have hn := Complex.norm_le_abs_re_add_abs_im
    (((p.eval (x : ℝ) : ℝ) : ℂ) + Complex.I * ((q.eval (x : ℝ) : ℝ) : ℂ) - f x)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero,
    add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add,
    Real.norm_eq_abs, fr, fi, ContinuousMap.coe_mk] at hn hr hi
  linarith

/-- An error bound tending to zero, independent of the point, implies uniform convergence. -/
private lemma uniformly_of_error_bounds {α E : Type*} [NormedAddCommGroup E]
    (F : ℕ → α → E) (f : α → E)
    (h : ∀ n x, ‖F n x - f x‖ < 1 / ((n : ℝ) + 1)) :
    TendstoUniformly F f atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
  filter_upwards [he] with n hn x
  rw [dist_comm, dist_eq_norm]
  exact (h n x).trans hn

theorem real_uniform_limit :
    Specs.ExpandedFA.Approximation.IntervalPolynomials.RealUniformLimit := by
  intro a b f
  have h (n : ℕ) : ∃ p : Polynomial ℝ, ∀ x : Set.Icc a b,
      ‖p.eval (x : ℝ) - f x‖ < 1 / ((n : ℝ) + 1) :=
    exists_real_polynomial_near a b f _ (by positivity)
  choose p hp using h
  exact ⟨p, uniformly_of_error_bounds _ _ hp⟩

theorem complex_uniform_limit :
    Specs.ExpandedFA.Approximation.IntervalPolynomials.ComplexUniformLimit := by
  intro a b f
  have h (n : ℕ) : ∃ p : Polynomial ℂ, ∀ x : Set.Icc a b,
      ‖p.eval (x : ℂ) - f x‖ < 1 / ((n : ℝ) + 1) :=
    exists_complex_polynomial_near a b f _ (by positivity)
  choose p hp using h
  exact ⟨p, uniformly_of_error_bounds _ _ hp⟩

theorem real_singleton :
    Specs.ExpandedFA.Approximation.IntervalPolynomials.RealSingleton := by
  intro a f x
  have hx : x = ⟨a, le_rfl, le_rfl⟩ := Subtype.ext (le_antisymm x.property.2 x.property.1)
  subst x
  simp

theorem complex_singleton :
    Specs.ExpandedFA.Approximation.IntervalPolynomials.ComplexSingleton := by
  intro a f x
  have hx : x = ⟨a, le_rfl, le_rfl⟩ := Subtype.ext (le_antisymm x.property.2 x.property.1)
  subst x
  simp

end ExpandedFA.Approximation.IntervalPolynomials
