import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.UniformApproximation
import MathGenome.Internal.FourierSobolev.P102.Periodic.FejerRecovery

/-! Lemma 1.9 and Theorem 1.10 of `paper.tex:438–473`.
Bernstein convergence uses Mathlib's locally convex space theorem, specialized to
real and complex scalars. The complex interval theorem combines real polynomial
approximations of the real and imaginary parts. The circle statements reuse the
canonical upstream trigonometric polynomial spaces and their uniform density. -/
noncomputable section
open Filter Set
open scoped Topology unitInterval Polynomial

namespace P102.Approximation

variable {𝕜 : Type} [RCLike 𝕜]

/-- The Bernstein approximant on [0,1]; at n = 0 it is the constant f(0). -/
def bernsteinApproximant (n : ℕ) (f : C(I, 𝕜)) : C(I, 𝕜) :=
  bernsteinApproximation n f

/-- The actual scalar polynomial whose restriction is the Bernstein approximant. -/
def bernsteinPolynomialFor (n : ℕ) (f : C(I, 𝕜)) : 𝕜[X] :=
  ∑ k : Fin (n + 1), Polynomial.C (f (bernstein.z k)) * bernsteinPolynomial 𝕜 n k

/-- The source formula, with k/n represented by `bernstein.z k` in [0,1]. -/
theorem bernstein_formula (n : ℕ) (f : C(I, 𝕜)) (x : I) :
    bernsteinApproximant n f x = ∑ k : Fin (n + 1),
      ((n.choose k : ℝ) * (x : ℝ) ^ (k : ℕ) * (1 - (x : ℝ)) ^ (n - k)) •
        f (bernstein.z k) := by
  simp only [bernsteinApproximant, bernsteinApproximation.apply, bernstein_apply]

theorem bernstein_polynomial_eval (n : ℕ) (f : C(I, 𝕜)) (x : I) :
    (bernsteinPolynomialFor n f).eval (algebraMap ℝ 𝕜 (x : ℝ)) =
      bernsteinApproximant n f x := by
  rw [bernstein_formula]
  simp only [bernsteinPolynomialFor, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, bernsteinPolynomial, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one, Algebra.smul_def,
    map_mul, map_pow, map_sub, map_one, map_natCast]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem bernstein_zero (f : C(I, 𝕜)) :
    bernsteinApproximant 0 f = ContinuousMap.const I (f 0) := by
  ext x
  simp [bernsteinApproximant, bernsteinApproximation.apply, bernstein_apply, bernstein.z]

/-- Uniform convergence for every continuous real or complex function on [0,1]. -/
theorem bernstein_uniform (f : C(I, 𝕜)) :
    TendstoUniformly (fun n x => bernsteinApproximant n f x) f atTop := by
  exact ContinuousMap.tendsto_iff_tendstoUniformly.mp (bernsteinApproximation_uniform f)

/-- Real algebraic uniform approximation, with no restriction on a and b. -/
theorem algebraic_uniform_real (a b : ℝ) (f : C(Icc a b, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ[X], ‖p.toContinuousMapOn (Icc a b) - f‖ < ε :=
  exists_polynomial_near_continuousMap a b f ε hε

/-- Complex algebraic uniform approximation on a real interval. Empty and singleton
intervals are included by the real approximation theorem used for each component. -/
theorem algebraic_uniform_complex (a b : ℝ) (f : C(Icc a b, ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ x : Icc a b, ‖p.eval (x : ℂ) - f x‖ < ε := by
  let fr : C(Icc a b, ℝ) := ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
  let fi : C(Icc a b, ℝ) := ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩
  obtain ⟨p, hp⟩ := algebraic_uniform_real a b fr (ε / 2) (half_pos hε)
  obtain ⟨q, hq⟩ := algebraic_uniform_real a b fi (ε / 2) (half_pos hε)
  refine ⟨p.map (algebraMap ℝ ℂ) + Polynomial.C Complex.I * q.map (algebraMap ℝ ℂ), ?_⟩
  intro x
  have hpr : |p.eval (x : ℝ) - (f x).re| < ε / 2 :=
    lt_of_le_of_lt ((p.toContinuousMapOn (Icc a b) - fr).norm_coe_le_norm x) hp
  have hqi : |q.eval (x : ℝ) - (f x).im| < ε / 2 :=
    lt_of_le_of_lt ((q.toContinuousMapOn (Icc a b) - fi).norm_coe_le_norm x) hq
  have hp_eval : (p.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((p.eval (x : ℝ) : ℝ) : ℂ) :=
    Polynomial.eval_map_apply (p := p) (algebraMap ℝ ℂ) (x : ℝ)
  have hq_eval : (q.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((q.eval (x : ℝ) : ℝ) : ℂ) :=
    Polynomial.eval_map_apply (p := q) (algebraMap ℝ ℂ) (x : ℝ)
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hp_eval, hq_eval]
  apply lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _)
  simpa using (add_lt_add hpr hqi)

/-- The real circle conclusion of Theorem 1.10 for every positive period. -/
theorem trigonometric_uniform_real (T : ℝ) [Fact (0 < T)]
    (f : C(Periodic.Circle T, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p ∈ Periodic.realTrigPolynomials T, ‖p - f‖ < ε :=
  Periodic.trig_uniform_density_real T f ε hε

/-- The complex circle conclusion of Theorem 1.10 for every positive period. -/
theorem trigonometric_uniform_complex (T : ℝ) [Fact (0 < T)]
    (f : C(Periodic.Circle T, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p ∈ Periodic.complexTrigPolynomials T, ‖p - f‖ < ε :=
  Periodic.trig_uniform_density_complex T f ε hε

end P102.Approximation
