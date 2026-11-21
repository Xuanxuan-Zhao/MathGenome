import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.TaylorPolynomial
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.Lagrange

/-!
# Real Taylor theorem with the Lagrange remainder

K03.06.lagrange, paper.tex:2781–2792. The source's C^n compact-interval
hypothesis is the upstream continuous derivative family (equivalently
ContDiffOn at order n). Only the next interior derivative is required to exist.
Mathlib's `taylor_mean_remainder_lagrange` has precisely that regularity;
we identify its within derivatives with ordinary interior derivatives and
its coefficients with the continuous one-sided values in the upstream family.
In particular arbitrary exterior values never enter the endpoint coefficients.
Unordered intervals cover both endpoint orders, including n=0.
-/
noncomputable section
namespace SingleVariableAnalysis
open Set Filter
open scoped Topology BigOperators

/-- Locality of the iterated derivative, without a smoothness assumption. -/
theorem iteratedDerivWithin_eq_of_mem_nhds (f : ℝ → ℝ) (k : ℕ)
    (s : Set ℝ) (t : ℝ) (hs : s ∈ 𝓝 t) :
    iteratedDerivWithin k f s t = RealIteratedDerivative k f t := by
  change (iteratedFDerivWithin ℝ k f s t fun _ => 1) =
    (iteratedFDeriv ℝ k f t fun _ => 1)
  rw [← iteratedFDerivWithin_univ]
  rw [iteratedFDerivWithin_congr_set (Filter.eventuallyEqSet_univ.mpr hs) k]

/-- On the open segment the within jet is the ordinary real jet. -/
private theorem interior_jet (f : ℝ → ℝ) (k : ℕ) (a x : ℝ) :
    EqOn (iteratedDerivWithin k f (uIcc a x))
      (RealIteratedDerivative k f) (uIoo a x) := by
  intro t ht
  exact iteratedDerivWithin_eq_of_mem_nhds f k _ t (Icc_mem_nhds ht.1 ht.2)

/-- The endpoint Taylor polynomial has the coefficients specified in the
manuscript, including continuous one-sided endpoint values. -/
theorem endpointTaylor_eq_within (f : ℝ → ℝ) (n : ℕ) (a x : ℝ)
    (D : ℕ → ℝ → ℝ) (hax : a ≠ x)
    (hD : ClosedDerivativeFamily n f (min a x) (max a x) D) :
    taylorWithinEval f n (uIcc a x) a x =
      ∑ k ∈ Finset.range (n+1), D k a / (k.factorial : ℝ) * (x-a)^k := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have heq := closedDerivativeFamily_eq_iteratedDerivWithin n f _ _
    ((min_lt_max.mpr hax)) D hD k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    (show a ∈ Icc (min a x) (max a x) from ⟨min_le_left _ _, le_max_left _ _⟩)
  change D k a = iteratedDerivWithin k f (uIcc a x) a at heq
  rw [← heq]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- The Lagrange theorem on a closed segment, with canonical within coefficients. -/
theorem lagrange_remainder_within (f : ℝ → ℝ) (n : ℕ) (a x : ℝ)
    (hax : a ≠ x) (hf : CkOnClosed n f (min a x) (max a x))
    (hd : ∀ t ∈ uIoo a x, DifferentiableAt ℝ (RealIteratedDerivative n f) t) :
    ∃ ξ ∈ uIoo a x, f x - taylorWithinEval f n (uIcc a x) a x =
      RealIteratedDerivative (n+1) f ξ * (x-a)^(n+1) / ((n+1).factorial : ℝ) := by
  have hc : ContDiffOn ℝ n f (uIcc a x) :=
    (ckOnClosed_iff_contDiffOn n f _ _ ((min_lt_max.mpr hax))).mp hf
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc a x)) (uIoo a x) := by
    intro t ht
    exact ((hd t ht).congr_of_eventuallyEq
      ((interior_jet f n a x).eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2))).differentiableWithinAt
  obtain ⟨ξ, hξ, heq⟩ := taylor_mean_remainder_lagrange hax hc hdiff
  exact ⟨ξ, hξ, by simpa only [interior_jet f (n+1) a x hξ] using heq⟩

/-- Source statement: R_n = f - T_n, with the continuous endpoint jet D. -/
theorem lagrange_remainder (f : ℝ → ℝ) (n : ℕ) (a x : ℝ)
    (D : ℕ → ℝ → ℝ) (hax : a ≠ x)
    (hD : ClosedDerivativeFamily n f (min a x) (max a x) D)
    (hd : ∀ t ∈ uIoo a x, DifferentiableAt ℝ (RealIteratedDerivative n f) t) :
    ∃ ξ ∈ uIoo a x,
      f x - (∑ k ∈ Finset.range (n+1), D k a / (k.factorial : ℝ) * (x-a)^k) =
        RealIteratedDerivative (n+1) f ξ * (x-a)^(n+1) / ((n+1).factorial : ℝ) := by
  simpa only [endpointTaylor_eq_within f n a x D hax hD] using
    lagrange_remainder_within f n a x hax ⟨D, hD⟩ hd

/-- The upstream ambient Taylor remainder agrees when its jet has the indicated
endpoint values. The general theorem above does not impose this extra premise. -/
theorem lagrange_remainder_ambient (f : ℝ → ℝ) (n : ℕ) (a x : ℝ)
    (hax : a ≠ x) (hf : CkOnClosed n f (min a x) (max a x))
    (hd : ∀ t ∈ uIoo a x, DifferentiableAt ℝ (RealIteratedDerivative n f) t)
    (hjet : ∀ k ≤ n, iteratedDerivWithin k f (uIcc a x) a = RealIteratedDerivative k f a) :
    ∃ ξ ∈ uIoo a x, TaylorRemainder f n a x =
      RealIteratedDerivative (n+1) f ξ * (x-a)^(n+1) / ((n+1).factorial : ℝ) := by
  have heq : taylorWithinEval f n (uIcc a x) a x = TaylorPolynomialEval f n a x := by
    rw [taylor_within_apply, taylorPolynomialEval_formula]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hjet k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    simp only [smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply, div_eq_mul_inv]
    ring
  simpa only [heq, TaylorRemainder] using lagrange_remainder_within f n a x hax hf hd

/-- Order zero is the mean value theorem, also for x<a. -/
theorem lagrange_remainder_zero (f : ℝ → ℝ) (a x : ℝ) (hax : a ≠ x)
    (hf : ContinuousOn f (uIcc a x))
    (hd : ∀ t ∈ uIoo a x, DifferentiableAt ℝ f t) :
    ∃ ξ ∈ uIoo a x, f x - f a = deriv f ξ * (x-a) := by
  simpa [RealIteratedDerivative] using lagrange_remainder_within f 0 a x hax
    ((ckOnClosed_zero_iff f _ _).mpr hf) (by simpa using hd)

end SingleVariableAnalysis
