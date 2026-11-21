import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.TaylorPolynomial
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.Cauchy
import Mathlib.Analysis.Calculus.Taylor

/-!
# The real Cauchy remainder

K03.06.cauchy, paper.tex:2792–2804. We reuse Mathlib's
`taylor_mean_remainder_cauchy`, whose proof differentiates the Taylor sum
with a moving center and applies the real mean value theorem. The bridges
below identify its within derivatives with the upstream continuous closed
family and, on the interior, with the ordinary real iterates. In particular,
no continuity of the (n+1)st derivative and no differentiability across an
endpoint are imposed.

The finite sum in the first theorem is the source's Taylor polynomial with
one-sided endpoint coefficients. The second theorem recovers the existing
`TaylorRemainder` when the ambient iterates supply those coefficients.
-/
noncomputable section
namespace SingleVariableAnalysis
open Set
open scoped Topology

/-- Cauchy's remainder with the continuous, one-sided endpoint coefficients.
The closed family is precisely the upstream C^n data, not extra regularity. -/
theorem cauchy_remainder (f : ℝ → ℝ) (n : ℕ) (a x : ℝ) (D : ℕ → ℝ → ℝ)
    (hax : a ≠ x)
    (hD : ClosedDerivativeFamily n f (min a x) (max a x) D)
    (hd : ∀ t ∈ Ioo (min a x) (max a x),
      DifferentiableAt ℝ (RealIteratedDerivative n f) t) :
    ∃ ξ ∈ Ioo (min a x) (max a x),
      f x - ∑ k ∈ Finset.range (n + 1), (D k a / (k.factorial : ℝ)) * (x-a)^k =
        RealIteratedDerivative (n + 1) f ξ * (x-ξ)^n * (x-a) /
          (n.factorial : ℝ) := by
  have hlt : min a x < max a x := min_lt_max.mpr hax
  have hw (j : ℕ) (hj : j ≤ n) :=
    closedDerivativeFamily_eq_iteratedDerivWithin n f (min a x) (max a x) hlt D hD j hj
  have hi := closedDerivativeFamily_eq_interior n f (min a x) (max a x) D hD n le_rfl
  have heq : EqOn (iteratedDerivWithin n f (Icc (min a x) (max a x)))
      (RealIteratedDerivative n f) (Ioo (min a x) (max a x)) := by
    intro t ht
    exact (hw n le_rfl ⟨ht.1.le, ht.2.le⟩).symm.trans (hi ht)
  have hcont : ContDiffOn ℝ n f (uIcc a x) :=
    (ckOnClosed_iff_contDiffOn n f (min a x) (max a x) hlt).mp ⟨D, hD⟩
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc a x)) (uIoo a x) := by
    intro t ht
    exact ((hd t ht).congr_of_eventuallyEq
      (heq.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht))).differentiableWithinAt
  have htop (t : ℝ) (ht : t ∈ Ioo (min a x) (max a x)) :
      iteratedDerivWithin (n + 1) f (uIcc a x) t = RealIteratedDerivative (n + 1) f t := by
    rw [iteratedDerivWithin_succ, realIteratedDerivative_succ]
    change derivWithin (iteratedDerivWithin n f (Icc (min a x) (max a x)))
      (Icc (min a x) (max a x)) t = _
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact heq.deriv isOpen_Ioo ht
  have hp : taylorWithinEval f n (uIcc a x) a x =
      ∑ k ∈ Finset.range (n + 1), (D k a / (k.factorial : ℝ)) * (x-a)^k := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    change ((k.factorial : ℝ)⁻¹ * (x-a)^k) *
      iteratedDerivWithin k f (Icc (min a x) (max a x)) a = _
    rw [← hw k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      ⟨min_le_left _ _, le_max_left _ _⟩]
    ring
  obtain ⟨ξ, hξ, hrem⟩ := taylor_mean_remainder_cauchy hax hcont hdiff
  refine ⟨ξ, hξ, ?_⟩
  rw [hp, htop ξ hξ] at hrem
  rw [hrem]
  ring

/-- The same formula for the fixed TaylorRemainder when the ambient endpoint
iterates themselves have the stated C^n regularity. -/
theorem cauchy_remainder_taylor (f : ℝ → ℝ) (n : ℕ) (a x : ℝ)
    (hax : a ≠ x) (hf : CkOn n f (Icc (min a x) (max a x)))
    (hd : ∀ t ∈ Ioo (min a x) (max a x),
      DifferentiableAt ℝ (RealIteratedDerivative n f) t) :
    ∃ ξ ∈ Ioo (min a x) (max a x),
      TaylorRemainder f n a x =
        RealIteratedDerivative (n + 1) f ξ * (x-ξ)^n * (x-a) /
          (n.factorial : ℝ) := by
  have hD : ClosedDerivativeFamily n f (min a x) (max a x)
      (fun j => RealIteratedDerivative j f) := by
    refine ⟨?_, hf.2, ?_⟩
    · simp only [realIteratedDerivative_zero]
      exact eqOn_refl _ _
    · intro j hj t ht
      dsimp only
      rw [realIteratedDerivative_succ]
      exact (hf.1 j hj t ht).hasDerivAt.hasDerivWithinAt
  obtain ⟨ξ, hξ, heq⟩ := cauchy_remainder f n a x _ hax hD hd
  refine ⟨ξ, hξ, ?_⟩
  simpa [TaylorRemainder, taylorPolynomialEval_formula]
    using heq

end SingleVariableAnalysis
