import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Fermat
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
Fermat's necessary condition and its two counterexamples (K03.05.fermat).
Mathlib's real Fermat theorem proves the derivative-value statement; the
upstream interior bridge handles derivatives relative to a domain. In the
absolute-value example, nonexistence is stated using differentiability and
the explicit increment limit, rather than the total function `deriv`.
-/

namespace SingleVariableAnalysis

open Set

theorem fermat_hasDerivAt (f : ℝ → ℝ) (a L : ℝ)
    (he : IsLocalExtr f a) (hd : HasDerivAt f L a) : L = 0 :=
  he.hasDerivAt_eq_zero hd

theorem fermat_within (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ)
    (ha : a ∈ interior I) (he : IsLocalExtrOn f I a)
    (hd : HasRealIncrementDerivativeWithin f L I a) : L = 0 := by
  exact fermat_hasDerivAt f a L
    (he.isLocalExtr (mem_interior_iff_mem_nhds.mp ha))
    ((withinDerivative_interior_iff f L I a ha).mp hd)

theorem fermat_deriv (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ)
    (ha : a ∈ interior I) (he : IsLocalExtrOn f I a)
    (hd : DifferentiableAt ℝ f a) : deriv f a = 0 := by
  exact fermat_hasDerivAt f a (deriv f a)
    (he.isLocalExtr (mem_interior_iff_mem_nhds.mp ha)) hd.hasDerivAt

theorem endpoint_minimum_example :
    (0 : ℝ) ∈ Icc 0 1 ∧
      (0 : ℝ) ∉ interior (Icc (0 : ℝ) 1) ∧
      IsMinOn (fun x : ℝ => x) (Icc 0 1) 0 ∧
      IsLocalMinOn (fun x : ℝ => x) (Icc 0 1) 0 ∧
      HasDerivWithinAt (fun x : ℝ => x) 1 (Ici 0) 0 ∧
      HasRealIncrementDerivativeWithin (fun x : ℝ => x) 1 (Icc 0 1) 0 ∧
      (1 : ℝ) ≠ 0 := by
  have hm : IsMinOn (fun x : ℝ => x) (Icc 0 1) 0 := fun x hx => hx.1
  have hd : HasRealIncrementDerivativeWithin (fun x : ℝ => x) 1 (Icc 0 1) 0 := by
    intro ε hε
    refine ⟨1, zero_lt_one, fun h _ hh _ => ?_⟩
    have hn : h ≠ 0 := by simpa only [Real.dist_eq, sub_zero, abs_pos] using hh
    simpa [RealIncrementQuotient, smul_eq_mul, inv_mul_cancel₀ hn] using hε
  exact ⟨by norm_num, by simp [interior_Icc], hm, hm.isLocalMinOn,
    (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt, hd, one_ne_zero⟩

theorem abs_minimum_example :
    (0 : ℝ) ∈ interior (univ : Set ℝ) ∧
      IsMinOn (abs : ℝ → ℝ) univ 0 ∧
      IsLocalMin (abs : ℝ → ℝ) 0 ∧
      ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 ∧
      ¬ ∃ L : ℝ, HasRealIncrementDerivative (abs : ℝ → ℝ) L 0 := by
  have hm : IsMinOn (abs : ℝ → ℝ) univ 0 := by
    intro x _
    change |(0 : ℝ)| ≤ |x|
    simpa only [abs_zero] using abs_nonneg x
  refine ⟨by simp, hm, hm.isLocalMin (by simp), not_differentiableAt_abs_zero, ?_⟩
  rintro ⟨L, hd⟩
  exact not_differentiableAt_abs_zero
    ((hasRealIncrementDerivative_iff_hasDerivAt _ L 0).mp hd).differentiableAt

end SingleVariableAnalysis
