import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Approximation.ConjugationBoundary
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The polynomial algebra on the circle is unital and separates points, but
conjugation is outside its uniform closure. Normalized circle averages annihilate
`z * p(z)` and take the value one on `z * conj z`. The mean-value property and
the integral norm inequality give the quantitative obstruction.
-/

namespace ExpandedFA.Approximation.ConjugationBoundary

open Specs.ExpandedFA.Approximation.ConjugationBoundary
open scoped ComplexConjugate

theorem contains_constants : ContainsConstants := by
  intro c
  exact polynomialAlgebra.algebraMap_mem c

theorem separates_points : SeparatesPoints :=
  polynomialFunctions_separatesPoints _

theorem polynomial_mean_zero : PolynomialMeanZero := by
  intro p
  have hd : Differentiable ℂ (fun z => z * p.eval z) :=
    differentiable_id.mul p.differentiable
  simpa using hd.diffContOnCl.circleAverage (c := 0) (R := 1)

private lemma mul_conjugate_on_circle (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    z * star z = 1 := by
  have hn : ‖z‖ = 1 := by simpa using hz
  simpa [hn] using Complex.mul_conj' z

theorem conjugation_mean_one : ConjugationMeanOne := by
  apply Real.circleAverage_const_on_circle
  intro z hz
  exact mul_conjugate_on_circle z (by simpa using hz)

theorem uniform_error_lower_bound : UniformErrorLowerBound := by
  intro p
  let f : ℂ → ℂ := fun z => z * p.eval z - 1
  have hd : Differentiable ℂ f :=
    (differentiable_id.mul p.differentiable).sub_const 1
  have hav : Real.circleAverage f 0 1 = -1 := by
    simpa [f] using hd.diffContOnCl.circleAverage (c := 0) (R := 1)
  have hb : Real.circleAverage (fun z => ‖f z‖) 0 1 ≤
      ‖p.toContinuousMapOn (Metric.sphere (0 : ℂ) 1) - conjugation‖ := by
    apply Real.circleAverage_mono_on_of_le_circle
      (hd.continuous.norm.continuousOn.circleIntegrable (by norm_num))
    intro z hz
    have hz' : z ∈ Metric.sphere (0 : ℂ) 1 := by simpa using hz
    have hn : ‖z‖ = 1 := by simpa using hz'
    have heq : f z = z * (p.eval z - star z) := by
      calc
        f z = z * p.eval z - z * star z :=
          congrArg (fun w => z * p.eval z - w) (mul_conjugate_on_circle z hz').symm
        _ = z * (p.eval z - star z) := (mul_sub _ _ _).symm
    rw [heq, norm_mul, hn, one_mul]
    exact ContinuousMap.norm_coe_le_norm
      (p.toContinuousMapOn (Metric.sphere (0 : ℂ) 1) - conjugation) ⟨z, hz'⟩
  have h := Real.norm_circleAverage_le_circleAverage_norm (f := f) (c := 0) (R := 1)
  rw [hav] at h
  simpa using h.trans hb

theorem non_approximation : NonApproximation := by
  intro h
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp h 1 (by norm_num)
  obtain ⟨p, _, hp⟩ := hg
  have hbound := uniform_error_lower_bound p
  rw [← hp] at hdist
  rw [dist_comm, dist_eq_norm] at hdist
  exact (not_lt_of_ge hbound) hdist

theorem not_dense : NotDense := by
  intro h
  exact non_approximation (h conjugation)

theorem not_conjugation_closed : NotConjugationClosed := by
  intro h
  have hx : Polynomial.X.toContinuousMapOn (Metric.sphere (0 : ℂ) 1) ∈
      polynomialAlgebra := by
    exact ⟨Polynomial.X, trivial, rfl⟩
  have hc := h _ hx
  have heq : star (Polynomial.X.toContinuousMapOn (Metric.sphere (0 : ℂ) 1)) =
      conjugation := by
    ext z
    simp [conjugation]
  rw [heq] at hc
  exact non_approximation (subset_closure hc)

end ExpandedFA.Approximation.ConjugationBoundary
