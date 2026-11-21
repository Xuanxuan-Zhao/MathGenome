import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.AbsolutePolynomial
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
Polynomial approximation of absolute value (paper.tex, d10:16:absolute-polynomial).

The interval approximation theorem used here is proved in Mathlib by Bernstein
polynomials, not by Stone–Weierstrass: see
`Mathlib.Analysis.SpecialFunctions.Bernstein.bernsteinApproximation_uniform`
and `Mathlib.Topology.ContinuousMap.Weierstrass`. Thus this scalar ingredient
is independent of the general Stone–Weierstrass conclusion. Choose a polynomial
with uniform error less than 1/(n+1) for each n, then let that tolerance tend to 0.
-/

open Filter Set
open scoped Topology

namespace D10Topology.Ch16

theorem absolute_polynomial : Specs.D10Topology.Ch16.AbsolutePolynomial.absolute_polynomial := by
  have happrox (n : ℕ) : ∃ p : Polynomial ℝ,
      ∀ t ∈ Icc (-1 : ℝ) 1, abs (p.eval t - |t|) < 1 / ((n : ℝ) + 1) := by
    exact exists_polynomial_near_of_continuousOn (-1) 1 (fun t : ℝ => |t|)
      continuous_abs.continuousOn _ (by positivity)
  choose p hp using happrox
  refine ⟨p, Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  filter_upwards [hlim.eventually_lt_const hε] with n hn t ht
  simpa only [Real.dist_eq, abs_sub_comm] using (hp n t ht).trans hn

theorem absolute_polynomial_epsilon :
    Specs.D10Topology.Ch16.AbsolutePolynomial.absolute_polynomial_epsilon := by
  obtain ⟨p, hp⟩ := absolute_polynomial
  refine ⟨p, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hp) ε hε)
  exact ⟨N, fun n hn t ht => by
    simpa only [Real.dist_eq, abs_sub_comm] using hN n hn t ht⟩

end D10Topology.Ch16
