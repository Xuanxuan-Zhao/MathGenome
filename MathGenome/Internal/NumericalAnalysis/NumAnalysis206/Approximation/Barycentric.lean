import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.Lagrange
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.Barycentric

/-! Exact barycentric interpolation identities (paper.tex W49).
We retain the accepted Lagrange interpolant and identify the source's
products with Mathlib's nodal polynomial and nodal weights. -/

noncomputable section
open Polynomial

universe u v
namespace NumAnalysis206.Approximation

variable {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]

/-- The monic product ω(X) = ∏ i ∈ s, (X - xᵢ). -/
def nodalPolynomial (s : Finset ι) (x : ι → K) : K[X] :=
  Specs.NumAnalysis206.Approximation.nodalPolynomialValue s x

/-- The weight wᵢ = (∏ j ∈ s.erase i, (xᵢ - xⱼ))⁻¹. -/
def barycentricWeight (s : Finset ι) (x : ι → K) (i : ι) : K :=
  Specs.NumAnalysis206.Approximation.barycentricWeightValue s x i

private theorem nodalPolynomial_eq (s : Finset ι) (x : ι → K) :
    nodalPolynomial s x = Lagrange.nodal s x := rfl

private theorem barycentricWeight_eq (s : Finset ι) (x : ι → K) (i : ι) :
    barycentricWeight s x i = Lagrange.nodalWeight s x i := by
  simp only [barycentricWeight,
    Specs.NumAnalysis206.Approximation.barycentricWeightValue,
    Lagrange.nodalWeight, Finset.prod_inv_distrib]

theorem nodalPolynomial_monic (s : Finset ι) (x : ι → K) :
    (nodalPolynomial s x).Monic := by
  rw [nodalPolynomial_eq]
  exact Lagrange.nodal_monic

/-- First barycentric form; it even holds for empty data. -/
theorem barycentric_first (s : Finset ι) (x y : ι → K) (z : K)
    (hz : ∀ i ∈ s, z ≠ x i) :
    (interpolant s x y).eval z = (nodalPolynomial s x).eval z *
      ∑ i ∈ s, barycentricWeight s x i * y i / (z - x i) := by
  change (Lagrange.interpolate s x y).eval z = _
  simpa only [nodalPolynomial_eq, barycentricWeight_eq, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using
    (Lagrange.eval_interpolate_not_at_node y hz)

/-- With at least one distinct node, the quotient has a nonzero denominator. -/
theorem barycentric_denominator_nonzero (s : Finset ι) (x : ι → K) (z : K)
    (hx : Set.InjOn x s) (hs : s.Nonempty) (hz : ∀ i ∈ s, z ≠ x i) :
    (∑ i ∈ s, barycentricWeight s x i / (z - x i)) ≠ 0 := by
  simpa only [barycentricWeight_eq, div_eq_mul_inv] using
    (Lagrange.sum_nodalWeight_mul_inv_sub_ne_zero hx hz hs)

/-- Second barycentric form for the source's n + 1 distinct nodes. -/
theorem barycentric_second (s : Finset ι) (x y : ι → K) (z : K)
    (hx : Set.InjOn x s) (hs : s.Nonempty) (hz : ∀ i ∈ s, z ≠ x i) :
    (interpolant s x y).eval z =
      (∑ i ∈ s, barycentricWeight s x i * y i / (z - x i)) /
        (∑ i ∈ s, barycentricWeight s x i / (z - x i)) := by
  change (Lagrange.interpolate s x y).eval z = _
  simpa only [barycentricWeight_eq, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using
    (Lagrange.eval_interpolate_not_at_node' y hx hs hz)

/-- At a node one evaluates the interpolant directly to obtain the given datum. -/
theorem barycentric_at_node (s : Finset ι) (x y : ι → K) (hx : Set.InjOn x s)
    (i : ι) (hi : i ∈ s) : (interpolant s x y).eval (x i) = y i :=
  interpolant_eval s x y hx i hi

end NumAnalysis206.Approximation
