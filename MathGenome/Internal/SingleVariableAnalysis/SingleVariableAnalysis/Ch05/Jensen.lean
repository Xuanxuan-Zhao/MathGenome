import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Convexity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Jensen
import Mathlib.Analysis.Convex.Jensen

/-!
# Finite Jensen inequality and its strict equality case

K03.05.jensen, paper.tex:952–964. We use the accepted equivalences between
the manuscript's one-parameter convexity predicates and Mathlib's predicates.
`Convex.sum_mem` supplies membership of the weighted point. The inequality
and strict equality case reuse Mathlib's finite Jensen results; the latter
discards zero weights, as does the manuscript's proof. Neither the finite
index set nor the interval is assumed nonempty: normalization already excludes
the impossible empty-family case.
-/

namespace SingleVariableAnalysis

open scoped BigOperators

/-- Finite Jensen, together with membership of the weighted point in the interval. -/
theorem finite_jensen {ι : Type*} (I : Set ℝ) (hI : I.OrdConnected)
    (f : ℝ → ℝ) (hf : ConvexFunctionOn I f) (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hs : (∑ j ∈ s, w j) = 1)
    (hx : ∀ j ∈ s, x j ∈ I) :
    (∑ j ∈ s, w j * x j) ∈ I ∧
      f (∑ j ∈ s, w j * x j) ≤ ∑ j ∈ s, w j * f (x j) := by
  have hconv : ConvexOn ℝ I f := (convexFunctionOn_iff_convexOn I hI f).mp hf
  constructor
  · simpa only [smul_eq_mul] using hconv.1.sum_mem hw hs hx
  · simpa only [smul_eq_mul] using hconv.map_sum_le hw hs hx

/-- In strict Jensen, exactly the positive-weight inputs must agree for equality. -/
theorem strict_finite_jensen_eq_iff {ι : Type*} (I : Set ℝ) (hI : I.OrdConnected)
    (f : ℝ → ℝ) (hf : StrictConvexFunctionOn I f) (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hs : (∑ j ∈ s, w j) = 1)
    (hx : ∀ j ∈ s, x j ∈ I) :
    f (∑ j ∈ s, w j * x j) = ∑ j ∈ s, w j * f (x j) ↔
      ∀ j ∈ s, 0 < w j → ∀ k ∈ s, 0 < w k → x j = x k := by
  have hconv : StrictConvexOn ℝ I f :=
    (strictConvexFunctionOn_iff_strictConvexOn I hI f).mp hf
  have heq := hconv.map_sum_eq_iff_of_nonneg hw hs hx
  simp only [smul_eq_mul] at heq
  constructor
  · intro h j hj hjpos k hk hkpos
    exact heq.mp h hj (ne_of_gt hjpos) hk (ne_of_gt hkpos)
  · intro h
    apply heq.mpr
    intro j hj hjne k hk hkne
    exact h j hj (lt_of_le_of_ne (hw j hj) (Ne.symm hjne))
      k hk (lt_of_le_of_ne (hw k hk) (Ne.symm hkne))

end SingleVariableAnalysis
