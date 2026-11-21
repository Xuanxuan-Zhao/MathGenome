import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05Sublinear

/-!
Real sublinear functions and their two stated consequences,
`paper.tex:855–861`, label `fa2:p1:c05:sublinear`.
-/

universe u

namespace ExpandedFA.P1

/-- A finite real-valued function on a real vector space is sublinear when
it is subadditive and homogeneous for every nonnegative real scalar.
Positivity and symmetry of the function are not required. -/
def IsSublinear {E : Type u} [AddCommGroup E] [Module ℝ E] (p : E → ℝ) : Prop :=
  (∀ x y : E, p (x + y) ≤ p x + p y) ∧
  (∀ (t : ℝ), 0 ≤ t → ∀ x : E, p (t • x) = t * p x)

namespace IsSublinear

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {p : E → ℝ}

/-- Homogeneity at scalar zero forces the value at the zero vector to be zero. -/
theorem map_zero (hp : IsSublinear p) : p 0 = 0 := by
  simpa only [zero_smul, zero_mul] using hp.2 0 le_rfl (0 : E)

/-- Subadditivity on a vector and its negative yields the stated lower bound. -/
theorem neg_le (hp : IsSublinear p) (x : E) : -p (-x) ≤ p x := by
  have h : 0 ≤ p x + p (-x) := by
    simpa only [add_neg_cancel, hp.map_zero] using hp.1 x (-x)
  exact neg_le_iff_add_nonneg.mpr h

end IsSublinear

end ExpandedFA.P1
