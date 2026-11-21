import Mathlib.Algebra.Module.Basic
import Mathlib.Basic.Real.Basic

/-!
Independent specification of the real sublinear function definition,
`paper.tex:855–861`, label `fa2:p1:c05:sublinear`.

The domain is any real vector space, including the zero space. The codomain
is ℝ, so values are finite. No positivity, symmetry, or topology is assumed.
-/

universe u

namespace Specs.ExpandedFA.P1.C05Sublinear

/-- Type of the real sublinearity predicate, with all vector-space parameters. -/
def isSublinearType :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], (E → ℝ) → Prop

/-- The two conditions defining sublinearity, including homogeneity at zero. -/
def isSublinearValue : isSublinearType.{u} :=
  fun {E} _ _ p =>
    (∀ x y : E, p (x + y) ≤ p x + p y) ∧
    (∀ (t : ℝ), 0 ≤ t → ∀ x : E, p (t • x) = t * p x)

/-- The first stated consequence: every sublinear function vanishes at zero. -/
def mapZeroType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] {p : E → ℝ},
    isSublinearValue p → p 0 = 0

/-- The second stated consequence: the lower bound from opposite vectors. -/
def negLeType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] {p : E → ℝ},
    isSublinearValue p → ∀ x : E, -p (-x) ≤ p x

end Specs.ExpandedFA.P1.C05Sublinear
