import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05Sublinear
import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
Independent specification of real analytic Hahn–Banach,
`paper.tex:862–867`, label `fa2:p1:c05:real-hahn-banach`.

The vector space and subspace are purely algebraic. The bound is finite
real-valued, with no positivity, symmetry, continuity or norm assumptions.
-/

universe u

namespace Specs.ExpandedFA.P1.C05RealHahnBanach

/-- A dominated real linear functional on any subspace has a global real
linear extension dominated by the same sublinear function. -/
def realHahnBanachType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E]
    (M : Submodule ℝ E) (p : E → ℝ),
    Specs.ExpandedFA.P1.C05Sublinear.isSublinearValue p →
    ∀ (f : M →ₗ[ℝ] ℝ), (∀ m : M, f m ≤ p (m : E)) →
    ∃ F : E →ₗ[ℝ] ℝ,
      (∀ m : M, F (m : E) = f m) ∧ (∀ x : E, F x ≤ p x)

end Specs.ExpandedFA.P1.C05RealHahnBanach
