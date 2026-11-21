import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent statement of the algebraic-dual counterexample in paper.tex,
lines 770–780. The sequence uses natural-number indices, with value `n` at
`u n`. A Hamel basis is an algebraic basis: all expansions have finite support.
The basis is indexed by its actual vectors, and its inclusion into `E` is
specified explicitly. No completeness or separability is assumed.
-/

namespace ExpandedFA.P1.DiscontinuousAlgebraicFunctional.Spec

universe u v

/-- Every infinite-dimensional real or complex normed space has independent
unit vectors contained in a Hamel basis, and a scalar-linear functional taking
the value `n` on the nth chosen vector and zero on all other basis vectors.
Its values on the unit sphere are unbounded, so it is discontinuous and does
not arise from a member of the continuous linear dual. -/
def DiscontinuousAlgebraicFunctional : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ¬ FiniteDimensional 𝕜 E →
    ∃ (u : ℕ → E) (B : Set E) (b : Module.Basis B 𝕜 E) (f : E →ₗ[𝕜] 𝕜),
      LinearIndependent 𝕜 u ∧
      (∀ n, ‖u n‖ = 1) ∧
      (∀ x : B, b x = (x : E)) ∧
      Set.range u ⊆ B ∧
      (∀ n, f (u n) = (n : 𝕜)) ∧
      (∀ x ∈ B, x ∉ Set.range u → f x = 0) ∧
      (∀ C : ℝ, ∃ n, C < ‖f (u n)‖) ∧
      ¬ Bornology.IsBounded (f '' Metric.sphere (0 : E) 1) ∧
      ¬ Continuous f ∧
      ¬ ∃ g : E →L[𝕜] 𝕜, g.toLinearMap = f

end ExpandedFA.P1.DiscontinuousAlgebraicFunctional.Spec
