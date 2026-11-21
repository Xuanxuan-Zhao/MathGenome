import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FiniteDimensionalSplittings
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08Splitting
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02Projections
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01FiniteDimension
import Mathlib.LinearAlgebra.Isomorphisms

/-!
Finite-dimensional specializations of the one-sided inverse criteria.
The kernel of a surjection onto a finite-dimensional space is closed and has
finite codimension, via the algebraic first isomorphism theorem. The range of
a map from a finite-dimensional space is finite-dimensional, hence closed and
complemented. Applying the accepted criteria gives bounded inverses on the
entire spaces. Both arguments include dimension zero.
-/

namespace ExpandedFA.P1.FiniteDimensionalSplittings

universe u v w

theorem finite_dimensional_right_inverse :
    Spec.FiniteDimensionalRightInverse.{u, v, w} := by
  intro 𝕜 E F _ _ _ _ _ _ _ _ T hT
  let e : (E ⧸ T.ker) ≃ₗ[𝕜] F :=
    T.toLinearMap.quotKerEquivOfSurjective hT
  let : FiniteDimensional 𝕜 (E ⧸ T.ker) := e.symm.finiteDimensional
  have hclosed : IsClosed (T.ker : Set E) := T.isClosed_ker
  have hcomp :=
    (C02Projections.finite_codimensional_complemented 𝕜 E T.ker hclosed).1
  exact (C08Splitting.right_inverse_criterion 𝕜 E F T hT).mpr hcomp

theorem finite_dimensional_left_inverse :
    Spec.FiniteDimensionalLeftInverse.{u, v, w} := by
  intro 𝕜 E F _ _ _ _ _ _ _ _ T hT
  let : FiniteDimensional 𝕜 T.range :=
    LinearMap.finiteDimensional_range T.toLinearMap
  have hclosed : IsClosed (T.range : Set F) :=
    C01FiniteDimension.finite_dimensional_subspace_closed 𝕜 F T.range
  have hcomp := (C02Projections.finite_dimensional_complemented 𝕜 F T.range).1
  exact (C08Splitting.left_inverse_criterion 𝕜 E F T hT).mpr ⟨hclosed, hcomp⟩

end ExpandedFA.P1.FiniteDimensionalSplittings
