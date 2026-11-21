import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.OrderNormMonotonicity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.PositiveConeSquareRoots
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

noncomputable section
namespace ExpandedFA.CStar.OrderNormMonotonicity
universe u

theorem selfAdjoint_square_characterization : Spec.SelfAdjointSquareCharacterization.{u} :=
  PositiveConeSquareRoots.selfAdjoint_square_characterization

theorem star_square_characterization : Spec.StarSquareCharacterization.{u} :=
  PositiveConeSquareRoots.star_square_characterization

theorem closed_proper_convex_cone : Spec.ClosedProperConvexCone.{u} :=
  PositiveConeSquareRoots.closed_proper_convex_cone

theorem unique_positive_square_root : Spec.UniquePositiveSquareRoot.{u} :=
  PositiveConeSquareRoots.unique_positive_square_root

theorem operator_quadratic_characterization : Spec.OperatorQuadraticCharacterization.{u} :=
  PositiveConeSquareRoots.operator_quadratic_characterization

/-- Use the spectral order only inside the proof. The library estimate is
proved by continuous functional calculus in the isometric unitization:
`0 ≤ a ≤ b ≤ ‖b‖ • 1` implies `‖a‖ ≤ ‖b‖` by the spectral norm criterion.
It uses no GNS representation, ideal, or quotient theorem. -/
theorem order_norm_monotonicity : Spec.OrderNormMonotonicity.{u} := by
  intro A _ a b ha hab
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  have ha0 : 0 ≤ a := (PositiveConeSquareRoots.positive_iff_nonneg a).mp ha
  have hab0 : 0 ≤ b - a :=
    (PositiveConeSquareRoots.positive_iff_nonneg (b - a)).mp hab
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_nonneg.mp hab0) ha0

end ExpandedFA.CStar.OrderNormMonotonicity
