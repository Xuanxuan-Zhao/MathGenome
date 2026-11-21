import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.NormalEquations
import MathGenome.Internal.D05.M14.NormalEquations

/-! P206 W28. The reused normal-equation results are for the same canonical
`LinearMap.adjoint` and the same global residual-norm minimum. General existence
uses the independently constructed pseudoinverse, without any rank hypothesis. -/
noncomputable section

namespace NumAnalysis206.NormalEquations

theorem minimizer_iff_normal_equation :
    Specs.NumAnalysis206.NormalEquations.minimizer_iff_normal_equation := by
  exact D05.M14.NormalEquations.minimizer_iff_normal_equation

theorem exists_minimizer :
    Specs.NumAnalysis206.NormalEquations.exists_minimizer := by
  intro K E F _ _ _ _ _ _ _ A b
  exact ⟨D05.pseudoinverse A b, D05.M14.LeastSquares.pseudoinverse_minimizes A b⟩

theorem gram_isUnit_of_injective :
    Specs.NumAnalysis206.NormalEquations.gram_isUnit_of_injective := by
  intro K E F _ _ _ _ _ _ _ A hA
  exact (D05.M14.NormalEquations.gram_isUnit_iff_injective A).mpr hA

theorem gram_inverse_identities :
    Specs.NumAnalysis206.NormalEquations.gram_inverse_identities := by
  exact D05.M14.NormalEquations.gram_inverse_identities

theorem minimizer_iff_inverse_formula :
    Specs.NumAnalysis206.NormalEquations.minimizer_iff_inverse_formula := by
  exact D05.M14.NormalEquations.minimizer_iff_inverse_formula

theorem exists_unique_injective_minimizer :
    Specs.NumAnalysis206.NormalEquations.exists_unique_injective_minimizer := by
  exact D05.M14.NormalEquations.exists_unique_injective_minimizer

end NumAnalysis206.NormalEquations
