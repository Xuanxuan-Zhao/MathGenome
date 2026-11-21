import MathGenome.Internal.Specs.D05.M06.QuotientDimension
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-! K05.06.quotient_dimension: dimension of an algebraic quotient. -/

namespace D05.M06.QuotientDimension

/-- The additive quotient dimension formula, including zero and full subspaces. -/
theorem quotient_dimension : Specs.D05.M06.QuotientDimension.quotient_dimension := by
  intro K V _ _ _ _ U
  exact Submodule.finrank_quotient_add_finrank U

end D05.M06.QuotientDimension
