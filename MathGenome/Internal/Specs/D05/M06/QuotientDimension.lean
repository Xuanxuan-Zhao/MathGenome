import MathGenome.Internal.Specs.D05.M03.RankNullity
import MathGenome.Internal.Specs.D05.M06.QuotientMap

/-!
Independent statement for K05.06.quotient_dimension (paper.tex:956–963).

The quotient is the canonical algebraic quotient `V ⧸ U` and dimension is
`Module.finrank`, as in the prerequisite interfaces. Only the ambient space
is assumed finite-dimensional. No complement, basis, or nonzero-dimension
condition is imposed, so the statement includes `U = ⊥`, `U = ⊤`, and `V = 0`.
-/

namespace Specs.D05.M06.QuotientDimension

/-- The quotient dimension plus the subspace dimension is the ambient dimension. -/
def quotient_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Submodule K V),
    Module.finrank K (V ⧸ U) + Module.finrank K U = Module.finrank K V

end Specs.D05.M06.QuotientDimension
