import MathGenome.Internal.Specs.D05.M02.Grassmann
import MathGenome.Internal.D05.M02.Dimension
import MathGenome.Internal.D05.M02.SumIntersection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! K05.02.grassmann: the dimension formula for a sum of subspaces. -/

namespace D05.M02.Grassmann

/-- Grassmann's formula requires finite-dimensional summands, with no
finite-dimensionality assumption on the ambient space. -/
theorem grassmann : Specs.D05.M02.Grassmann.grassmann := by
  intro K V _ _ _ U W _ _
  exact Submodule.finrank_sup_add_finrank_inf_eq U W

end D05.M02.Grassmann
