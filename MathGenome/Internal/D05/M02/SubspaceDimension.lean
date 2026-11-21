import MathGenome.Internal.Specs.D05.M02.SubspaceDimension
import MathGenome.Internal.D05.M02.Dimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! K05.02.subspace_dimension: finite bases and dimension of subspaces. -/

namespace D05.M02.SubspaceDimension

/-- The ambient finiteness hypothesis supplies finiteness of the subspace.
The upstream basis theorem then supplies its finite basis. The dimension
comparison and its equality case use the canonical inclusion of the subspace. -/
theorem subspace_dimension : Specs.D05.M02.SubspaceDimension.subspace_dimension := by
  intro K V _ _ _ _ U n hn
  refine ⟨inferInstance, D05.M02.Dimension.exists_basis_dimension, ?_, ?_⟩
  · exact hn ▸ U.finrank_le
  · rw [← hn]
    constructor
    · exact Submodule.eq_top_of_finrank_eq
    · intro hU
      subst U
      exact finrank_top K V

end D05.M02.SubspaceDimension
