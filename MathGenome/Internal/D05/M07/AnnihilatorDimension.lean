import MathGenome.Internal.Specs.D05.M07.AnnihilatorDimension
import MathGenome.Internal.D05.M07.Annihilator
import MathGenome.Internal.D05.M07.DualBasis
import MathGenome.Internal.D05.M02.BasisExtension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! K05.07.annihilator_dimension: dimension and endpoint annihilators. -/

namespace D05.M07.AnnihilatorDimension

/-- Mathlib identifies the annihilator with a space of dimension `dim(V/U)`.
Its dimension identity is `dim U + dim U⁰ = dim V`. Natural-number subtraction
then gives precisely the source formula, including `U = V` and `V = 0`. -/
theorem annihilator_dimension :
    Specs.D05.M07.AnnihilatorDimension.annihilator_dimension := by
  intro K V _ _ _ _ U
  refine ⟨inferInstance, ?_⟩
  exact Nat.eq_sub_of_add_eq
    (by simpa only [add_comm] using Subspace.finrank_add_finrank_dualAnnihilator_eq U)

theorem annihilator_dimension_of_dimensions :
    Specs.D05.M07.AnnihilatorDimension.annihilator_dimension_of_dimensions := by
  intro K V _ _ _ _ U n k hn hk
  simpa only [hn, hk] using (annihilator_dimension U).2

theorem annihilator_top : Specs.D05.M07.AnnihilatorDimension.annihilator_top := by
  intro K V _ _ _
  exact Submodule.dualAnnihilator_top

theorem annihilator_bot : Specs.D05.M07.AnnihilatorDimension.annihilator_bot := by
  intro K V _ _ _
  exact Submodule.dualAnnihilator_bot

end D05.M07.AnnihilatorDimension
