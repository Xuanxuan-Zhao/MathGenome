import MathGenome.Internal.Specs.D05.M03.BasisExtension
import MathGenome.Internal.D05.M02.Basis
import MathGenome.Internal.D05.M03.LinearMap

/-! K05.03.basis_extension: specifying a linear map on an arbitrary basis. -/

namespace D05.M03.BasisExtension

/-- Construct the extension in finite-support coordinates; agreement on the basis
then forces equality on every vector. -/
theorem exists_unique_linear_map :
    Specs.D05.M03.BasisExtension.exists_unique_linear_map := by
  intro K V W I _ _ _ _ _ b w
  refine ⟨b.constr K w, b.constr_basis K w, ?_⟩
  intro T hT
  exact b.ext (fun i => (hT i).trans (b.constr_basis K w i).symm)

/-- Linearity applied to the unique basis expansion gives the explicit formula. -/
theorem linear_map_eq_sum : Specs.D05.M03.BasisExtension.linear_map_eq_sum := by
  intro K V W I _ _ _ _ _ b w T hT x
  calc
    T x = T (∑ i ∈ (b.repr x).support, b.repr x i • b i) :=
      congrArg T (b.linearCombination_repr x).symm
    _ = ∑ i ∈ (b.repr x).support, b.repr x i • T (b i) :=
      D05.M03.LinearMap.map_finite_combination T _ _ _
    _ = ∑ i ∈ (b.repr x).support, b.repr x i • w i := by simp only [hT]

end D05.M03.BasisExtension
