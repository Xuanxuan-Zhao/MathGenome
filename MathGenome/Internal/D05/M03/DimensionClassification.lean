import MathGenome.Internal.Specs.D05.M03.DimensionClassification
import MathGenome.Internal.D05.M02.Dimension
import MathGenome.Internal.D05.M03.BasisExtension
import MathGenome.Internal.D05.M03.Isomorphism
import Mathlib.LinearAlgebra.Dimension.Free

/-! K05.03.dimension_classification: classification over a common scalar field.
The library classification constructs an equivalence by matching bases of equal
cardinality. Its converse transports dimension through a linear equivalence.
-/

namespace D05.M03.DimensionClassification

theorem isomorphic_iff_dimension_eq :
    Specs.D05.M03.DimensionClassification.isomorphic_iff_dimension_eq := by
  intro K V W _ _ _ _ _ _ _
  exact FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq

theorem exists_bijective_iff_dimension_eq :
    Specs.D05.M03.DimensionClassification.exists_bijective_iff_dimension_eq := by
  intro K V W _ _ _ _ _ _ _
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨e, _⟩ := (D05.M03.Isomorphism.isomorphism_iff_bijective T).mpr hT
    exact isomorphic_iff_dimension_eq.mp ⟨e⟩
  · intro hdim
    obtain ⟨e⟩ := isomorphic_iff_dimension_eq.mpr hdim
    exact ⟨e.toLinearMap, e.bijective⟩

end D05.M03.DimensionClassification
