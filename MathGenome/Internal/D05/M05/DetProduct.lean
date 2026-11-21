import MathGenome.Internal.Specs.D05.M05.DetProduct
import MathGenome.Internal.D05.M05.DetDefinition

/-! K05.05.det_product: multiplication and transposition over commutative rings. -/

namespace D05.M05.DetProduct

/-- Transport multiplicativity through the proved bridge from the paper's
column Leibniz determinant to Mathlib's determinant. -/
theorem det_mul : D05.Specs.DetProduct.det_mul := by
  intro R _ n A B
  rw [DetDefinition.matrix_det_bridge, DetDefinition.matrix_det_bridge,
    DetDefinition.matrix_det_bridge]
  exact Matrix.det_mul A B

/-- The same bridge transports the permutation-inversion transpose identity. -/
theorem det_transpose : D05.Specs.DetProduct.det_transpose := by
  intro R _ n A
  rw [DetDefinition.matrix_det_bridge, DetDefinition.matrix_det_bridge]
  exact Matrix.det_transpose A

end D05.M05.DetProduct
