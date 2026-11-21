import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.DotProduct
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.MatrixProduct

/-! The matrix assertion of paper.tex W08. Each output entry is computed by
one of W07's two sequential dot-product algorithms, with its own safe-primitive
checks. All inequalities below are entrywise real inequalities. -/
noncomputable section

namespace NumAnalysis206.Rounding

/-- The matrix whose entries are computed sequential row-column dot products. -/
def matrixProductTrace : MatrixSpecs.ProductType := MatrixSpecs.productValue

/-- Safety of all primitives used to compute the matrix entries. -/
def matrixProductSafe : MatrixSpecs.SafeType := MatrixSpecs.safeValue

/-- The entrywise matrix product error bound, with the sharp inner-dimension
budget k. The theorem includes zero inner dimension and empty output dimensions. -/
theorem matrix_product_error : MatrixSpecs.matrixProductError := by
  intro m k n fused round A B u D hm hku hs i j
  have h := (finite_sequential_dot_product fused round k (A i) (fun l => B l j)
    u D hm hku (hs i j)).2
  simpa only [MatrixSpecs.productValue, Matrix.of_apply, Matrix.mul_apply,
    abs_mul] using h

/-- With no inner coordinates, every computed entry is zero. -/
theorem matrix_product_zero_inner_dimension : MatrixSpecs.zeroInnerDimension := by
  intro m n fused round A B
  funext i j
  rfl

end NumAnalysis206.Rounding
