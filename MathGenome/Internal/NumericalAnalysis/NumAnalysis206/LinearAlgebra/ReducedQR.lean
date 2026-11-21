import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.ReducedQR
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.D05.M14.QrCholesky.Qr

namespace NumAnalysis206.ReducedQR

/-- W27, including matrices with no columns. The canonical full-rank condition
is independence of the actual columns; the reused theorem has no dimension or
nonemptiness assumptions. Its four factorization conditions unfold to the
explicit conditions in the independent statement. -/
theorem exists_unique_reduced_qr :
    Specs.NumAnalysis206.ReducedQR.exists_unique_reduced_qr := by
  intro K _ m n A hA
  change ∃! p : Matrix (Fin m) (Fin n) K × Matrix (Fin n) (Fin n) K,
    D05.QrCholesky.ReducedQR A p.1 p.2
  exact D05.M14.QrCholesky.Qr.exists_unique_reduced_qr A hA

end NumAnalysis206.ReducedQR
