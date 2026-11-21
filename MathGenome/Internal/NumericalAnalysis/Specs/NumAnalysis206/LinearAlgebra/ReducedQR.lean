import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

/-! Independent statement of paper.tex, W27. Natural-number dimensions include
zero; no dimension inequality is assumed. -/
namespace Specs.NumAnalysis206.ReducedQR

open _root_.NumAnalysis206.MatrixDefinitions

/-- Unique reduced QR with a strictly positive real diagonal, over either
real or complex scalars. Uniqueness quantifies over the entire pair. -/
def exists_unique_reduced_qr : Prop :=
  ∀ {K : Type*} [RCLike K] {m n : ℕ} (A : Mat K m n),
    FullColumnRank A →
      ∃! p : Mat K m n × Mat K n n,
        A = p.1 * p.2 ∧ adjoint p.1 * p.1 = 1 ∧
          IsUpperTriangular p.2 ∧ PositiveRealDiagonal p.2

end Specs.NumAnalysis206.ReducedQR
