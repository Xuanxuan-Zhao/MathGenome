import MathGenome.Internal.Specs.D07.Ch20.MultiplicationTraceNorm
import Mathlib.RingTheory.AlgebraTower

/-!
Independent specification of the restriction-of-scalars determinant identity
in the proof of K07.20.trace_norm_towers (paper.tex:5914–5918).

For the specified finite field extension M/K, R(A) is the matrix of the
M-linear map with matrix A, viewed as a K-linear map. Its basis consists
of b j times the ith standard basis vector of M^r, indexed by (i,j).
The block-entry specification identifies R(A) with the paper's blocks.
The norm is the determinant of multiplication, as in the upstream Spec.
No separability or nonsingularity assumption, and no positive-size assumption,
is imposed.
-/

universe u v w

namespace Specs.D07.Ch20.TraceNormTowersRestrictionScalarDeterminant

noncomputable section

/-- The K-matrix in the product basis (b j • e_i) of the map with M-matrix A. -/
def restrictionMatrix {K : Type u} {M : Type v} [Field K] [Field M]
    [Algebra K M] {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K M) {r : ℕ} (A : Matrix (Fin r) (Fin r) M) :
    Matrix (Fin r × ι) (Fin r × ι) K :=
  LinearMap.toMatrix (b.smulTower' (Pi.basisFun M (Fin r)))
    (b.smulTower' (Pi.basisFun M (Fin r)))
    ((Matrix.toLin (Pi.basisFun M (Fin r)) (Pi.basisFun M (Fin r)) A).restrictScalars K)

/-- The (i,j) block is the multiplication matrix of A i j on M over K. -/
def BlockEntries : Prop :=
  ∀ (K : Type u) (M : Type v) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] (r : ℕ) (ι : Type w) [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K M) (A : Matrix (Fin r) (Fin r) M)
    (i j : Fin r) (k l : ι),
    restrictionMatrix b A (i, k) (j, l) = Algebra.leftMulMatrix b (A i j) k l

/-- The full identity for all matrices, including singular matrices and r=0. -/
def RestrictionScalarDeterminant : Prop :=
  ∀ (K : Type u) (M : Type v) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] (r : ℕ) (ι : Type w) [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K M) (A : Matrix (Fin r) (Fin r) M),
    Matrix.det (restrictionMatrix b A) = Algebra.norm K (Matrix.det A)

end

end Specs.D07.Ch20.TraceNormTowersRestrictionScalarDeterminant
