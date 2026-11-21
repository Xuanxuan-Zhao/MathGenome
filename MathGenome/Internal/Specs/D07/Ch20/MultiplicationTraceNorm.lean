import MathGenome.Internal.Specs.D07.Ch12.DegreeDefinition
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Norm.Defs
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
Independent specification of K07.20.multiplication_trace_norm,
paper.tex:5865–5893. The extension is any finite-dimensional extension of
commutative fields with its specified structure map. No separability, perfection,
characteristic, or finiteness of the underlying fields is assumed.

Trace and norm mean operator trace and determinant of left multiplication.
The characteristic polynomial is det(TI - m_a). The matrix formulas quantify
over every finite basis, so also specify basis independence. The natural degree
is finrank; the upstream degree specification identifies this with cardinal
degree for exactly the finite extensions in question.
-/

universe u v w

namespace Specs.D07.Ch20.MultiplicationTraceNorm

noncomputable section

def MultiplicationType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L], L →ₐ[K] Module.End K L

def multiplicationValue : MultiplicationType.{u, v} :=
  fun K L _ _ _ _ => Algebra.lmul K L

def TraceType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L], L →ₗ[K] K

def traceValue : TraceType.{u, v} :=
  fun K L _ _ _ _ => (LinearMap.trace K L).comp (Algebra.lmul K L).toLinearMap

def NormType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L], L →* K

def normValue : NormType.{u, v} :=
  fun K L _ _ _ _ => LinearMap.det.comp (Algebra.lmul K L).toRingHom.toMonoidHom

def CharacteristicPolynomialType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L], L → Polynomial K

def characteristicPolynomialValue : CharacteristicPolynomialType.{u, v} :=
  fun K L _ _ _ _ a => (Algebra.lmul K L a).charpoly

def NormOnUnitsType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L], Lˣ →* Kˣ

def normOnUnitsValue : NormOnUnitsType.{u, v} :=
  fun K L _ _ _ _ => Units.map (Algebra.norm K (S := L))

def MultiplicationApply : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a x : L), Algebra.lmul K L a x = a * x

def TraceApply : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : L),
    Algebra.trace K L a = LinearMap.trace K L (Algebra.lmul K L a)

def NormApply : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : L),
    Algebra.norm K a = LinearMap.det (Algebra.lmul K L a)

/-- Equalities with the same intrinsic objects for every basis establish basis
independence, including independence of the finite indexing type. -/
def MatrixFormulas : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (a : L),
    Algebra.trace K L a = Matrix.trace (Algebra.leftMulMatrix b a) ∧
    Algebra.norm K a = Matrix.det (Algebra.leftMulMatrix b a) ∧
    (Algebra.lmul K L a).charpoly =
      Matrix.det (Matrix.charmatrix (Algebra.leftMulMatrix b a))

def TraceAdd : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a b : L),
    Algebra.trace K L (a + b) = Algebra.trace K L a + Algebra.trace K L b

def TraceSmul : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (c : K) (a : L),
    Algebra.trace K L (c • a) = c * Algebra.trace K L a

def NormOne : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L], Algebra.norm K (1 : L) = 1

def NormMul : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a b : L),
    Algebra.norm K (a * b) = Algebra.norm K a * Algebra.norm K b

def TraceAlgebraMap : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (c : K),
    Algebra.trace K L (algebraMap K L c) = (Module.finrank K L : K) * c

def NormAlgebraMap : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (c : K),
    Algebra.norm K (algebraMap K L c) = c ^ Module.finrank K L

def TraceScalarMul : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (c : K) (a : L),
    Algebra.trace K L (algebraMap K L c * a) = c * Algebra.trace K L a

def NormScalarMul : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (c : K) (a : L),
    Algebra.norm K (algebraMap K L c * a) = c ^ Module.finrank K L * Algebra.norm K a

def NormEqZeroIff : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : L), Algebra.norm K a = 0 ↔ a = 0

def NormOnUnitsApply : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : Lˣ),
    (Units.map (Algebra.norm K (S := L)) a : K) = Algebra.norm K (a : L)

end

end Specs.D07.Ch20.MultiplicationTraceNorm
