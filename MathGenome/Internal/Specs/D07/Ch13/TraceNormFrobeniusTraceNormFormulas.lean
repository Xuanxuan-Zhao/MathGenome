import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Norm.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent statements for the formula part of K07.13.trace_norm
(paper.tex:4065–4080). The base embedding is the given `Algebra K L`.
`Algebra.trace` and `Algebra.norm` are the trace and determinant of
left multiplication, rather than definitions by a sum/product of conjugates.

We assume only a finite base field and finite extension degree. In particular,
normality, separability and an enumeration of embeddings are not hypotheses.
The cardinality q can be any prime power, and is not restricted to a prime.
The statements apply to every specified extension, hence also to the canonical
embedded root field in a fixed algebraic closure with its inherited embedding.
All elements, including zero, occur in the product formula. Surjectivity and
linearity are the separately allocated goal K07.13.trace_norm.
-/

universe u v

namespace Specs.D07.Ch13.TraceNormFrobeniusTraceNormFormulas

/-- The multiplication matrix has the actual multiplication coordinates, acts
on coordinate columns by multiplication, and computes both canonical maps. -/
def MultiplicationMatrixConnection : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (b : Module.Basis (Fin n) K L) (x : L),
    (∀ i j, Algebra.leftMulMatrix b x i j = b.repr (x * b j) i) ∧
    (∀ y : L, (Algebra.leftMulMatrix b x).mulVec (b.repr y) = b.repr (x * y)) ∧
    Algebra.trace K L x = Matrix.trace (Algebra.leftMulMatrix b x) ∧
    Algebra.norm K x = Matrix.det (Algebra.leftMulMatrix b x)

/-- Trace as a sum of the relative (q-power) Frobenius iterates. -/
def FrobeniusTraceFormula : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [FiniteDimensional K L] (q n : ℕ),
    Nat.card K = q → Module.finrank K L = n → ∀ x : L,
      algebraMap K L (Algebra.trace K L x) =
        ∑ j ∈ Finset.range n, x ^ (q ^ j)

/-- Norm as a product of the same iterates, with no nonzero premise. -/
def FrobeniusNormProductFormula : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [FiniteDimensional K L] (q n : ℕ),
    Nat.card K = q → Module.finrank K L = n → ∀ x : L,
      algebraMap K L (Algebra.norm K x) =
        ∏ j ∈ Finset.range n, x ^ (q ^ j)

/-- The geometric-sum exponent in the norm formula for a nonzero element. -/
def FrobeniusNormPowerFormula : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [FiniteDimensional K L] (q n : ℕ),
    Nat.card K = q → Module.finrank K L = n → ∀ x : L, x ≠ 0 →
      algebraMap K L (Algebra.norm K x) = x ^ ((q ^ n - 1) / (q - 1))

end Specs.D07.Ch13.TraceNormFrobeniusTraceNormFormulas
