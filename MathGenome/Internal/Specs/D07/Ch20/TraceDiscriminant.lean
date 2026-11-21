import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
Independent statements of K07.20.trace_discriminant, paper.tex:5952–5975.
The canonical discriminant uses the multiplication-operator trace. A list
is a basis precisely when it is the underlying family of an actual basis;
its length is explicitly the extension degree. Coordinate matrices act on
columns: a'_j = ∑ i, P_ij • a_i. Embedding matrices have embeddings as rows.
PowerBasis packages a primitive element with its full power basis.
The Moore statement enumerates all embeddings in Frobenius order in the
specified common closure, for any compatible copies of the finite fields.
-/
universe u v w
noncomputable section
namespace Specs.D07.Ch20.TraceDiscriminant

/-- The discriminant is exactly the trace Gram determinant. -/
def TraceGramDefinition : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (n : ℕ) (a : Fin n → L),
    Algebra.discr K a = Matrix.det (Matrix.of (fun i j : Fin n => Algebra.trace K L (a i * a j)))

/-- The length hypothesis is necessary for the converse to independence. -/
def NonzeroIffBasis : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (n : ℕ), n = Module.finrank K L → ∀ a : Fin n → L,
    Algebra.discr K a ≠ 0 ↔ ∃ b : Module.Basis (Fin n) K L, (b : Fin n → L) = a

/-- No invertibility assumption on P or basis assumption on a is needed. -/
def ChangeOfList : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (n : ℕ) (a a' : Fin n → L)
    (P : Matrix (Fin n) (Fin n) K),
    (∀ j, a' j = ∑ i, P i j • a i) →
    Algebra.discr K a' = P.det ^ 2 * Algebra.discr K a

/-- All distinct embeddings occur once. Equality is in the common closure. -/
def EmbeddingDeterminant : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsAlgClosed Ω]
    (n : ℕ) (e : Fin n ≃ (L →ₐ[K] Ω)) (a : Fin n → L),
    algebraMap K Ω (Algebra.discr K a) =
      Matrix.det (Matrix.of (fun i j : Fin n => e i (a j))) ^ 2

/-- Polynomial discriminant is the canonical modified resultant determinant. -/
def PowerBasisDiscriminant : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (b : PowerBasis K L),
    Algebra.discr K b.basis = (minpoly K b.gen).discr

/-- Explicit formulation for each primitive element, without assuming a
power basis as extra data. -/
def PrimitiveElementDiscriminant : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (x : L),
    IntermediateField.adjoin K ({x} : Set L) = ⊤ →
    ∃ b : PowerBasis K L, b.gen = x ∧
      Algebra.discr K b.basis = (minpoly K x).discr

/-- The row index i starts at zero, corresponding to i-1 in the paper. -/
def FiniteFieldMoore : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Finite K] [Finite L]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [IsAlgClosed Ω] (q n : ℕ), Nat.card K = q → Module.finrank K L = n →
    ∀ a : Fin n → L, ∃ e : Fin n ≃ (L →ₐ[K] Ω),
      (∀ i j, e i (a j) = algebraMap L Ω ((a j) ^ (q ^ (i : ℕ)))) ∧
      algebraMap K Ω (Algebra.discr K a) =
        Matrix.det (Matrix.of (fun i j : Fin n => algebraMap L Ω ((a j) ^ (q ^ (i : ℕ))))) ^ 2

/-- The whole Gram matrix, not just its determinant, vanishes. -/
def InseparableGramZero : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L], ¬ Algebra.IsSeparable K L →
    ∀ (n : ℕ) (a : Fin n → L),
      Matrix.of (fun i j : Fin n => Algebra.trace K L (a i * a j)) = 0

end Specs.D07.Ch20.TraceDiscriminant
