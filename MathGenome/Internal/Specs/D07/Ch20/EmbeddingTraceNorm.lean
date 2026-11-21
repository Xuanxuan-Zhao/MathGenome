import MathGenome.Internal.Specs.D07.Ch20.CharacteristicMinpoly
import MathGenome.Internal.Specs.D07.Ch20.SeparableInseparableDegrees
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic

/-! Independent statements of K07.20.embedding_trace_norm (paper.tex:5921–5940).
The maps on the left embed the operator trace and determinant norm from K into
one common algebraically closed K-field. The sum/product range over all distinct
K-algebra embeddings, each once. No separability assumption is made in the two
general formulas, and the multiplicity is the canonical inseparable degree,
namely the dimension of L over its separable part. An algebraic closure is a
particular instance of the allowed algebraically closed target.
-/

universe u v w
namespace Specs.D07.Ch20.EmbeddingTraceNorm

noncomputable section

/-- Weighted sum over distinct embeddings for every finite field extension. -/
def TraceFormula : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [FiniteDimensional K L] [IsAlgClosed Ω] (a : L),
    algebraMap K Ω (Algebra.trace K L a) =
      (Field.finInsepDegree K L : Ω) * ∑ σ : L →ₐ[K] Ω, σ a

/-- Product over distinct embeddings, raised to the inseparable degree. -/
def NormFormula : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [FiniteDimensional K L] [IsAlgClosed Ω] (a : L),
    algebraMap K Ω (Algebra.norm K a) =
      (∏ σ : L →ₐ[K] Ω, σ a) ^ Field.finInsepDegree K L

/-- In the separable case there are exactly [L:K] embeddings, and no weights. -/
def SeparableFormulas : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [FiniteDimensional K L] [IsAlgClosed Ω] [Algebra.IsSeparable K L],
    Fintype.card (L →ₐ[K] Ω) = Module.finrank K L ∧
      ∀ a : L,
        algebraMap K Ω (Algebra.trace K L a) = (∑ σ : L →ₐ[K] Ω, σ a) ∧
        algebraMap K Ω (Algebra.norm K a) = (∏ σ : L →ₐ[K] Ω, σ a)

/-- Inseparable means not separable; the trace is the zero K-linear map. -/
def InseparableTraceZero : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L],
    ¬ Algebra.IsSeparable K L → Algebra.trace K L = 0

end
end Specs.D07.Ch20.EmbeddingTraceNorm
