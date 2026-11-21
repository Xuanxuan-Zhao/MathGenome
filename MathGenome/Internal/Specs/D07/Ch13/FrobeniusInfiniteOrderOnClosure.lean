import MathGenome.Internal.Specs.D07.Ch13.Existence
import Mathlib.GroupTheory.OrderOfElement

/-!
Independent statements for the remark after K07.13.frobenius,
paper.tex:3895–3897. The closure and the embedding of the finite base are
fixed. The witness belongs to the specified embedded root field of size
q^(j+1), rather than an unrelated abstract finite field.
-/

universe u v

namespace Specs.D07.Ch13.FrobeniusInfiniteOrderOnClosure

/-- Every positive iterate moves an element of the next embedded root field.
The automorphism is identified by its actual q-power action. -/
def EmbeddedMovedElement : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Finite K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
    (q : ℕ), Nat.card K = q →
    ∀ Φ : Ω ≃ₐ[K] Ω, (∀ x : Ω, Φ x = x ^ q) →
      ∀ j : ℕ, 0 < j →
        ∃ x : Existence.rootFieldValue K Ω q (j + 1),
          (Φ ^ j) (x : Ω) ≠ (x : Ω)

/-- Relative Frobenius exists on the fixed algebraic closure, has infinite
order (encoded by `orderOf = 0`), and each positive iterate moves an element.
There is no finiteness assumption on the closure. -/
def InfiniteOrderOnClosure : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Finite K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
    (q : ℕ), Nat.card K = q →
      ∃ Φ : Ω ≃ₐ[K] Ω, (∀ x : Ω, Φ x = x ^ q) ∧
        orderOf Φ = 0 ∧ ∀ j : ℕ, 0 < j → ∃ x : Ω, (Φ ^ j) x ≠ x

end Specs.D07.Ch13.FrobeniusInfiniteOrderOnClosure
