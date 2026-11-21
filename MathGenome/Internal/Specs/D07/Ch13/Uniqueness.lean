import MathGenome.Internal.Specs.D07.Ch13.Existence

/-!
Independent statements for K07.13.uniqueness (paper.tex:3907–3913).
Field extensions carry their specified structure maps. `AlgEquiv` therefore
requires preservation of the chosen base, rather than just an abstract field
isomorphism. Finiteness is explicit wherever natural cardinality or finrank
is used. Embedded fields containing K are represented by `IntermediateField`
in one fixed algebraic closure; their uniqueness is literal equality with
the previously specified root field. No uniqueness of the isomorphism is claimed.
-/

universe u v w

namespace Specs.D07.Ch13.Uniqueness

/-- All abstract fields of the stated prime-power order are isomorphic. -/
def PrimePowerUniqueness : Prop :=
  ∀ (p n : ℕ), p.Prime → 1 ≤ n →
    ∀ (E : Type u) (L : Type v) [Field E] [Field L] [Finite E] [Finite L],
      Nat.card E = p ^ n → Nat.card L = p ^ n → Nonempty (E ≃+* L)

/-- Equal finite degrees over the same finite base give an isomorphism
commuting with both prescribed base embeddings. -/
def BaseUniqueness : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    [Finite K] [FiniteDimensional K E] [FiniteDimensional K L]
    (n : ℕ), Module.finrank K E = n → Module.finrank K L = n →
      Nonempty (E ≃ₐ[K] L)

/-- The canonical field actually has q^n elements, and every embedded
field containing K with that size is equal to it. Together these express
existence and uniqueness inside the fixed closure, including n = 1. -/
def EmbeddedUniqueness : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Finite K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
    (q n : ℕ), Nat.card K = q → 1 ≤ n →
      let F := Existence.rootFieldValue K Ω q n
      Finite F ∧ Nat.card F = q ^ n ∧
        ∀ E : IntermediateField K Ω,
          Finite E → Nat.card E = q ^ n → E = F

end Specs.D07.Ch13.Uniqueness
