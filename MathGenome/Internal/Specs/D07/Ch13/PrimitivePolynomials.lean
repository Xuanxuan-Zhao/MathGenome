import MathGenome.Internal.Specs.D07.Ch13.PrimitiveDistinction
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
Independent statements for K07.13.primitive_polynomials, paper.tex:4043–4056.

`L` is a field with a specified embedding of the finite base `K`. In the
source's fixed closure it can be the subtype of the specified intermediate
field of cardinality `q^n`. The root-choice statement explicitly retains this
cardinality condition. Other presentations are compared by `K`-algebra
equivalences, as required by the source's convention.

The predicate below is multiplicative primitivity over a finite field, and
does not use the unrelated Gauss-content predicate `Polynomial.IsPrimitive`.
The value is defined for arbitrary extensions as well; the finite-field
statements supply the source's finiteness and cardinality hypotheses.
-/

universe u v w
namespace Specs.D07.Ch13.PrimitivePolynomials

open Polynomial

def PrimitivePredicateType : Type (max (u + 1) (v + 1)) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], ℕ → K[X] → Prop

/-- Monic positive-degree irreducible, with a root generating the unit group. -/
def primitivePredicateValue : PrimitivePredicateType.{u,v} :=
  fun _K L _ _ _ n f =>
    0 < n ∧ f.Monic ∧ f.natDegree = n ∧ Irreducible f ∧
      ∃ a : Lˣ, aeval (a : L) f = 0 ∧ Subgroup.zpowers a = ⊤

/-- The stronger intermediate assertion in the source proof: any two roots
of an irreducible polynomial over a finite field have the same order.
`orderOf` on the ambient multiplicative monoid also handles the root zero. -/
def RootOrdersEqual : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Finite K]
    (f : K[X]) (a b : L), Irreducible f → aeval a f = 0 → aeval b f = 0 →
      orderOf a = orderOf b

/-- With any chosen root, the existential definition is equivalent to that
root generating all units. The unit witness also asserts that it is nonzero. -/
def RootChoiceIndependent : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [Finite L] (n : ℕ) (f : K[X]),
    0 < n → Nat.card L = Nat.card K ^ n → f.Monic → f.natDegree = n →
    Irreducible f → ∀ b : L, aeval b f = 0 →
      (primitivePredicateValue K L n f ↔
        ∃ a : Lˣ, (a : L) = b ∧ Subgroup.zpowers a = ⊤)

/-- An actual base-preserving isomorphism transports the definition. -/
def BasePreservingInvariance : Prop :=
  ∀ (K : Type u) (L : Type v) (M : Type w) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] (_e : L ≃ₐ[K] M) (n : ℕ) (f : K[X]),
    primitivePredicateValue K L n f ↔ primitivePredicateValue K M n f

/-- The source's irreducible but nonprimitive polynomial X²+1 over F₃,
inside a specified algebraically closed ambient field. -/
def IrreducibleNotPrimitive : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra (ZMod 3) Ω] [IsAlgClosed Ω],
    ∃ E : IntermediateField (ZMod 3) Ω,
      Finite E ∧ Nat.card E = 9 ∧ Module.finrank (ZMod 3) E = 2 ∧ Nat.card Eˣ = 8 ∧
      (X ^ 2 + 1 : (ZMod 3)[X]).Monic ∧
      (X ^ 2 + 1 : (ZMod 3)[X]).natDegree = 2 ∧
      Irreducible (X ^ 2 + 1 : (ZMod 3)[X]) ∧
      (∀ b : E, aeval b (X ^ 2 + 1 : (ZMod 3)[X]) = 0 → orderOf b = 4) ∧
      ¬ primitivePredicateValue (ZMod 3) E 2 (X ^ 2 + 1)

end Specs.D07.Ch13.PrimitivePolynomials
