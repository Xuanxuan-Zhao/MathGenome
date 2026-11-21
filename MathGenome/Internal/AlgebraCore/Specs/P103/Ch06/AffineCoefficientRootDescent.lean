import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-! The finite constant-root construction in the inseparable reduction of
Theorem 6.8 (paper.tex, lines 1127–1129). All fields are actual subfields of Ω.
The finite set C records explicitly that the constant extension is generated
by finitely many roots of constants. No perfection of k is assumed. -/
namespace P103.Ch06.CoefficientRootDescent

universe u v

/-- The complete finite coefficient descent statement. `S` consists of elements
of the actual rational function field k(t). Empty families and exponent zero
are allowed. -/
def coefficientRootDescentType : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (d : ℕ) (t : Fin d → Ω), AlgebraicIndependent k t →
    ∀ (e : ℕ) (S : Finset (IntermediateField.adjoin k (Set.range t))),
    ∃ (C : Finset Ω) (c : IntermediateField k Ω) (z : Fin d → Ω),
      c = IntermediateField.adjoin k (C : Set Ω) ∧
      (∀ x ∈ C, x ^ (p ^ e) ∈ (algebraMap k Ω).range) ∧
      Module.Finite k c ∧ IsPurelyInseparable k c ∧
      (∀ a : c, (a : Ω) ^ (p ^ e) ∈ (algebraMap k Ω).range) ∧
      (∀ i, z i ^ (p ^ e) = t i) ∧
      (let P := (IntermediateField.adjoin c (Set.range z)).restrictScalars k
       IntermediateField.adjoin k (Set.range t) ≤ P ∧
       ∀ a ∈ S, ∃ b : P, (b : Ω) ^ (p ^ e) = (a : Ω))

end P103.Ch06.CoefficientRootDescent
