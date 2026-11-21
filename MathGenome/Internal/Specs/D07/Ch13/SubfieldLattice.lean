import MathGenome.Internal.Specs.D07.Ch13.Existence
import Mathlib.Algebra.Field.ZMod

/-! Independent statements for K07.13.subfield_lattice, paper.tex:3931–3940.
The ambient field is one fixed algebraic closure of the specified finite base.
Intermediate fields of its canonical degree-n field are represented as fields
in that closure contained in it. Thus equality below is equality of embedded
fields, with the base embedding retained. -/

universe u v

namespace Specs.D07.Ch13.SubfieldLattice

open Existence

/-- Every positive divisor gives the specified embedded field, with the exact
root set, cardinality and degree. It is the only embedded field of that size. -/
def DivisorField : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Finite K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
    (q n d : ℕ), Nat.card K = q → 1 ≤ n → 1 ≤ d → d ∣ n →
      let E := rootFieldValue K Ω q d
      E ≤ rootFieldValue K Ω q n ∧ Finite E ∧ Nat.card E = q ^ d ∧
        FiniteDimensional K E ∧ Module.finrank K E = d ∧
        (∀ x : Ω, x ∈ E ↔ x ^ (q ^ d) = x) ∧
        (∀ M : IntermediateField K Ω, Finite M → Nat.card M = q ^ d → M = E)

/-- No other intermediate fields occur, and the positive divisor indexing
any particular intermediate field is unique. -/
def EmbeddedClassification : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Finite K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
    (q n : ℕ), Nat.card K = q → 1 ≤ n →
      ∀ E : IntermediateField K Ω,
        E ≤ rootFieldValue K Ω q n ↔
          ∃! d : ℕ, 1 ≤ d ∧ d ∣ n ∧ E = rootFieldValue K Ω q d

/-- All subfields, without a premise that they contain the prime field.
The prime-field containment must be proved. The divisor fields and their
root descriptions are the same canonical ones as in `DivisorField`. -/
def PrimeSubfieldClassification : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type v) [Field Ω] [Algebra (ZMod p) Ω]
    [Algebra.IsAlgebraic (ZMod p) Ω] [IsAlgClosed Ω]
    (n : ℕ), 1 ≤ n → ∀ S : Subfield Ω,
      S ≤ (rootFieldValue (ZMod p) Ω p n).toSubfield ↔
        ∃! d : ℕ, 1 ≤ d ∧ d ∣ n ∧
          S = (rootFieldValue (ZMod p) Ω p d).toSubfield

end Specs.D07.Ch13.SubfieldLattice
