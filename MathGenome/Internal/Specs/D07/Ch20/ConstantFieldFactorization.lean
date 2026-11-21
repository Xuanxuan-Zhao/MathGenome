import MathGenome.Internal.Specs.D07.Ch13.Existence
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.FieldDivision

/-! K07.20.constant_field_factorization, paper.tex:6074–6087.
The new constants are the specified embedded root field in the common closure.
The finite set in the conclusion records distinct factors; its product has no
unit multiplier because both the input and all factors are monic. -/

universe u v
namespace Specs.D07.Ch20.ConstantFieldFactorization
open Polynomial
open Specs.D07.Ch13.Existence

def Factorization : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Finite K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
    (q n k : ℕ), Nat.card K = q → 1 ≤ n → 1 ≤ k →
    ∀ (f : K[X]), f.Monic → Irreducible f → f.natDegree = n →
    let E := rootFieldValue K Ω q k
    ∃ s : Finset E[X],
      s.card = Nat.gcd n k ∧
      (∀ g ∈ s, g.Monic ∧ Irreducible g ∧ g.natDegree = n / Nat.gcd n k) ∧
      f.map (algebraMap K E) = ∏ g ∈ s, g

def RemainsIrreducible : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Finite K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
    (q n k : ℕ), Nat.card K = q → 1 ≤ n → 1 ≤ k →
    ∀ (f : K[X]), f.Monic → Irreducible f → f.natDegree = n →
    let E := rootFieldValue K Ω q k
    Irreducible (f.map (algebraMap K E)) ↔ Nat.gcd n k = 1

end Specs.D07.Ch20.ConstantFieldFactorization
