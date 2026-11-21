import Mathlib.FieldTheory.Finite.Basic

/-!
Independent statements for K07.13.universal_factorization, paper.tex:3982–3988.
K is the fixed finite base and q is its actual cardinality. The statement is
intrinsic to K[X], so no identification with an unrelated finite-field copy
or choice of an algebraic closure is needed. For irreducible polynomials,
natDegree is the ordinary (positive) degree.
-/

universe u
namespace Specs.D07.Ch13.UniversalFactorization

open Polynomial

/-- The criterion applies to all irreducibles, without a monicity assumption. -/
def IrreducibleDivisibility : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] (q n : ℕ),
    Nat.card K = q → 1 ≤ n → ∀ f : K[X], Irreducible f →
      (f ∣ X ^ (q ^ n) - X ↔ f.natDegree ∣ n)

/-- The index set is finite, contains exactly the indicated monic
irreducibles, and the product takes each of them once. -/
def Factorization : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] (q n : ℕ),
    Nat.card K = q → 1 ≤ n →
      ∃ s : Finset K[X],
        (∀ f : K[X], f ∈ s ↔ f.Monic ∧ Irreducible f ∧ f.natDegree ∣ n) ∧
        (X ^ (q ^ n) - X : K[X]) = ∏ f ∈ s, f

end Specs.D07.Ch13.UniversalFactorization
