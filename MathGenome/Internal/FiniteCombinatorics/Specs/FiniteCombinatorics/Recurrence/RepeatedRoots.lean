import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Recurrence.InitialValues
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Recurrence.RootSequences
import Mathlib.LinearAlgebra.Basis.Defs

/-! Independent statements for the split-characteristic basis assertion in
`paper.tex`, p204:W16. The finite set indexes distinct roots. No restriction on
field characteristic, and no assumption that the roots are nonzero, is imposed.
The solution module and coefficient sequences are the accepted upstream objects. -/
noncomputable section
open scoped BigOperators
open Polynomial
universe u
namespace Specs.FiniteCombinatorics.Recurrence

/-- Membership of every member of the repeated-root family. -/
def repeated_root_membership : Prop :=
  ∀ {K : Type u} [Field K] {r : ℕ} (c : Fin r → K)
    (s : Finset K) (m : K → ℕ),
    characteristicPolynomialValue c = ∏ lam ∈ s, (X - C lam) ^ m lam →
    ∀ i : Σ lam : s, Fin (m lam.val),
      rootSequenceValue i.1.val i.2.val ∈ solutionSpaceValue c

/-- Joint independence for arbitrary distinct roots and chain lengths. -/
def repeated_root_independence : Prop :=
  ∀ {K : Type u} [Field K] (s : Finset K) (m : K → ℕ),
    LinearIndependent K (fun i : Σ lam : s, Fin (m lam.val) =>
      rootSequenceValue i.1.val i.2.val)

/-- The degree of the characteristic polynomial accounts for all multiplicities. -/
def repeated_root_multiplicities : Prop :=
  ∀ {K : Type u} [Field K] {r : ℕ} (c : Fin r → K)
    (s : Finset K) (m : K → ℕ),
    characteristicPolynomialValue c = ∏ lam ∈ s, (X - C lam) ^ m lam →
    ∑ lam ∈ s, m lam = r

/-- Full basis statement, retaining the source's order and multiplicity hypotheses. -/
def repeated_root_basis : Prop :=
  ∀ {K : Type u} [Field K] {r : ℕ} (c : Fin r → K), 1 ≤ r →
    ∀ (s : Finset K) (m : K → ℕ), (∀ lam ∈ s, 0 < m lam) →
    characteristicPolynomialValue c = ∏ lam ∈ s, (X - C lam) ^ m lam →
    ∃ B : Module.Basis (Σ lam : s, Fin (m lam.val)) K (solutionSpaceValue c),
      ∀ i, (B i : ℕ → K) = rootSequenceValue i.1.val i.2.val

/-- Spanning and uniqueness as an explicit expansion of every solution sequence. -/
def repeated_root_expansion : Prop :=
  ∀ {K : Type u} [Field K] {r : ℕ} (c : Fin r → K), 1 ≤ r →
    ∀ (s : Finset K) (m : K → ℕ), (∀ lam ∈ s, 0 < m lam) →
    characteristicPolynomialValue c = ∏ lam ∈ s, (X - C lam) ^ m lam →
    ∀ a : ℕ → K, IsSolutionValue c a →
    ∃! d : (Σ lam : s, Fin (m lam.val)) → K,
      a = ∑ i, d i • rootSequenceValue i.1.val i.2.val

end Specs.FiniteCombinatorics.Recurrence
