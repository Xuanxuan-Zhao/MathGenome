import MathGenome.Internal.Specs.D05.Foundations.Division
import MathGenome.Internal.Specs.D05.M04.MatrixProduct
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.GroupTheory.Perm.Basic

/-! Independent statements for the existence/termination stage of
paper.tex:1468–1481. All matrices have formal polynomial entries. The operation
type permits only swaps, additions of polynomial multiples of different rows or
columns, and rescaling by a nonzero element of the base field. A list records a
finite sequence, including the empty sequence in zero and empty shapes. -/
noncomputable section

namespace D05.M10.Smith

/-- Operations over K[x]; the rescaling parameter is a unit of K, not K(x). -/
inductive Operation (K : Type*) [Field K] (m n : ℕ) where
  | swapRows (i j : Fin m)
  | swapCols (i j : Fin n)
  | addRow (i j : Fin m) (distinct : i ≠ j) (q : Polynomial K)
  | addCol (i j : Fin n) (distinct : i ≠ j) (q : Polynomial K)
  | scaleRow (i : Fin m) (c : Kˣ)
  | scaleCol (j : Fin n) (c : Kˣ)

namespace Operation
variable {K : Type*} [Field K] {m n : ℕ}

/-- The entrywise meaning of each permitted operation. -/
def apply : Operation K m n → Matrix (Fin m) (Fin n) (Polynomial K) →
    Matrix (Fin m) (Fin n) (Polynomial K)
  | .swapRows i j, M => fun a b => M (Equiv.swap i j a) b
  | .swapCols i j, M => fun a b => M a (Equiv.swap i j b)
  | .addRow i j _ q, M => fun a b => if a = i then M a b + q * M j b else M a b
  | .addCol i j _ q, M => fun a b => if b = i then M a b + q * M a j else M a b
  | .scaleRow i c, M => fun a b => if a = i then Polynomial.C (c : K) * M a b else M a b
  | .scaleCol j c, M => fun a b => if b = j then Polynomial.C (c : K) * M a b else M a b

/-- Inverse operation: all its parameters remain permitted. -/
def inverse : Operation K m n → Operation K m n
  | .swapRows i j => .swapRows i j
  | .swapCols i j => .swapCols i j
  | .addRow i j h q => .addRow i j h (-q)
  | .addCol i j h q => .addCol i j h (-q)
  | .scaleRow i c => .scaleRow i c⁻¹
  | .scaleCol j c => .scaleCol j c⁻¹

end Operation

/-- Operations are applied in the order in which they occur in the list. -/
def run {K : Type*} [Field K] {m n : ℕ} (ops : List (Operation K m n))
    (M : Matrix (Fin m) (Fin n) (Polynomial K)) := ops.foldl (fun A op => op.apply A) M

/-- Reachability requires an actual finite list, not an assumed invertible change of basis. -/
def Reachable {K : Type*} [Field K] {m n : ℕ}
    (M N : Matrix (Fin m) (Fin n) (Polynomial K)) : Prop := ∃ ops, run ops M = N

/-- A rectangular diagonal with its nonzero monic entries first, in increasing
order of divisibility. The sequence is extended by zero to make empty shapes
and the final divisibility condition uniform. -/
def IsSmith {K : Type*} [Field K] {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) (Polynomial K)) : Prop :=
  ∃ (r : ℕ) (d : ℕ → Polynomial K), r ≤ min m n ∧
    (∀ i, i < r → d i ≠ 0 ∧ (d i).Monic) ∧
    (∀ i, r ≤ i → d i = 0) ∧
    (∀ i, d i ∣ d (i + 1)) ∧
    (∀ i j, D i j = if i.val = j.val then d i.val else 0)

end D05.M10.Smith

namespace D05.Specs.InvariantFactorComputation.Existence
open D05.M10.Smith

/-- Full original existence obligation, with a finite operation witness. -/
def smithReduction : Prop := ∀ (K : Type*) [Field K] (m n : ℕ)
    (M : Matrix (Fin m) (Fin n) (Polynomial K)),
  ∃ ops : List (Operation K m n), IsSmith (run ops M)

/-- Invertibility is required for every operation, on every rectangular shape. -/
def operationInverse : Prop := ∀ (K : Type*) [Field K] (m n : ℕ)
    (op : Operation K m n) (M : Matrix (Fin m) (Fin n) (Polynomial K)),
  op.inverse.apply (op.apply M) = M ∧ op.apply (op.inverse.apply M) = M

/-- A failed divisibility test gives a nonzero, strictly smaller-degree remainder. -/
def remainderDescent : Prop := ∀ (K : Type*) [Field K] (a b : Polynomial K),
  a ≠ 0 → ¬a ∣ b → b % a ≠ 0 ∧ (b % a).natDegree < a.natDegree

/-- A nondivisible entry in an isolated trailing block causes a genuine pivot
reduction using permitted operations, before any smaller rectangle is processed. -/
def trailingEntryDescent : Prop := ∀ (K : Type*) [Field K] (m n : ℕ)
    (M : Matrix (Fin (m+1)) (Fin (n+1)) (Polynomial K))
    (i : Fin m) (j : Fin n),
  M 0 0 ≠ 0 → (∀ k : Fin m, M k.succ 0 = 0) →
  (∀ l : Fin n, M 0 l.succ = 0) → ¬M 0 0 ∣ M i.succ j.succ →
    ∃ N, Reachable M N ∧ N 0 0 ≠ 0 ∧ (N 0 0).natDegree < (M 0 0).natDegree

/-- The degree relation on nonzero pivots is well founded. -/
def pivotTermination : Prop := ∀ (K : Type*) [Field K],
  WellFounded (fun a b : {p : Polynomial K // p ≠ 0} => a.val.natDegree < b.val.natDegree)

end D05.Specs.InvariantFactorComputation.Existence
