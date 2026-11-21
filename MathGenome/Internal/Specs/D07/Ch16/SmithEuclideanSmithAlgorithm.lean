import MathGenome.Internal.Specs.D07.Ch10.EuclideanDefinition
import Mathlib.Data.Matrix.Mul

/-! Independent interface for the Euclidean algorithmic supplement to
K07.16.smith, paper.tex:3190–3205. No Euclidean structure on an arbitrary PID
is used. The relation and chosen division operations are those already fixed
in the upstream Euclidean-definition specification. -/

universe u

namespace Specs.D07.Ch16.SmithEuclideanSmithAlgorithm

open Specs.D07.Ch10.EuclideanDefinition

/-- The elementary operations needed by this algorithm. Unit scalings are
unnecessary because no normalization of associates is requested. -/
inductive Operation (R : Type u) (m n : ℕ) where
  | swapRows (i j : Fin m)
  | swapCols (i j : Fin n)
  | addRow (i j : Fin m) (different : i ≠ j) (c : R)
  | addCol (i j : Fin n) (different : i ≠ j) (c : R)

/-- Direct entrywise semantics: `addCol i j c` adds c times column j to i. -/
def Operation.apply {R : Type u} [CommRing R] {m n : ℕ}
    (o : Operation R m n) (A : Matrix (Fin m) (Fin n) R) :
    Matrix (Fin m) (Fin n) R :=
  match o with
  | .swapRows i j => Matrix.of fun k l => A (Equiv.swap i j k) l
  | .swapCols i j => Matrix.of fun k l => A k (Equiv.swap i j l)
  | .addRow i j _ c => Matrix.of fun k l => if k = i then A k l + c * A j l else A k l
  | .addCol i j _ c => Matrix.of fun k l => if l = i then A k l + c * A k j else A k l

/-- Execute a finite ordered list of elementary operations. -/
def execute {R : Type u} [CommRing R] {m n : ℕ}
    (ops : List (Operation R m n)) (A : Matrix (Fin m) (Fin n) R) :
    Matrix (Fin m) (Fin n) R :=
  ops.foldl (fun B o => o.apply B) A

/-- Reachability records an actual finite operation list, not just abstract
matrix equivalence. -/
def Reachable {R : Type u} [CommRing R] {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) R) : Prop := ∃ ops, execute ops A = B

/-- Rectangular Smith form with exactly s nonzero initial diagonal entries.
The pointwise formula includes all unused rows and columns, as well as zeros
on and off the rest of the diagonal. Empty matrices and s=0 are allowed. -/
def SmithForm {R : Type u} [CommRing R] {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ (s : ℕ) (_hm : s ≤ m) (_hn : s ≤ n) (a : Fin s → R),
    (∀ i, a i ≠ 0) ∧
    (∀ i j, i ≤ j → a i ∣ a j) ∧
    ∀ i j, B i j = if h : i.val = j.val ∧ i.val < s then a ⟨i.val, h.2⟩ else 0

/-- A finite execution of the pivot loop. A finishing stage consists of a
finite border-clearing trace preserving the pivot. Every restart consists
of a finite elementary trace producing a strictly smaller nonzero pivot,
followed by the continuation at that new pivot. This records the loop
structure in addition to the flattened list of elementary instructions. -/
inductive PivotRun {R : Type u} [CommRing R] [IsDomain R] (d : EuclideanData R)
    {m n : ℕ} : Matrix (Fin (m+1)) (Fin (n+1)) R →
      Matrix (Fin (m+1)) (Fin (n+1)) R → Prop where
  | finish {A B} (trace : Reachable A B) (pivot : B 0 0 = A 0 0)
      (nonzero : A 0 0 ≠ 0)
      (column : ∀ i, i ≠ 0 → B i 0 = 0)
      (row : ∀ j, j ≠ 0 → B 0 j = 0)
      (divides : ∀ i j, B 0 0 ∣ B i j) : PivotRun d A B
  | restart {A C B} (trace : Reachable A C) (nonzero : C 0 0 ≠ 0)
      (decrease : d.smaller (C 0 0) (A 0 0)) (tail : PivotRun d C B) : PivotRun d A B

/-- A nonzero initial pivot always admits a finite loop execution. -/
def PivotPreparationTerminates : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (d : EuclideanData R)
    (m n : ℕ) (A : Matrix (Fin (m+1)) (Fin (n+1)) R),
    A 0 0 ≠ 0 → ∃ B, PivotRun d A B

/-- Every completed loop gives a finite instruction trace with a cleared
border and a nonzero pivot dividing every entry. -/
def PivotRunCorrectness : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (d : EuclideanData R)
    (m n : ℕ) (A B : Matrix (Fin (m+1)) (Fin (n+1)) R),
    PivotRun d A B → Reachable A B ∧ B 0 0 ≠ 0 ∧
      (∀ i, i ≠ 0 → B i 0 = 0) ∧ (∀ j, j ≠ 0 → B 0 j = 0) ∧
      (∀ i j, B 0 0 ∣ B i j)

/-- Full finite elementary-operation construction. -/
def AlgorithmTerminates : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (_d : EuclideanData R)
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) R),
    ∃ ops : List (Operation R m n), SmithForm (execute ops A)

/-- Every operation trace yields actual invertible left and right factors. -/
def OperationCorrectness : Prop :=
  ∀ (R : Type u) [CommRing R] (m n : ℕ)
    (ops : List (Operation R m n)) (A : Matrix (Fin m) (Fin n) R),
    ∃ (P : Matrix (Fin m) (Fin m) R) (Q : Matrix (Fin n) (Fin n) R),
      IsUnit P ∧ IsUnit Q ∧ execute ops A = P * A * Q

/-- The requested conclusion, with both elementary provenance and invertible
factors. No finite-generation or nonzero-dimension assumptions are added. -/
def SmithConstruction : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (_d : EuclideanData R)
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) R),
    ∃ (ops : List (Operation R m n))
      (P : Matrix (Fin m) (Fin m) R) (Q : Matrix (Fin n) (Fin n) R),
      IsUnit P ∧ IsUnit Q ∧ execute ops A = P * A * Q ∧ SmithForm (P * A * Q)

/-- Once the first row and column have been cleared, a block entry not
divisible by the pivot produces, by the stated operations, a nonzero pivot
strictly smaller in the original Euclidean relation. -/
def BlockFailureReduction : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (d : EuclideanData R)
    (m n : ℕ) (A : Matrix (Fin (m+1)) (Fin (n+1)) R),
    A 0 0 ≠ 0 →
    (∀ i, i ≠ 0 → A i 0 = 0) → (∀ j, j ≠ 0 → A 0 j = 0) →
    ∀ i j, ¬ A 0 0 ∣ A i j →
      ∃ ops : List (Operation R (m+1) (n+1)),
        execute ops A 0 0 = d.remainder (A i j) (A 0 0) ∧
        execute ops A 0 0 ≠ 0 ∧ d.smaller (execute ops A 0 0) (A 0 0)

/-- Strict pivot replacements cannot continue forever, including replacements
caused by entries outside the first row and column. -/
def NoInfiniteRestarts : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (d : EuclideanData R)
    (p : ℕ → R), ¬ (∀ k, d.smaller (p (k+1)) (p k))

end Specs.D07.Ch16.SmithEuclideanSmithAlgorithm
