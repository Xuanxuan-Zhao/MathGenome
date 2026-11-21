import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.HouseholderReflector
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Reindex

noncomputable section
open Matrix
namespace NumAnalysis206.HouseholderQRDefinitions
open NumAnalysis206.MatrixDefinitions NumAnalysis206.HouseholderDefinitions

/-- The original coordinate order, partitioned just before coordinate k. -/
def split (m k : ℕ) (h : k ≤ m) : Fin k ⊕ Fin (m-k) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

/-- Extend a tail operation by the identity on all preceding coordinates. -/
def blockLift {m k : ℕ} (h : k ≤ m) (T : Mat ℝ (m-k) (m-k)) : Mat ℝ m m :=
  (fromBlocks (1 : Mat ℝ k k) 0 0 T).submatrix (split m k h).symm (split m k h).symm

def tail {m n : ℕ} (B : Mat ℝ m n) (j : Fin n) (h : n ≤ m) : Vec ℝ (m-j.val) :=
  WithLp.toLp 2 (fun i => B (split m j.val (by omega) (Sum.inr i)) j)

/-- Exactly the accepted stable-sign step on the current column tail. -/
def update {m n : ℕ} (B : Mat ℝ m n) (j : Fin n) (h : n ≤ m) : Mat ℝ m m :=
  haveI : NeZero (m-j.val) := ⟨by have := j.isLt; omega⟩
  blockLift (by omega) (step (tail B j h))

/-- Successive left updates, in increasing column order. Stages beyond n idle. -/
def run {m n : ℕ} (A : Mat ℝ m n) (h : n ≤ m) : ℕ → Mat ℝ m n
  | 0 => A
  | k+1 => if hk : k < n then update (run A h k) ⟨k,hk⟩ h * run A h k else run A h k

/-- The same actual orthogonal updates accumulated in their order of application. -/
def product {m n : ℕ} (A : Mat ℝ m n) (h : n ≤ m) : ℕ → Mat ℝ m m
  | 0 => 1
  | k+1 => if hk : k < n then update (run A h k) ⟨k,hk⟩ h * product A h k else product A h k

/-- Every processed column has zeros strictly below its diagonal position. -/
def Cleared {m n : ℕ} (B : Mat ℝ m n) (k : ℕ) : Prop :=
  ∀ c : Fin n, c.val < k → ∀ i : Fin m, c.val < i.val → B i c = 0

def rFactor {m n : ℕ} (A : Mat ℝ m n) (h : n ≤ m) : Mat ℝ n n :=
  (run A h n).submatrix (Fin.castLE h) id

def qFactor {m n : ℕ} (A : Mat ℝ m n) (h : n ≤ m) : Mat ℝ m n :=
  (product A h n).conjTranspose.submatrix id (Fin.castLE h)

/-- Simultaneous column/row signs, fixed even when a diagonal entry is zero. -/
def signs {n : ℕ} (R : Mat ℝ n n) : Mat ℝ n n :=
  diagonal (fun i => signPlus (R i i))

def positiveQ {m n : ℕ} (A : Mat ℝ m n) (h : n ≤ m) : Mat ℝ m n :=
  qFactor A h * signs (rFactor A h)

def positiveR {m n : ℕ} (A : Mat ℝ m n) (h : n ≤ m) : Mat ℝ n n :=
  signs (rFactor A h) * rFactor A h

end NumAnalysis206.HouseholderQRDefinitions

namespace Specs.NumAnalysis206.HouseholderExactQR
open NumAnalysis206.MatrixDefinitions NumAnalysis206.HouseholderQRDefinitions

/-- Zero tails cause the full update to be the identity. -/
def zero_tail : Prop :=
  ∀ {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j : Fin n),
    tail B j h = 0 → update B j h = 1

/-- One actual update is orthogonal, fixes previous cleared columns, and clears
its own column. The zero-tail identity is part of the step definition. -/
def one_step : Prop :=
  ∀ {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j : Fin n),
    (update B j h).conjTranspose * update B j h = 1 ∧
    (Cleared B j.val →
      (∀ c : Fin n, c.val < j.val → ∀ i, (update B j h * B) i c = B i c) ∧
      Cleared (update B j h * B) (j.val+1))

/-- All prefixes of the deterministic run have their claimed exact meaning. -/
def construction : Prop :=
  ∀ {m n : ℕ} (A : Mat ℝ m n) (h : n ≤ m) (k : ℕ), k ≤ n →
    run A h k = product A h k * A ∧
    (product A h k).conjTranspose * product A h k = 1 ∧
    Cleared (run A h k) k

/-- The reduction is literally [R;0], in the original row order; Q consists of
first n columns of the inverse orthogonal product. Includes n=0 and singular A. -/
def exact_qr : Prop :=
  ∀ {m n : ℕ} (A : Mat ℝ m n) (h : n ≤ m),
    (∀ i : Fin m, n ≤ i.val → ∀ j, run A h n i j = 0) ∧
    A = qFactor A h * rFactor A h ∧
    (qFactor A h).conjTranspose * qFactor A h = 1 ∧
    NumAnalysis206.MatrixDefinitions.IsUpperTriangular (rFactor A h)

/-- Signs applied to the constructed factors give the source's positive-diagonal
normalization whenever the original columns are independent. -/
def positive_diagonal : Prop :=
  ∀ {m n : ℕ} (A : Mat ℝ m n) (h : n ≤ m), FullColumnRank A →
    ReducedQR A (positiveQ A h) (positiveR A h)

def split_type := (m k : ℕ) → (h : k ≤ m) → (Fin k ⊕ Fin (m-k) ≃ Fin m)
def split_value : split_type := @NumAnalysis206.HouseholderQRDefinitions.split

def blockLift_type := {m k : ℕ} → (h : k ≤ m) → Mat ℝ (m-k) (m-k) → Mat ℝ m m
def blockLift_value : blockLift_type := @NumAnalysis206.HouseholderQRDefinitions.blockLift

def tail_type := {m n : ℕ} → Mat ℝ m n → (j : Fin n) → n ≤ m → Vec ℝ (m-j.val)
def tail_value : tail_type := @NumAnalysis206.HouseholderQRDefinitions.tail

def update_type := {m n : ℕ} → Mat ℝ m n → Fin n → n ≤ m → Mat ℝ m m
def update_value : update_type := @NumAnalysis206.HouseholderQRDefinitions.update

def run_type := {m n : ℕ} → Mat ℝ m n → n ≤ m → ℕ → Mat ℝ m n
def run_value : run_type := @NumAnalysis206.HouseholderQRDefinitions.run

def product_type := {m n : ℕ} → Mat ℝ m n → n ≤ m → ℕ → Mat ℝ m m
def product_value : product_type := @NumAnalysis206.HouseholderQRDefinitions.product

def Cleared_type := {m n : ℕ} → Mat ℝ m n → ℕ → Prop
def Cleared_value : Cleared_type := @NumAnalysis206.HouseholderQRDefinitions.Cleared

def rFactor_type := {m n : ℕ} → Mat ℝ m n → n ≤ m → Mat ℝ n n
def rFactor_value : rFactor_type := @NumAnalysis206.HouseholderQRDefinitions.rFactor

def qFactor_type := {m n : ℕ} → Mat ℝ m n → n ≤ m → Mat ℝ m n
def qFactor_value : qFactor_type := @NumAnalysis206.HouseholderQRDefinitions.qFactor

def signs_type := {n : ℕ} → Mat ℝ n n → Mat ℝ n n
def signs_value : signs_type := @NumAnalysis206.HouseholderQRDefinitions.signs

def positiveQ_type := {m n : ℕ} → Mat ℝ m n → n ≤ m → Mat ℝ m n
def positiveQ_value : positiveQ_type := @NumAnalysis206.HouseholderQRDefinitions.positiveQ

def positiveR_type := {m n : ℕ} → Mat ℝ m n → n ≤ m → Mat ℝ n n
def positiveR_value : positiveR_type := @NumAnalysis206.HouseholderQRDefinitions.positiveR

end Specs.NumAnalysis206.HouseholderExactQR
