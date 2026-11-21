import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Complex.Module

/-! Canonical finite-partition data for quantitative insertion.

These definitions are shared by all downstream Specs. No analytic or refinement
certificate is part of partition validity. The expected values below independently
record each definition; the elementary order assertions are Prop definitions.
-/

noncomputable section

namespace D03Insertion

/-- Validity records precisely a positive number of cells, strict order, and both endpoints. -/
def ValidPartition (a b : ℝ) {k : ℕ} (u : Fin (k + 1) → ℝ) : Prop :=
  1 ≤ k ∧ StrictMono u ∧ u 0 = a ∧ u (Fin.last k) = b

/-- Left endpoint of cell i. -/
def left {k : ℕ} (u : Fin (k + 1) → ℝ) (i : Fin k) : ℝ :=
  u i.castSucc

/-- Right endpoint of cell i. -/
def right {k : ℕ} (u : Fin (k + 1) → ℝ) (i : Fin k) : ℝ :=
  u i.succ

/-- Length of cell i. -/
def width {k : ℕ} (u : Fin (k + 1) → ℝ) (i : Fin k) : ℝ :=
  right u i - left u i

/-- The finite set of partition nodes, without repetitions. -/
def nodes {k : ℕ} (u : Fin (k + 1) → ℝ) : Finset ℝ :=
  Finset.univ.image u

/-- Only indices strictly between the endpoint indices. -/
def interiorIndices (s : ℕ) : Finset (Fin (s + 1)) :=
  Finset.univ.filter (fun k => 0 < k.val ∧ k.val < s)

/-- The interior-point count m, with natural subtraction. -/
def interiorCount (s : ℕ) : ℕ :=
  s - 1

/-- A cell is marked only by a node in its open interior. -/
def marked {s n : ℕ} (p : Fin (s + 1) → ℝ) (q : Fin (n + 1) → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ k ∈ interiorIndices s, left q i < p k ∧ p k < right q i)

/-- The finite set of cell lengths. -/
def widths {n : ℕ} (q : Fin (n + 1) → ℝ) : Finset ℝ :=
  Finset.univ.image (width q)

/-- A total mesh: the largest width or zero. For valid partitions it is the largest width. -/
def mesh {n : ℕ} (q : Fin (n + 1) → ℝ) : ℝ :=
  (insert 0 (widths q)).max' (Finset.insert_nonempty 0 (widths q))

/-- Tags belong to closed cells, including their endpoints. -/
def Legal {a b : ℝ} {n : ℕ} (q : Fin (n + 1) → ℝ) (ξ : Fin n → Set.Icc a b) : Prop :=
  ∀ i, left q i ≤ (ξ i : ℝ) ∧ (ξ i : ℝ) ≤ right q i

/-- Tagged sum with real scalar multiplication, in particular for K = ℝ and K = ℂ. -/
def taggedSum {K : Type} [AddCommMonoid K] [Module ℝ K] {a b : ℝ} {n : ℕ}
    (f : Set.Icc a b → K) (q : Fin (n + 1) → ℝ) (ξ : Fin n → Set.Icc a b) : K :=
  ∑ i : Fin n, width q i • f (ξ i)

namespace Specification

def ValidPartitionType := ∀ (a b : ℝ) {k : ℕ} (u : Fin (k + 1) → ℝ), Prop

def ValidPartitionValue : ValidPartitionType :=
  fun (a b : ℝ) {k : ℕ} (u : Fin (k + 1) → ℝ) =>
    1 ≤ k ∧ StrictMono u ∧ u 0 = a ∧ u (Fin.last k) = b

def leftType := ∀ {k : ℕ} (u : Fin (k + 1) → ℝ) (i : Fin k), ℝ

def leftValue : leftType :=
  fun {k : ℕ} (u : Fin (k + 1) → ℝ) (i : Fin k) =>
    u i.castSucc

def rightType := ∀ {k : ℕ} (u : Fin (k + 1) → ℝ) (i : Fin k), ℝ

def rightValue : rightType :=
  fun {k : ℕ} (u : Fin (k + 1) → ℝ) (i : Fin k) =>
    u i.succ

def widthType := ∀ {k : ℕ} (u : Fin (k + 1) → ℝ) (i : Fin k), ℝ

def widthValue : widthType :=
  fun {k : ℕ} (u : Fin (k + 1) → ℝ) (i : Fin k) =>
    right u i - left u i

def nodesType := ∀ {k : ℕ} (u : Fin (k + 1) → ℝ), Finset ℝ

def nodesValue : nodesType :=
  fun {k : ℕ} (u : Fin (k + 1) → ℝ) =>
    Finset.univ.image u

def interiorIndicesType := ∀ (s : ℕ), Finset (Fin (s + 1))

def interiorIndicesValue : interiorIndicesType :=
  fun (s : ℕ) =>
    Finset.univ.filter (fun k => 0 < k.val ∧ k.val < s)

def interiorCountType := ∀ (s : ℕ), ℕ

def interiorCountValue : interiorCountType :=
  fun (s : ℕ) =>
    s - 1

def markedType := ∀ {s n : ℕ} (p : Fin (s + 1) → ℝ) (q : Fin (n + 1) → ℝ), Finset (Fin n)

def markedValue : markedType :=
  fun {s n : ℕ} (p : Fin (s + 1) → ℝ) (q : Fin (n + 1) → ℝ) =>
    Finset.univ.filter (fun i => ∃ k ∈ interiorIndices s, left q i < p k ∧ p k < right q i)

def widthsType := ∀ {n : ℕ} (q : Fin (n + 1) → ℝ), Finset ℝ

def widthsValue : widthsType :=
  fun {n : ℕ} (q : Fin (n + 1) → ℝ) =>
    Finset.univ.image (width q)

def meshType := ∀ {n : ℕ} (q : Fin (n + 1) → ℝ), ℝ

def meshValue : meshType :=
  fun {n : ℕ} (q : Fin (n + 1) → ℝ) =>
    (insert 0 (widths q)).max' (Finset.insert_nonempty 0 (widths q))

def LegalType := ∀ {a b : ℝ} {n : ℕ} (q : Fin (n + 1) → ℝ) (ξ : Fin n → Set.Icc a b), Prop

def LegalValue : LegalType :=
  fun {a b : ℝ} {n : ℕ} (q : Fin (n + 1) → ℝ) (ξ : Fin n → Set.Icc a b) =>
    ∀ i, left q i ≤ (ξ i : ℝ) ∧ (ξ i : ℝ) ≤ right q i

def taggedSumType := ∀ {K : Type} [AddCommMonoid K] [Module ℝ K] {a b : ℝ} {n : ℕ}
    (f : Set.Icc a b → K) (q : Fin (n + 1) → ℝ) (ξ : Fin n → Set.Icc a b), K

def taggedSumValue : taggedSumType :=
  fun {K : Type} [AddCommMonoid K] [Module ℝ K] {a b : ℝ} {n : ℕ}
    (f : Set.Icc a b → K) (q : Fin (n + 1) → ℝ) (ξ : Fin n → Set.Icc a b) =>
    ∑ i : Fin n, width q i • f (ξ i)

def width_posType : Prop :=
  ∀ {a b : ℝ} {n : ℕ} {q : Fin (n + 1) → ℝ},
    ValidPartition a b q → ∀ i : Fin n, 0 < width q i

def mesh_nonnegType : Prop :=
  ∀ {n : ℕ} (q : Fin (n + 1) → ℝ), 0 ≤ mesh q

def width_le_meshType : Prop :=
  ∀ {n : ℕ} (q : Fin (n + 1) → ℝ) (i : Fin n), width q i ≤ mesh q

def widths_nonemptyType : Prop :=
  ∀ {n : ℕ} (q : Fin (n + 1) → ℝ), 1 ≤ n → (widths q).Nonempty

def mesh_eq_maxType : Prop :=
  ∀ {a b : ℝ} {n : ℕ} {q : Fin (n + 1) → ℝ},
    ValidPartition a b q → ∀ h : (widths q).Nonempty,
      mesh q = (widths q).max' h

end Specification

end D03Insertion
