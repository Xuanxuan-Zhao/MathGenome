import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.FinitePartitionData

/-! Elementary order facts for the shared finite-partition vocabulary. -/

noncomputable section

namespace D03Insertion

/-! The canonical vocabulary lives in the independent shared Spec so downstream
Specs can use it without importing proofs. These candidate definitions reuse
that vocabulary and give each definition binding a candidate-owned declaration. -/
namespace Implementation

def ValidPartition (a b : ℝ) {k : ℕ} (u : Fin (k + 1) → ℝ) : Prop :=
  D03Insertion.ValidPartition a b u

def left {k : ℕ} (u : Fin (k + 1) → ℝ) (i : Fin k) : ℝ :=
  D03Insertion.left u i

def right {k : ℕ} (u : Fin (k + 1) → ℝ) (i : Fin k) : ℝ :=
  D03Insertion.right u i

def width {k : ℕ} (u : Fin (k + 1) → ℝ) (i : Fin k) : ℝ :=
  D03Insertion.width u i

def nodes {k : ℕ} (u : Fin (k + 1) → ℝ) : Finset ℝ :=
  D03Insertion.nodes u

def interiorIndices (s : ℕ) : Finset (Fin (s + 1)) :=
  D03Insertion.interiorIndices s

def interiorCount (s : ℕ) : ℕ :=
  D03Insertion.interiorCount s

def marked {s n : ℕ} (p : Fin (s + 1) → ℝ) (q : Fin (n + 1) → ℝ) : Finset (Fin n) :=
  D03Insertion.marked p q

def widths {n : ℕ} (q : Fin (n + 1) → ℝ) : Finset ℝ :=
  D03Insertion.widths q

def mesh {n : ℕ} (q : Fin (n + 1) → ℝ) : ℝ :=
  D03Insertion.mesh q

def Legal {a b : ℝ} {n : ℕ} (q : Fin (n + 1) → ℝ) (ξ : Fin n → Set.Icc a b) : Prop :=
  D03Insertion.Legal q ξ

def taggedSum {K : Type} [AddCommMonoid K] [Module ℝ K] {a b : ℝ} {n : ℕ}
    (f : Set.Icc a b → K) (q : Fin (n + 1) → ℝ) (ξ : Fin n → Set.Icc a b) : K :=
  D03Insertion.taggedSum f q ξ

end Implementation

theorem width_pos {a b : ℝ} {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : ValidPartition a b q) (i : Fin n) : 0 < width q i := by
  exact sub_pos.mpr (hq.2.1 i.castSucc_lt_succ)

theorem mesh_nonneg {n : ℕ} (q : Fin (n + 1) → ℝ) : 0 ≤ mesh q := by
  exact Finset.le_max' _ _ (Finset.mem_insert_self 0 (widths q))

theorem width_le_mesh {n : ℕ} (q : Fin (n + 1) → ℝ) (i : Fin n) :
    width q i ≤ mesh q := by
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

theorem widths_nonempty {n : ℕ} (q : Fin (n + 1) → ℝ) (hn : 1 ≤ n) :
    (widths q).Nonempty := by
  let i : Fin n := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩
  exact ⟨width q i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

/-- The zero adjoined in the total definition of mesh never changes the
maximum of the widths of a valid partition. -/
theorem mesh_eq_max {a b : ℝ} {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : ValidPartition a b q) (h : (widths q).Nonempty) :
    mesh q = (widths q).max' h := by
  have hmax : 0 ≤ (widths q).max' h := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.max'_mem (widths q) h)
    rw [← hi]
    exact (width_pos hq i).le
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact hx ▸ hmax
    · exact Finset.le_max' _ _ hx
  · apply Finset.max'_le
    intro x hx
    exact Finset.le_max' _ _ (Finset.mem_insert_of_mem hx)

end D03Insertion
