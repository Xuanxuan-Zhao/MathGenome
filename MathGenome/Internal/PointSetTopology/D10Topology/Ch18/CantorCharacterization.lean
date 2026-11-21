import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.CantorCharacterization
import MathGenome.Internal.PointSetTopology.D10Topology.Ch18.CantorModel
import MathGenome.Internal.PointSetTopology.D10Topology.Ch18.ClopenPartitions
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Metrizable.Uniformity

noncomputable section
open Set TopologicalSpace
open scoped Topology Classical
universe u
namespace D10Topology.Ch18
namespace CantorCharacterization

variable {X : Type u} [MetricSpace X] [CompactSpace X]

/-- A nonempty clopen cell in the recursive binary partition. -/
structure Cell (X : Type u) [TopologicalSpace X] where
  carrier : Set X
  clopen : IsClopen carrier
  nonempty : carrier.Nonempty

/-- A binary split can also decide membership in any specified clopen set. -/
theorem exists_deciding_split (hz : Ch06.ZeroDimensional X)
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X)) (H : Cell X)
    (B : Set X) (hB : IsClopen B) :
    ∃ P : Bool → Cell X,
      (∀ b, (P b).carrier ⊆ H.carrier) ∧
      Disjoint (P false).carrier (P true).carrier ∧
      (P false).carrier ∪ (P true).carrier = H.carrier ∧
      ∀ b, (P b).carrier ⊆ B ∨ (P b).carrier ⊆ Bᶜ := by
  classical
  by_cases h : (H.carrier ∩ B).Nonempty ∧ (H.carrier ∩ Bᶜ).Nonempty
  · let L : Cell X := ⟨H.carrier ∩ B, H.clopen.inter hB, h.1⟩
    let R : Cell X := ⟨H.carrier ∩ Bᶜ, H.clopen.inter hB.compl, h.2⟩
    refine ⟨(fun b => cond b R L), ?_, ?_, ?_, ?_⟩
    · intro b; cases b <;> exact inter_subset_left
    · exact disjoint_left.mpr (fun x hx hy => hy.2 hx.2)
    · ext x; simp [L, R]
    · intro b; cases b
      · exact Or.inl inter_subset_right
      · exact Or.inr inter_subset_right
  · obtain ⟨Q, hQ⟩ := split_clopen_part hz hno H.carrier H.clopen H.nonempty 2 (by decide)
    have hsub (i : Fin 2) : Q i ⊆ H.carrier := by
      rw [← hQ.2.2.2]
      exact subset_iUnion Q i
    let L : Cell X := ⟨Q 0, hQ.1 0, hQ.2.1 0⟩
    let R : Cell X := ⟨Q 1, hQ.1 1, hQ.2.1 1⟩
    have hdec : H.carrier ⊆ B ∨ H.carrier ⊆ Bᶜ := by
      by_cases hleft : (H.carrier ∩ B).Nonempty
      · left
        intro x hx
        by_contra hxB
        exact h ⟨hleft, ⟨x, hx, hxB⟩⟩
      · right
        intro x hx hxB
        exact hleft ⟨x, hx, hxB⟩
    refine ⟨(fun b => cond b R L), ?_, ?_, ?_, ?_⟩
    · intro b; cases b <;> exact hsub _
    · exact hQ.2.2.1 (by decide : (0 : Fin 2) ≠ 1)
    · change Q 0 ∪ Q 1 = H.carrier
      rw [← hQ.2.2.2]
      ext x
      simp only [mem_union, mem_iUnion]
      constructor
      · rintro (h | h)
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      · rintro ⟨i, hi⟩
        fin_cases i <;> simp_all
    · intro b
      exact hdec.imp (fun hB => (by cases b <;> exact (hsub _).trans hB))
        (fun hB => (by cases b <;> exact (hsub _).trans hB))


/-- The basis is decided successively, with one genuine binary split at
 every node. Lists are stored with the most recent bit first. -/
structure BinaryPartition (X : Type u) [TopologicalSpace X] (B : ℕ → Set X) where
  cell : List Bool → Cell X
  root : (cell []).carrier = univ
  child_subset : ∀ l b, (cell (b :: l)).carrier ⊆ (cell l).carrier
  child_disjoint : ∀ l, Disjoint (cell (false :: l)).carrier (cell (true :: l)).carrier
  child_union : ∀ l,
    (cell (false :: l)).carrier ∪ (cell (true :: l)).carrier = (cell l).carrier
  decides : ∀ l b,
    (cell (b :: l)).carrier ⊆ B l.length ∨ (cell (b :: l)).carrier ⊆ (B l.length)ᶜ

private def partitionNode [Nonempty X] (split : ℕ → Cell X → Bool → Cell X) :
    List Bool → Cell X
  | [] => ⟨univ, isClopen_univ, Set.univ_nonempty⟩
  | b :: l => split l.length (partitionNode split l) b

theorem exists_binaryPartition [Nonempty X] (hz : Ch06.ZeroDimensional X)
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X)) (B : ℕ → Set X)
    (hB : ∀ n, IsClopen (B n)) : Nonempty (BinaryPartition X B) := by
  classical
  choose split hs hd hu hb using fun n H => exists_deciding_split hz hno H (B n) (hB n)
  exact ⟨{
    cell := partitionNode split
    root := rfl
    child_subset := fun l b => hs l.length (partitionNode split l) b
    child_disjoint := fun l => hd l.length (partitionNode split l)
    child_union := fun l => hu l.length (partitionNode split l)
    decides := fun l b => hb l.length (partitionNode split l) b }⟩

namespace BinaryPartition
section Branches
variable {Y : Type u} [TopologicalSpace Y] [CompactSpace Y]
variable {B : ℕ → Set Y} (T : BinaryPartition Y B)

/-- Compactness supplies a point on every infinite branch. -/
theorem branch_nonempty (a : ℕ → Bool) :
    (⋂ n, (T.cell (PiNat.res a n)).carrier).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  · intro n
    rw [PiNat.res_succ]
    exact T.child_subset _ _
  · intro n
    exact (T.cell _).nonempty
  · exact (T.cell _).clopen.isClosed.isCompact
  · intro n
    exact (T.cell _).clopen.isClosed

private def branchPoint (a : ℕ → Bool) : Y := (T.branch_nonempty a).some

private theorem branchPoint_mem (a : ℕ → Bool) (n : ℕ) :
    T.branchPoint a ∈ (T.cell (PiNat.res a n)).carrier :=
  mem_iInter.mp (T.branch_nonempty a).some_mem n

/-- Deciding every basis set makes a branch intersection a singleton. -/
theorem branch_unique [T2Space Y] (hB : IsTopologicalBasis (range B))
    (a : ℕ → Bool) {x y : Y}
    (hx : ∀ n, x ∈ (T.cell (PiNat.res a n)).carrier)
    (hy : ∀ n, y ∈ (T.cell (PiNat.res a n)).carrier) : x = y := by
  by_contra hxy
  obtain ⟨U, ⟨n, rfl⟩, hxU, hU⟩ := hB.exists_subset_of_mem_open
    (show x ∈ ({y} : Set Y)ᶜ from hxy) isClosed_singleton.isOpen_compl
  have hdec := T.decides (PiNat.res a n) (a n)
  rw [PiNat.res_length] at hdec
  have hx' := hx (n + 1)
  have hy' := hy (n + 1)
  rw [PiNat.res_succ] at hx' hy'
  rcases hdec with h | h
  · exact hU (h hy') (mem_singleton y)
  · exact h hx' hxU

private theorem branchPoint_injective : Function.Injective T.branchPoint := by
  intro a b hab
  apply PiNat.res_injective
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [PiNat.res_succ, PiNat.res_succ]
    congr 1
    by_contra hne
    have ha := T.branchPoint_mem a (n + 1)
    have hb := T.branchPoint_mem b (n + 1)
    rw [PiNat.res_succ] at ha hb
    rw [← ih, ← hab] at hb
    cases hna : a n <;> cases hnb : b n <;> simp_all
    · exact disjoint_left.mp (T.child_disjoint _) ha hb
    · exact disjoint_left.mp (T.child_disjoint _) hb ha

/-- An address is obtained by following the unique child containing a point. -/
private def addressPrefix (x : Y) : ℕ → List Bool
  | 0 => []
  | n + 1 =>
      (decide (x ∈ (T.cell (true :: addressPrefix x n)).carrier)) :: addressPrefix x n

private theorem addressPrefix_mem (x : Y) (n : ℕ) :
    x ∈ (T.cell (T.addressPrefix x n)).carrier := by
  classical
  induction n with
  | zero => simp only [addressPrefix, T.root, mem_univ]
  | succ n ih =>
    simp only [addressPrefix]
    by_cases h : x ∈ (T.cell (true :: T.addressPrefix x n)).carrier
    · simp [h]
    · have hm : x ∈ (T.cell (false :: T.addressPrefix x n)).carrier ∪
          (T.cell (true :: T.addressPrefix x n)).carrier := by
        rw [T.child_union]
        exact ih
      simpa [h] using hm.resolve_right h

private def address (x : Y) (n : ℕ) : Bool :=
  decide (x ∈ (T.cell (true :: T.addressPrefix x n)).carrier)

private theorem res_address (x : Y) (n : ℕ) :
    PiNat.res (T.address x) n = T.addressPrefix x n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [PiNat.res_succ, address, ih, addressPrefix]

private theorem branchPoint_surjective [T2Space Y] (hB : IsTopologicalBasis (range B)) :
    Function.Surjective T.branchPoint := by
  intro x
  refine ⟨T.address x, T.branch_unique hB (T.address x) (T.branchPoint_mem _) ?_⟩
  intro n
  rw [T.res_address]
  exact T.addressPrefix_mem x n

private theorem branchPoint_continuous (hB : IsTopologicalBasis (range B)) :
    Continuous T.branchPoint := by
  rw [continuous_def]
  intro O hO
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  obtain ⟨U, ⟨n, rfl⟩, hmem, hsub⟩ := hB.exists_subset_of_mem_open ha hO
  have hcell : (T.cell (PiNat.res a (n + 1))).carrier ⊆ B n := by
    have hdec := T.decides (PiNat.res a n) (a n)
    rw [PiNat.res_length] at hdec
    rw [PiNat.res_succ]
    rcases hdec with h | h
    · exact h
    · have hm := T.branchPoint_mem a (n + 1)
      rw [PiNat.res_succ] at hm
      exact False.elim (h hm hmem)
  apply Filter.mem_of_superset ((PiNat.isOpen_cylinder (fun _ => Bool) a (n + 1)).mem_nhds
    (PiNat.self_mem_cylinder a (n + 1)))
  intro b hb
  apply hsub
  apply hcell
  rw [PiNat.cylinder_eq_res] at hb
  rw [← hb]
  exact T.branchPoint_mem b (n + 1)

include T

/-- The continuous bijection has a continuous inverse by compactness and
Hausdorffness; hence the output includes the full topology. -/
theorem homeomorph_of_binaryPartition [T2Space Y] (hB : IsTopologicalBasis (range B)) :
    Nonempty (Y ≃ₜ (ℕ → Bool)) := by
  let e : (ℕ → Bool) ≃ Y := Equiv.ofBijective T.branchPoint
    ⟨T.branchPoint_injective, T.branchPoint_surjective hB⟩
  exact ⟨(Continuous.homeoOfEquivCompactToT2 (f := e) (T.branchPoint_continuous hB)).symm⟩

end Branches
end BinaryPartition
end CantorCharacterization

/-- Cantor characterization for the source's canonical clopen-basis predicate.
A compatible metric is chosen only internally; the conclusion uses the original
topology and the positive-integer-indexed product from `CantorModel`. -/
theorem cantor_characterization (X : Type u) [TopologicalSpace X] [Nonempty X]
    [CompactSpace X] [MetrizableSpace X] (hz : Ch06.ZeroDimensional X)
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X)) : Nonempty (X ≃ₜ CantorSpace) := by
  letI : MetricSpace X := metrizableSpaceMetric X
  letI : ZeroDimensionalSpace X := (Ch06.zeroDimensional_iff_mathlib X).mp hz
  have hbase : IsTopologicalBasis {U : Set X | IsClopen U} := isTopologicalBasis_isClopen
  obtain ⟨S, hS, hcount, hb⟩ := hbase.exists_countable
  have hne : S.Nonempty := by
    obtain ⟨U, hU, _, _⟩ := hb.exists_subset_of_mem_open
      (mem_univ (Classical.choice (inferInstance : Nonempty X))) isOpen_univ
    exact ⟨U, hU⟩
  obtain ⟨B, hB⟩ := hcount.exists_eq_range hne
  have hbB : IsTopologicalBasis (range B) := hB ▸ hb
  have hclopen (n : ℕ) : IsClopen (B n) := hS (hB.symm ▸ mem_range_self n)
  obtain ⟨T⟩ := CantorCharacterization.exists_binaryPartition hz hno B hclopen
  obtain ⟨e⟩ := T.homeomorph_of_binaryPartition hbB
  exact ⟨e.trans positiveReindex.symm⟩

/-- Under compact metrizability the two separation predicates in the statement
are equivalent, with no hidden nonemptiness or perfectness premise. -/
theorem cantor_characterization_hypotheses (X : Type u) [TopologicalSpace X]
    [CompactSpace X] [MetrizableSpace X] :
    Ch06.ZeroDimensional X ↔ Ch06.TotallyDisconnected X :=
  (Ch06.compact_t2_totallyDisconnected_iff_zeroDimensional X).symm

/-- The equivalent totally disconnected version, retaining nonemptiness and
absence of isolated points and producing an actual homeomorphism. -/
theorem cantor_characterization_totallyDisconnected (X : Type u) [TopologicalSpace X]
    [Nonempty X] [CompactSpace X] [MetrizableSpace X]
    (ht : Ch06.TotallyDisconnected X) (hno : ∀ x : X, ¬ IsOpen ({x} : Set X)) :
    Nonempty (X ≃ₜ CantorSpace) :=
  cantor_characterization X ((cantor_characterization_hypotheses X).mpr ht) hno

end D10Topology.Ch18
