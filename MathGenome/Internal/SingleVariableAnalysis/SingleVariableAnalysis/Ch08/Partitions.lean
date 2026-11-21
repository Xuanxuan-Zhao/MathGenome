import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Partitions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite strict partitions, closed-cell tags and tagged sums for
`K03.08.partitions`. Refinements insert points; union supplies a common
refinement. Uniform partitions give arbitrarily small positive meshes.
The singleton interval uses no cells, mesh zero and the empty sum. -/

namespace SingleVariableAnalysis.Riemann
open scoped BigOperators
namespace S
export Specs.SingleVariableAnalysis.Ch08.Partitions
  (pointsValue lengthValue meshValue taggingValue sumValue refinesValue)
end S

abbrev Partition := PartitionData
noncomputable abbrev points := @S.pointsValue
abbrev cellLength := @S.lengthValue
noncomputable abbrev mesh := @S.meshValue
abbrev Tagging := @S.taggingValue
noncomputable abbrev taggedSum := @S.sumValue
abbrev Refines := @S.refinesValue

theorem endpoints : Specs.SingleVariableAnalysis.Ch08.Partitions.endpoints := by
  intro a b P
  have hmem (i : Fin (P.n+1)) : P.point i ∈ points P := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  refine ⟨by simpa only [P.first] using hmem 0, by simpa only [P.last] using hmem (Fin.last P.n), ?_⟩
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨by simpa only [P.first] using P.strictMono.monotone (Fin.zero_le i),
    by simpa only [P.last] using P.strictMono.monotone (Fin.le_last i)⟩

theorem cell_positive : Specs.SingleVariableAnalysis.Ch08.Partitions.cellPositive := by
  intro a b P i
  exact sub_pos.mpr (P.strictMono (Fin.castSucc_lt_succ (i := i)))

theorem tags_exist : Specs.SingleVariableAnalysis.Ch08.Partitions.tagsExist := by
  intro a b P
  exact ⟨fun i => ⟨P.point i.castSucc, le_rfl, le_of_lt (P.strictMono (Fin.castSucc_lt_succ (i := i)))⟩⟩

theorem refinement_laws : Specs.SingleVariableAnalysis.Ch08.Partitions.refinementLaws := by
  intro a b P Q R
  exact ⟨Finset.Subset.refl _, fun hRQ hQP => Finset.Subset.trans hQP hRQ⟩

/-- Sort any finite endpoint set, retaining exactly its points. -/
noncomputable def ofPoints {a b : ℝ} (s : Finset ℝ) (ha : a ∈ s) (hb : b ∈ s)
    (hbound : ∀ x ∈ s, x ∈ Set.Icc a b) : Partition a b := by
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hc : s.card = (s.card - 1) + 1 := by omega
  let e := s.orderEmbOfFin hc
  refine ⟨s.card - 1, e, e.strictMono, ?_, ?_⟩
  · apply le_antisymm
    · obtain ⟨j, hj⟩ := (show a ∈ Set.range (s.orderEmbOfFin hc) by rw [s.range_orderEmbOfFin hc]; exact ha)
      rw [← hj]
      exact e.monotone (Fin.zero_le j)
    · exact (hbound _ (s.orderEmbOfFin_mem hc 0)).1
  · apply le_antisymm
    · exact (hbound _ (s.orderEmbOfFin_mem hc (Fin.last _))).2
    · obtain ⟨j, hj⟩ := (show b ∈ Set.range (s.orderEmbOfFin hc) by rw [s.range_orderEmbOfFin hc]; exact hb)
      rw [← hj]
      exact e.monotone (Fin.le_last j)

theorem points_ofPoints {a b : ℝ} (s : Finset ℝ) (ha : a ∈ s) (hb : b ∈ s)
    (hbound : ∀ x ∈ s, x ∈ Set.Icc a b) :
    points (ofPoints s ha hb hbound) = s := by
  exact s.image_orderEmbOfFin_univ _

theorem finite_representation : Specs.SingleVariableAnalysis.Ch08.Partitions.finiteRepresentation := by
  intro a b s ha hb hbound
  exact ⟨ofPoints s ha hb hbound, points_ofPoints s ha hb hbound⟩

/-- The common refinement is obtained by union, followed by increasing enumeration. -/
noncomputable def commonRefinement {a b : ℝ} (P Q : Partition a b) : Partition a b :=
  ofPoints (points P ∪ points Q)
    (Finset.mem_union_left _ (endpoints P).1)
    (Finset.mem_union_left _ (endpoints P).2.1)
    (by intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact (endpoints P).2.2 x hx
        · exact (endpoints Q).2.2 x hx)

theorem common_refinement : Specs.SingleVariableAnalysis.Ch08.Partitions.commonRefinement := by
  intro a b P Q
  have hp : points (commonRefinement P Q) = points P ∪ points Q := points_ofPoints _ _ _ _
  refine ⟨commonRefinement P Q, hp, ?_, ?_⟩
  · change points P ⊆ points (commonRefinement P Q)
    rw [hp]
    exact Finset.subset_union_left
  · change points Q ⊆ points (commonRefinement P Q)
    rw [hp]
    exact Finset.subset_union_right

theorem mesh_nonneg {a b : ℝ} (P : Partition a b) : 0 ≤ mesh P :=
  Finset.le_sup' id (Finset.mem_insert_self _ _)

theorem cellLength_le_mesh {a b : ℝ} (P : Partition a b) (i : Fin P.n) :
    cellLength P i ≤ mesh P :=
  Finset.le_sup' (s := insert (0 : ℝ) (Finset.univ.image (cellLength P))) id
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

theorem mesh_le {a b c : ℝ} (P : Partition a b) (hc : 0 ≤ c)
    (hi : ∀ i, cellLength P i ≤ c) : mesh P ≤ c := by
  apply Finset.sup'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hc
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hi i

/-- A nondegenerate interval has the explicit equally spaced partition. -/
noncomputable def uniformPartition {a b : ℝ} (hab : a < b) (n : ℕ) (hn : 0 < n) :
    Partition a b where
  n := n
  point i := a + (i.val : ℝ) * (b-a) / n
  strictMono := by
    intro i j hij
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hijR : (i.val : ℝ) < j.val := Nat.cast_lt.mpr hij
    have h := div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_right hijR (sub_pos.mpr hab)) hnR
    dsimp
    linarith
  first := by simp
  last := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    simp only [Fin.val_last]
    field_simp
    ring

theorem uniform_cellLength {a b : ℝ} (hab : a < b) (n : ℕ) (hn : 0 < n)
    (i : Fin n) : cellLength (uniformPartition hab n hn) i = (b-a)/n := by
  change (a + ((i.val+1 : ℕ) : ℝ) * (b-a) / n) -
    (a + (i.val : ℝ) * (b-a) / n) = (b-a)/n
  push_cast
  ring

theorem uniform_mesh {a b : ℝ} (hab : a < b) (n : ℕ) (hn : 0 < n) :
    mesh (uniformPartition hab n hn) = (b-a)/n := by
  apply le_antisymm
  · exact mesh_le _ (le_of_lt (div_pos (sub_pos.mpr hab) (Nat.cast_pos.mpr hn)))
      (fun i => (uniform_cellLength hab n hn i).le)
  · rw [← uniform_cellLength hab n hn ⟨0,hn⟩]
    exact cellLength_le_mesh _ _

theorem uniform_partitions : Specs.SingleVariableAnalysis.Ch08.Partitions.uniformPartitions := by
  intro a b hab n hn
  exact ⟨uniformPartition hab n hn, rfl, (fun _ => rfl), uniform_mesh hab n hn⟩

theorem mesh_maximum : Specs.SingleVariableAnalysis.Ch08.Partitions.meshMaximum := by
  intro a b P
  refine ⟨mesh_nonneg P, cellLength_le_mesh P, ?_⟩
  intro hn
  let i₀ : Fin P.n := ⟨0, Nat.pos_of_ne_zero hn⟩
  have hpos : 0 < mesh P := lt_of_lt_of_le (cell_positive P i₀) (cellLength_le_mesh P i₀)
  obtain ⟨x, hx, heq⟩ := Finset.exists_mem_eq_sup'
    (s := insert 0 (Finset.univ.image (cellLength P))) ⟨0, Finset.mem_insert_self _ _⟩ id
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact False.elim (ne_of_gt hpos heq)
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i, heq⟩

theorem arbitrarily_fine : Specs.SingleVariableAnalysis.Ch08.Partitions.arbitrarilyFine := by
  intro a b hab ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt ((b-a)/ε)
  have hnR : (0 : ℝ) < n := lt_trans (div_pos (sub_pos.mpr hab) hε) hn
  have hnN : 0 < n := Nat.cast_pos.mp hnR
  refine ⟨uniformPartition hab n hnN, ?_, ?_⟩
  · change 0 < mesh (uniformPartition hab n hnN)
    rw [uniform_mesh]
    exact div_pos (sub_pos.mpr hab) hnR
  · change mesh (uniformPartition hab n hnN) < ε
    rw [uniform_mesh]
    apply (div_lt_iff₀ hnR).mpr
    have h := (div_lt_iff₀ hε).mp hn
    nlinarith

/-- The unique endpoint list on a singleton has no cells. -/
def emptyPartition (a : ℝ) : Partition a a where
  n := 0
  point _ := a
  strictMono := by
    intro i j hij
    have h : i.val < j.val := hij
    have hi := i.isLt
    have hj := j.isLt
    omega
  first := rfl
  last := rfl

theorem n_eq_zero_of_degenerate (a : ℝ) (P : Partition a a) : P.n = 0 := by
  by_contra hn
  have hi : (0 : Fin (P.n+1)) < Fin.last P.n := by
    change 0 < P.n
    exact Nat.pos_of_ne_zero hn
  have h := P.strictMono hi
  rw [P.first, P.last] at h
  exact lt_irrefl _ h

theorem mesh_eq_zero_of_n_eq_zero {a b : ℝ} (P : Partition a b) (hn : P.n = 0) :
    mesh P = 0 := by
  have : IsEmpty (Fin P.n) := Fin.isEmpty_iff.mpr hn
  simp [mesh, S.meshValue]

theorem degenerate_all : Specs.SingleVariableAnalysis.Ch08.Partitions.degenerateAll := by
  intro a P
  exact ⟨n_eq_zero_of_degenerate a P, mesh_eq_zero_of_n_eq_zero P (n_eq_zero_of_degenerate a P)⟩

theorem degenerate : Specs.SingleVariableAnalysis.Ch08.Partitions.degenerate := by
  intro a
  exact ⟨emptyPartition a, rfl, mesh_eq_zero_of_n_eq_zero _ rfl, tags_exist _⟩

theorem degenerate_sum : Specs.SingleVariableAnalysis.Ch08.Partitions.degenerateSum := by
  intro E _ _ a P ξ f
  have : IsEmpty (Fin P.n) := Fin.isEmpty_iff.mpr (n_eq_zero_of_degenerate a P)
  simp [S.sumValue]

end SingleVariableAnalysis.Riemann
