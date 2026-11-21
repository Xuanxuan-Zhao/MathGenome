import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Trees.MatrixTree
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Trees.IncidenceMinors
import MathGenome.Internal.D05.M15.DeterminantLine.CauchyBinet

universe u v w
noncomputable section
namespace FiniteCombinatorics.Graph.Trees
open scoped Matrix
attribute [local instance] Classical.propDecidable

abbrev spanningTrees : Specs.FiniteCombinatorics.Graph.Trees.MatrixTree.spanningTreesType :=
  Specs.FiniteCombinatorics.Graph.Trees.MatrixTree.spanningTreesValue

theorem mem_spanningTrees : Specs.FiniteCombinatorics.Graph.Trees.MatrixTree.mem_spanningTreesType := by
  intro V G _ S
  classical
  simp [Specs.FiniteCombinatorics.Graph.Trees.MatrixTree.spanningTreesValue]

/-- Weighted Cauchy–Binet on finite ordinal indices, using the checked
field-valued theorem and its bridge to Mathlib's determinant. -/
lemma weighted_cauchy_binet {K : Type v} [Field K] {n k : ℕ}
    (A : Matrix (Fin k) (Fin n) K) (w : Fin n → K) :
    (A * Matrix.diagonal w * A.transpose).det =
      ∑ S : Set.powersetCard (Fin n) k,
        (A.submatrix id (S.val.orderEmbOfFin S.prop)).det ^ 2 *
          ∏ e ∈ S.val, w e := by
  classical
  have h := D05.M15.DeterminantLine.CauchyBinet.det_rectangular_product
    A (Matrix.diagonal w * A.transpose)
  simp only [Specs.D05.M15.DeterminantLine.CauchyBinet.rowMinor] at h
  have bridge : ∀ M : Matrix (Fin k) (Fin k) K, D05.M05.determinant M = M.det :=
    fun M => D05.M05.DetDefinition.matrix_det_bridge M
  simp_rw [bridge] at h
  rw [Matrix.mul_assoc, h]
  apply Finset.sum_congr rfl
  intro S _
  have hm : ((Matrix.diagonal w * A.transpose).submatrix
      (S.val.orderEmbOfFin S.prop) id) =
      Matrix.diagonal (fun i => w (S.val.orderEmbOfFin S.prop i)) *
        (A.submatrix id (S.val.orderEmbOfFin S.prop)).transpose := by
    ext i j
    simp [Matrix.diagonal_mul]
  rw [hm, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
  have hp : (∏ i : Fin k, w (S.val.orderEmbOfFin S.prop i)) = ∏ e ∈ S.val, w e := by
    exact ((S.val.orderIsoOfFin S.prop).toEquiv.prod_comp (fun e : S.val => w e)).trans
      (Finset.prod_coe_sort S.val w)
  rw [hp]
  ring

/-- Transport combinations along an enumeration, without losing or duplicating subsets. -/
def combinationsEquiv {α : Type u} {β : Type w} (e : α ≃ β) (k : ℕ) :
    Set.powersetCard α k ≃ Set.powersetCard β k :=
  e.finsetCongr.subtypeEquiv (fun s => by
    simp [Equiv.finsetCongr_apply, Set.powersetCard])

lemma selectedGraph_le {V : Type u} (G : SimpleGraph V) (S : Finset G.edgeSet) :
    selectedGraph G S ≤ G := by
  intro x y hxy
  obtain ⟨e, _, he⟩ := (selectedGraph_adj G S x y).mp hxy
  have h := e.property
  rwa [he] at h

lemma selectedGraph_injective {V : Type u} (G : SimpleGraph V) :
    Function.Injective (selectedGraph G) := by
  intro S T h
  have he := congrArg SimpleGraph.edgeSet h
  rw [selectedGraph_edgeSet, selectedGraph_edgeSet] at he
  exact Finset.coe_injective (Subtype.val_injective.image_injective he)

/-- All spanning tree graphs occur exactly once in the sum. -/
theorem spanning_tree_selections :
    Specs.FiniteCombinatorics.Graph.Trees.MatrixTree.spanning_tree_selectionsType := by
  intro V _ G _ T hle ht
  classical
  let S := Finset.univ.filter (fun e : G.edgeSet => e.val ∈ T.edgeSet)
  have hsel : selectedGraph G S = T := by
    apply SimpleGraph.edgeSet_injective
    rw [selectedGraph_edgeSet]
    ext e
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (Finset.mem_filter.mp ha).2
    · intro he
      exact ⟨⟨e, SimpleGraph.edgeSet_mono hle he⟩, by simp [S, he], rfl⟩
  refine ⟨S, ⟨(mem_spanningTrees G S).mpr (by change (selectedGraph G S).IsTree; rwa [hsel]), hsel⟩, ?_⟩
  intro S' hS'
  exact selectedGraph_injective G (hS'.2.trans hsel.symm)

lemma tree_selection_card {V : Type u} [Fintype V] (G : SimpleGraph V)
    (r : V) (S : Finset G.edgeSet) (h : (selectedGraph G S).IsTree) :
    S.card = Fintype.card {x : V // x ≠ r} := by
  have : Nonempty V := ⟨r⟩
  have hc := ((tree_iff_edge_count (selectedGraph G S)).mp h).2
  rw [selectedGraph_card, Nat.card_eq_fintype_card] at hc
  rw [Fintype.card_subtype_compl (fun x : V => x = r),
    Fintype.card_unique (α := {x : V // x = r})]
  exact hc

/-- Cauchy–Binet with the incidence-minor classification, before discarding
zero coefficients. -/
lemma weighted_tree_expansion {V : Type u} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (K : Type v) [Field K] (o : EdgeOrientation G)
    (w : G.edgeSet → K) (r : V) :
    (principalMinor (weightedLaplacian G K w) r).det =
      ∑ S : Set.powersetCard G.edgeSet (Fintype.card {x : V // x ≠ r}),
        if (selectedGraph G S.val).IsTree then ∏ e ∈ S.val, w e else 0 := by
  classical
  let I := {x : V // x ≠ r}
  let k := Fintype.card I
  let n := Fintype.card G.edgeSet
  let a : Fin k ≃ I := (Fintype.equivFin I).symm
  let b : Fin n ≃ G.edgeSet := (Fintype.equivFin G.edgeSet).symm
  let D := reducedIncidence G K o r
  let A := D.submatrix a b
  have hL : (principalMinor (weightedLaplacian G K w) r).det =
      (A * Matrix.diagonal (fun i => w (b i)) * A.transpose).det := by
    have hf : principalMinor (weightedLaplacian G K w) r =
        D * Matrix.diagonal w * D.transpose := reduced_factorization G K o w r
    rw [hf]
    rw [← Matrix.det_submatrix_equiv_self a]
    congr 1
    ext i j
    simpa [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.diagonal, A]
      using (b.sum_comp (fun e => D (a i) e * w e * D (a j) e)).symm
  rw [hL, weighted_cauchy_binet]
  let c := combinationsEquiv b k
  rw [← c.sum_comp]
  apply Finset.sum_congr rfl
  intro S _
  let T : Finset G.edgeSet := S.val.map b.toEmbedding
  have hT : T.card = Fintype.card V - 1 := by
    calc
      T.card = k := (Finset.card_map _).trans S.prop
      _ = Fintype.card V - 1 := by
        dsimp [k, I]
        rw [Fintype.card_subtype_compl (fun x : V => x = r),
          Fintype.card_unique (α := {x : V // x = r})]
  let q : Fin k ≃ T := (S.val.orderIsoOfFin S.prop).toEquiv.trans
    (Finset.equivMap b.toEmbedding S.val)
  let e : I ≃ T := a.symm.trans q
  have hm : A.submatrix id (S.val.orderEmbOfFin S.prop) =
      (incidenceMinor G K o r T e).submatrix a a := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, incidenceMinor_apply, e,
      Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  have hd : (A.submatrix id (S.val.orderEmbOfFin S.prop)).det ^ 2 =
      if (selectedGraph G T).IsTree then 1 else 0 := by
    rw [hm, Matrix.det_submatrix_equiv_self]
    exact minor_det_sq G K o r T e hT
  have hp : (∏ i ∈ S.val, w (b i)) = ∏ i ∈ T, w i :=
    (Finset.prod_map S.val b.toEmbedding w).symm
  rw [hd, hp]
  change (if (selectedGraph G T).IsTree then (1 : K) else 0) * (∏ i ∈ T, w i) =
    if (selectedGraph G T).IsTree then ∏ i ∈ T, w i else 0
  split_ifs <;> simp

/-- W42: the weighted matrix–tree identity, over an arbitrary field. -/
theorem weighted_matrix_tree :
    Specs.FiniteCombinatorics.Graph.Trees.MatrixTree.weighted_matrix_treeType := by
  intro V _ G _ K _ w r
  classical
  obtain ⟨o⟩ := orientation_exists G
  change (principalMinor (weightedLaplacian G K w) r).det = _
  rw [weighted_tree_expansion G K o w r]
  let k := Fintype.card {x : V // x ≠ r}
  let f : Finset G.edgeSet → K := fun S =>
    if (selectedGraph G S).IsTree then ∏ e ∈ S, w e else 0
  have hs : (∑ S : Set.powersetCard G.edgeSet k, f S.val) =
      ∑ S ∈ Finset.univ.powersetCard k, f S := by
    symm
    apply Finset.sum_subtype
    intro S
    simp [Set.powersetCard]
  change (∑ S : Set.powersetCard G.edgeSet k, f S.val) = _
  rw [hs]
  change (∑ S ∈ Finset.univ.powersetCard k,
    if (selectedGraph G S).IsTree then ∏ e ∈ S, w e else 0) = _
  rw [← Finset.sum_filter]
  have hsets : (Finset.univ.powersetCard k).filter
      (fun S : Finset G.edgeSet => (selectedGraph G S).IsTree) = spanningTrees G := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
      true_and]
    exact ⟨fun h => (mem_spanningTrees G S).mpr h.2, fun h => by
      have ht := (mem_spanningTrees G S).mp h
      exact ⟨tree_selection_card G r S ht, ht⟩⟩
  rw [hsets]

/-- With rational unit weights, the sum is the natural number of spanning trees. -/
theorem matrix_tree_count :
    Specs.FiniteCombinatorics.Graph.Trees.MatrixTree.matrix_tree_countType := by
  intro V _ G _ r
  classical
  rw [weighted_matrix_tree G ℚ (fun _ => 1) r]
  simp

/-- A disconnected graph has no spanning tree, so every weighted cofactor vanishes. -/
theorem disconnected_minor :
    Specs.FiniteCombinatorics.Graph.Trees.MatrixTree.disconnected_minorType := by
  intro V _ G _ K _ w r hG
  classical
  rw [weighted_matrix_tree G K w r]
  apply Finset.sum_eq_zero
  intro S hS
  have ht := (mem_spanningTrees G S).mp hS
  exact (hG (ht.connected.mono (selectedGraph_le G S))).elim

/-- The single-vertex cofactor is the empty determinant. -/
theorem singleton_minor :
    Specs.FiniteCombinatorics.Graph.Trees.MatrixTree.singleton_minorType := by
  intro V _ _ G _ K _ w r
  classical
  have : IsEmpty {x : V // x ≠ r} :=
    ⟨fun x => x.property (Subsingleton.elim _ _)⟩
  exact Matrix.det_isEmpty

end FiniteCombinatorics.Graph.Trees
