import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Trees.Incidence
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Trees.Characterizations
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The signed incidence-minor classification in W42.

We use the elementary total unimodularity argument: an incidence submatrix
column either has zero sum or has just one nonzero entry ±1. Expansion in such
a column gives induction; if every column has zero sum, the all-one row vector
annihilates the matrix. This argument is valid in every characteristic.

For a square reduced minor, a left-kernel vector extends to the omitted vertex
by zero. Its product with an edge column is the difference of the endpoint
values. Connectivity makes all these values equal to zero, proving
nonsingularity. Conversely the indicator of a component disjoint from the root
is a nonzero left-kernel vector. The tree edge-count characterization then
finishes the classification for n-1 selected edges.
-/

universe u v w
noncomputable section
namespace FiniteCombinatorics.Graph.Trees
attribute [local instance] Classical.propDecidable
open scoped Matrix

abbrev selectedGraph : Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors.selectedGraphType :=
  Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors.selectedGraphValue

abbrev incidenceMinor : Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors.incidenceMinorType :=
  Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors.incidenceMinorValue

lemma incidence_eq_sub {V : Type u} (G : SimpleGraph V) (K : Type v) [Field K]
    (o : EdgeOrientation G) (x : V) (a : G.edgeSet) :
    incidence G K o x a =
      (if x = o.head a then 1 else 0) - (if x = o.tail a then 1 else 0) := by
  classical
  have hn := (orientation_endpoints G o a).2.1
  dsimp [incidence, Specs.FiniteCombinatorics.Graph.Trees.Incidence.incidenceValue]
  split_ifs <;> simp_all

lemma incidence_column_cases {V : Type u} (G : SimpleGraph V) (K : Type v) [Field K]
    (o : EdgeOrientation G) {I : Type w} [Fintype I] (f : I → V)
    (hf : Function.Injective f) (a : G.edgeSet) :
    (∑ i, incidence G K o (f i) a) = 0 ∨
      ∃ i, (incidence G K o (f i) a = 1 ∨ incidence G K o (f i) a = -1) ∧
        ∀ j, j ≠ i → incidence G K o (f j) a = 0 := by
  classical
  have hn := (orientation_endpoints G o a).2.1
  by_cases hh : ∃ i, f i = o.head a
  · obtain ⟨i, hi⟩ := hh
    have hih : ∀ j, f j = o.head a ↔ j = i := fun j => by rw [← hi, hf.eq_iff]
    by_cases ht : ∃ j, f j = o.tail a
    · obtain ⟨j, hj⟩ := ht
      have hjt : ∀ k, f k = o.tail a ↔ k = j := fun k => by rw [← hj, hf.eq_iff]
      left
      simp_rw [incidence_eq_sub, Finset.sum_sub_distrib, hih, hjt]
      simp
    · right
      refine ⟨i, Or.inl ?_, ?_⟩
      · rw [incidence_eq_sub]
        simp [hi, Ne.symm hn]
      · intro j hji
        rw [incidence_eq_sub]
        simp [hih j, hji, show f j ≠ o.tail a from fun h => ht ⟨j, h⟩]
  · by_cases ht : ∃ j, f j = o.tail a
    · obtain ⟨j, hj⟩ := ht
      have hjt : ∀ k, f k = o.tail a ↔ k = j := fun k => by rw [← hj, hf.eq_iff]
      right
      refine ⟨j, Or.inr ?_, ?_⟩
      · rw [incidence_eq_sub]
        simp [hj, hn]
      · intro k hkj
        rw [incidence_eq_sub]
        simp [hjt k, hkj, show f k ≠ o.head a from fun h => hh ⟨k, h⟩]
    · left
      apply Finset.sum_eq_zero
      intro i _
      rw [incidence_eq_sub]
      simp [show f i ≠ o.head a from fun h => hh ⟨i,h⟩,
        show f i ≠ o.tail a from fun h => ht ⟨i,h⟩]

lemma incidence_totallyUnimodular {V : Type u} (G : SimpleGraph V) (K : Type v) [Field K]
    (o : EdgeOrientation G) : (incidence G K o).IsTotallyUnimodular := by
  classical
  intro k
  induction k with
  | zero => intro f g hf hg; exact ⟨1, by simp⟩
  | succ k ih =>
    intro f g hf hg
    by_cases h : ∃ j i, (incidence G K o (f i) (g j) = 1 ∨
        incidence G K o (f i) (g j) = -1) ∧
        ∀ i', i' ≠ i → incidence G K o (f i') (g j) = 0
    · obtain ⟨j, i, hv, hz⟩ := h
      rw [Matrix.det_succ_column _ j, Fintype.sum_eq_single i]
      · change _ ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
        apply mul_mem
        · apply mul_mem
          · apply pow_mem
            exact ⟨-1, by simp⟩
          · rcases hv with hv | hv
            · exact ⟨1, by simpa using hv.symm⟩
            · exact ⟨-1, by simpa using hv.symm⟩
        · exact ih (f ∘ i.succAbove) (g ∘ j.succAbove)
            (hf.comp Fin.succAbove_right_injective) (hg.comp Fin.succAbove_right_injective)
      · intro i' hne
        simp [Matrix.submatrix_apply, hz i' hne]
    · have hs : ∀ j, ∑ i, incidence G K o (f i) (g j) = 0 := by
        intro j
        rcases incidence_column_cases G K o f hf (g j) with hs | ⟨i, hv, hz⟩
        · exact hs
        · exact (h ⟨j, i, hv, hz⟩).elim
      have hd : ((incidence G K o).submatrix f g).det = 0 := by
        apply Matrix.exists_vecMul_eq_zero_iff.mp
        refine ⟨fun _ => 1, ?_, ?_⟩
        · intro he
          have := congrFun he 0
          exact one_ne_zero this
        · ext j
          simpa [Matrix.vecMul, dotProduct, Matrix.submatrix_apply] using hs j
      exact ⟨0, by simpa using hd.symm⟩

lemma selectedGraph_edgeSet {V : Type u} (G : SimpleGraph V) (S : Finset G.edgeSet) :
    (selectedGraph G S).edgeSet = Subtype.val '' (S : Set G.edgeSet) := by
  rw [selectedGraph, Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors.selectedGraphValue,
    SimpleGraph.edgeSet_fromEdgeSet]
  ext a
  constructor
  · exact fun h => h.1
  · intro h
    obtain ⟨b, hb, rfl⟩ := h
    exact ⟨⟨b, hb, rfl⟩, G.edgeSet_subset_compl_diagSet b.property⟩

lemma selectedGraph_adj {V : Type u} (G : SimpleGraph V) (S : Finset G.edgeSet) (x y : V) :
    (selectedGraph G S).Adj x y ↔ ∃ a : G.edgeSet, a ∈ S ∧ a.val = s(x,y) := by
  change s(x,y) ∈ (selectedGraph G S).edgeSet ↔ _
  rw [selectedGraph_edgeSet]
  rfl

lemma selectedGraph_card {V : Type u} (G : SimpleGraph V) (S : Finset G.edgeSet) :
    Nat.card (selectedGraph G S).edgeSet = S.card := by
  rw [selectedGraph_edgeSet]
  have e := Equiv.Set.image Subtype.val (S : Set G.edgeSet) Subtype.val_injective
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  exact Fintype.card_coe S

lemma minor_index_equiv :
    Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors.minor_index_equivType := by
  intro V _ G r S hs
  classical
  refine ⟨Fintype.equivOfCardEq ?_⟩
  rw [Fintype.card_subtype_compl (fun x : V => x = r), Fintype.card_unique (α := {x : V // x = r}),
    Fintype.card_coe]
  exact hs.symm

lemma incidenceMinor_apply {V : Type u} (G : SimpleGraph V) (K : Type v) [Field K]
    (o : EdgeOrientation G) (r : V) (S : Finset G.edgeSet)
    (e : {x : V // x ≠ r} ≃ {a : G.edgeSet // a ∈ S}) (i j : {x : V // x ≠ r}) :
    incidenceMinor G K o r S e i j = incidence G K o i.val (e j).val := rfl

lemma sum_mul_incidence {V : Type u} [Fintype V] (G : SimpleGraph V) (K : Type v) [Field K]
    (o : EdgeOrientation G) (c : V → K) (a : G.edgeSet) :
    ∑ x, c x * incidence G K o x a = c (o.head a) - c (o.tail a) := by
  classical
  simp_rw [incidence_eq_sub, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  simp

lemma vecMul_incidenceMinor {V : Type u} [Fintype V] (G : SimpleGraph V) (K : Type v) [Field K]
    (o : EdgeOrientation G) (r : V) (S : Finset G.edgeSet)
    (e : {x : V // x ≠ r} ≃ {a : G.edgeSet // a ∈ S})
    (c : V → K) (hr : c r = 0) (j : {x : V // x ≠ r}) :
    ((fun i : {x : V // x ≠ r} => c i.val) ᵥ* incidenceMinor G K o r S e) j =
      c (o.head (e j).val) - c (o.tail (e j).val) := by
  classical
  rw [← sum_mul_incidence G K o c (e j).val]
  change (∑ i : {x : V // x ≠ r}, c i.val * incidence G K o i.val (e j).val) = _
  have h := Fintype.sum_subtype_add_sum_subtype (fun x : V => x ≠ r)
    (fun x => c x * incidence G K o x (e j).val)
  have hz : (∑ i : {x : V // ¬x ≠ r}, c i.val * incidence G K o i.val (e j).val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : i.val = r := not_ne_iff.mp i.property
    simp [hi, hr]
  rwa [hz, add_zero] at h

lemma eq_on_reachable_of_eq_on_adj {V K : Type*} {H : SimpleGraph V} {c : V → K}
    (hc : ∀ x y, H.Adj x y → c x = c y) {x y : V} (hxy : H.Reachable x y) :
    c x = c y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => rfl
  | @cons x y z h p ih => exact (hc x y h).trans ih

lemma eq_on_adj_of_vecMul_minor_eq_zero {V : Type u} [Fintype V]
    (G : SimpleGraph V) (K : Type v) [Field K] (o : EdgeOrientation G)
    (r : V) (S : Finset G.edgeSet)
    (e : {x : V // x ≠ r} ≃ {a : G.edgeSet // a ∈ S})
    (c : V → K) (hr : c r = 0)
    (hz : (fun i : {x : V // x ≠ r} => c i.val) ᵥ* incidenceMinor G K o r S e = 0) :
    ∀ x y, (selectedGraph G S).Adj x y → c x = c y := by
  intro x y hxy
  obtain ⟨a, ha, he⟩ := (selectedGraph_adj G S x y).mp hxy
  have hz' := congrFun hz (e.symm ⟨a, ha⟩)
  rw [vecMul_incidenceMinor G K o r S e c hr] at hz'
  simp only [e.apply_symm_apply, Pi.zero_apply] at hz'
  have hc := sub_eq_zero.mp hz'
  have hp : s(o.tail a, o.head a) = s(x,y) := (o.edge_eq a).trans he
  rcases Sym2.eq_iff.mp hp with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · simpa only [ht, hh] using hc.symm
  · simpa only [ht, hh] using hc

lemma connected_minor_det_ne_zero {V : Type u} [Fintype V]
    (G : SimpleGraph V) (K : Type v) [Field K] (o : EdgeOrientation G)
    (r : V) (S : Finset G.edgeSet)
    (e : {x : V // x ≠ r} ≃ {a : G.edgeSet // a ∈ S})
    (hconn : (selectedGraph G S).Connected) :
    (incidenceMinor G K o r S e).det ≠ 0 := by
  classical
  intro hd
  obtain ⟨z, hzne, hz⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
  let c : V → K := fun x => if h : x = r then 0 else z ⟨x, h⟩
  have hr : c r = 0 := by simp [c]
  have hc : (fun i : {x : V // x ≠ r} => c i.val) = z := by
    funext i
    simp [c, i.property]
  have hadj := eq_on_adj_of_vecMul_minor_eq_zero G K o r S e c hr (by rwa [hc])
  apply hzne
  funext i
  have h := eq_on_reachable_of_eq_on_adj hadj (hconn r i.val)
  simpa [hr, c, i.property] using h.symm

lemma disconnected_minor_det_eq_zero {V : Type u} [Fintype V]
    (G : SimpleGraph V) (K : Type v) [Field K] (o : EdgeOrientation G)
    (r : V) (S : Finset G.edgeSet)
    (e : {x : V // x ≠ r} ≃ {a : G.edgeSet // a ∈ S})
    (hconn : ¬(selectedGraph G S).Connected) :
    (incidenceMinor G K o r S e).det = 0 := by
  classical
  have hn : ∃ x, ¬(selectedGraph G S).Reachable r x := by
    by_contra! h
    exact hconn ((SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨r, h⟩)
  obtain ⟨x, hx⟩ := hn
  have hxr : x ≠ r := by rintro rfl; exact hx .rfl
  let c : V → K := fun y => if (selectedGraph G S).Reachable r y then 0 else 1
  have hr : c r = 0 := by simp [c]
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨fun i => c i.val, ?_, ?_⟩
  · intro hz
    have hh := congrFun hz ⟨x, hxr⟩
    simp [c, hx] at hh
  · ext j
    rw [vecMul_incidenceMinor G K o r S e c hr]
    have ha := (e j).property
    have hs : (selectedGraph G S).Adj (o.tail (e j).val) (o.head (e j).val) := by
      apply (selectedGraph_adj G S _ _).mpr
      exact ⟨(e j).val, ha, (o.edge_eq _).symm⟩
    have hi : (selectedGraph G S).Reachable r (o.head (e j).val) ↔
        (selectedGraph G S).Reachable r (o.tail (e j).val) :=
      ⟨fun h => h.trans hs.symm.reachable, fun h => h.trans hs.reachable⟩
    simp only [c, hi, sub_self, Pi.zero_apply]

/-- W42: a spanning-tree minor has determinant ±1, over every field. -/
theorem tree_minor_det :
    Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors.tree_minor_detType := by
  intro V _ G K _ o r S e ht
  classical
  have hTU := ((Matrix.isTotallyUnimodular_iff_fintype (incidence G K o)).mp
    (incidence_totallyUnimodular G K o)) {x : V // x ≠ r}
      (fun i => i.val) (fun i => (e i).val)
  change (incidenceMinor G K o r S e).det ∈ Set.range SignType.cast at hTU
  have hn := connected_minor_det_ne_zero G K o r S e ht.connected
  obtain ⟨s, hs⟩ := hTU
  cases s <;> simp_all

/-- W42: a selection of n-1 edges that is not a tree gives a singular minor. -/
theorem non_tree_minor_det :
    Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors.non_tree_minor_detType := by
  intro V _ G K _ o r S e hsize hnt
  classical
  have : Nonempty V := ⟨r⟩
  apply disconnected_minor_det_eq_zero G K o r S e
  intro hc
  apply hnt
  apply (tree_iff_edge_count _).mpr
  exact ⟨hc, by rw [selectedGraph_card, Nat.card_eq_fintype_card, hsize]⟩

/-- The coefficient used in the Cauchy--Binet expansion is the tree indicator. -/
theorem minor_det_sq :
    Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors.minor_det_sqType := by
  intro V _ G K _ o r S e hs
  classical
  by_cases ht : (selectedGraph G S).IsTree
  · rcases tree_minor_det G K o r S e ht with h | h <;> simp [ht, h]
  · simp [ht, non_tree_minor_det G K o r S e hs ht]

/-- A single vertex leaves the 0-by-0 determinant, including in characteristic two. -/
theorem singleton_minor_det :
    Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors.singleton_minor_detType := by
  intro V _ _ G K _ o r S e
  classical
  have : IsEmpty {x : V // x ≠ r} :=
    ⟨fun x => x.property (Subsingleton.elim _ _)⟩
  exact Matrix.det_isEmpty

end FiniteCombinatorics.Graph.Trees
