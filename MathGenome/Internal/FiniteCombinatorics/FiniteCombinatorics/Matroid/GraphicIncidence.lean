import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GraphicIncidence
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.MultigraphFoundation
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Trees.Incidence
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.VectorRepresentation
import Mathlib.Tactic.FinCases

universe u v w z
noncomputable section
namespace FiniteCombinatorics.Matroid.Graphic
open Set
attribute [local instance] Classical.propDecidable

variable {α : Type u} {β : Type v} (G : _root_.Graph α β)

/-- Orient every edge by choosing its two ends. -/
theorem orientation_exists : Nonempty (Orientation G) := by
  classical
  let ends (e : G.edgeSet) := G.exists_isLink_of_mem_edgeSet e.property
  exact ⟨⟨fun e => (ends e).choose,
    fun e => (ends e).choose_spec.choose,
    fun e => (ends e).choose_spec.choose_spec⟩⟩

theorem Forest.mono {A B : Set β} (h : Forest G A) (hBA : B ⊆ A) : Forest G B :=
  ⟨hBA.trans h.1, fun n c hc => h.2 n c (hc.trans hBA)⟩

theorem Forest.no_loop {A : Set β} (hA : Forest G A) {e : β} (he : e ∈ A)
    {x : α} (h : G.IsLink e x x) : False := by
  let c : Cycle G 1 := ⟨by decide, fun _ => x, fun _ => e,
    fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _,
    fun _ => h⟩
  exact hA.2 1 c (by rintro _ ⟨i, rfl⟩; exact he)

/-- A two-cycle uses two distinct edge labels, even when their ends agree. -/
theorem Forest.edge_unique {A : Set β} (hA : Forest G A) {e f : β}
    (he : e ∈ A) (hf : f ∈ A) {x y : α}
    (hel : G.IsLink e x y) (hfl : G.IsLink f x y) : e = f := by
  by_contra hne
  have hxy : x ≠ y := fun h => hA.no_loop G he (h ▸ hel)
  let c : Cycle G 2 := {
    positive := by decide
    vertex := ![x, y]
    edge := ![e, f]
    vertex_injective := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all
    edge_injective := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all
    link := by
      intro i
      fin_cases i
      · simpa [finRotate_apply] using hel
      · simpa [finRotate_apply] using hfl.symm }
  apply hA.2 2 c
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> assumption

/-- Any forest restriction is simple; loops and parallel pairs would be cycles. -/
theorem Forest.restrict_simple {A : Set β} (hA : Forest G A) :
    (G.restrict A).Simple where
  not_isLoopAt e x h := hA.no_loop G h.1 h.2
  eq_of_isLink := fun {_ _ _ _} he hf => hA.edge_unique G he.1 hf.1 he.2 hf.2

private theorem rotate_twice_ne {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  letI : NeZero n := ⟨by omega⟩
  intro h
  simp only [finRotate_apply, add_assoc] at h
  have htwo : (1 : Fin n) + 1 = 0 := add_left_cancel (show i + (1 + 1) = i + 0 by simpa only [add_zero] using h)
  have hv := congrArg Fin.val htwo
  have h1 : 1 < n := by omega
  have h2 : 2 < n := by omega
  norm_num [Fin.val_add, Fin.val_ofNat, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt h2] at hv

/-- Every cycle of the simple adjacency shadow lifts to a cycle with distinct
edge labels. Reversed equal edges would force a forbidden two-step rotation. -/
theorem Forest.shadow_acyclic {A : Set β} (hA : Forest G A) :
    (G.restrict A).toSimpleGraph.IsAcyclic := by
  classical
  apply SimpleGraph.isAcyclic_iff_free_cycleGraph.mpr
  intro n hn ⟨f⟩
  letI : NeZero n := ⟨by omega⟩
  have hadj (i : Fin n) : (SimpleGraph.cycleGraph n).Adj i (finRotate n i) := by
    rw [SimpleGraph.cycleGraph_adj']
    right
    simp [finRotate_apply, add_sub_cancel_left, Fin.val_ofNat, Nat.mod_eq_of_lt (show 1 < n by omega)]
  have hex (i : Fin n) : ∃ e, e ∈ A ∧
      G.IsLink e (f i).val (f (finRotate n i)).val := by
    obtain ⟨e, he⟩ := (f.toHom.map_adj (hadj i)).2
    exact ⟨e, he⟩
  choose edge heA he using hex
  have hv : Function.Injective (fun i => (f i).val) :=
    Subtype.val_injective.comp f.injective
  let c : Cycle G n := {
    positive := by omega
    vertex := fun i => (f i).val
    edge := edge
    vertex_injective := hv
    edge_injective := by
      intro i j hij
      have h := (he i).eq_and_eq_or_eq_and_eq (hij ▸ he j)
      rcases h with ⟨h, _⟩ | ⟨hij', hji'⟩
      · exact hv h
      · have h1 := hv hij'
        have h2 := hv hji'
        exact False.elim (rotate_twice_ne hn j (by rw [← h1, h2]))
    link := he }
  exact hA.2 n c (by rintro _ ⟨i, rfl⟩; exact heA i)

/-- A finite nonempty forest has a vertex with exactly one incident edge
identity. Isolated vertices do not affect the argument. -/
theorem Forest.leaf {A : Set β} (hV : G.vertexSet.Finite)
    (hA : Forest G A) (hne : A.Nonempty) :
    ∃ x : G.vertexSet, ∃ e ∈ A, G.Inc e x.val ∧
      ∀ f ∈ A, G.Inc f x.val → f = e := by
  classical
  letI : Finite G.vertexSet := hV.to_subtype
  letI : Fintype G.vertexSet := Fintype.ofFinite _
  let H : SimpleGraph G.vertexSet := (G.restrict A).toSimpleGraph
  obtain ⟨e, he⟩ := hne
  obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet (hA.1 he)
  let a' : G.vertexSet := ⟨a, hab.left_mem⟩
  let b' : G.vertexSet := ⟨b, hab.right_mem⟩
  have hab' : H.Adj a' b' := by
    refine ⟨?_, e, he, hab⟩
    intro h
    have habEq : a = b := congrArg Subtype.val h
    exact hA.no_loop G he (habEq ▸ hab)
  letI : Nonempty G.vertexSet := ⟨a'⟩
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H
  have hpos : 1 ≤ p.length := by
    have h := hmax a' b' (.cons hab' .nil) (by simp [hab'.ne])
    simpa using h
  have hnil : ¬ p.Nil := by
    intro h
    have := h.length_eq_zero
    omega
  have hu : ∀ w, H.Adj u w → w = p.snd := by
    intro w hw
    apply (hA.shadow_acyclic G).eq_snd_of_adj_start hp hw
    by_contra hn
    have hle := hmax w v (p.cons hw.symm) (hp.cons hn)
    simp only [SimpleGraph.Walk.length_cons] at hle
    omega
  obtain ⟨f, hf, hfl⟩ := (p.adj_snd hnil).2
  refine ⟨u, f, hf, hfl.inc_left, ?_⟩
  intro g hg hgi
  obtain ⟨y, hgy⟩ := hgi
  let y' : G.vertexSet := ⟨y, hgy.right_mem⟩
  have hgy' : H.Adj u y' := by
    refine ⟨?_, g, hg, hgy⟩
    intro h
    exact hA.no_loop G hg (congrArg Subtype.val h ▸ hgy)
  have hy := congrArg Subtype.val (hu y' hgy')
  exact hA.edge_unique G hg hf (hy ▸ hgy) hfl

variable (K : Type w) [Field K] (o : Orientation G)

/-- A loop has the zero column, in every characteristic. -/
theorem column_loop {e : β} {x : α} (h : G.IsLink e x x) :
    column G K o e = 0 := by
  classical
  have he := h.edge_mem
  have hends := (o.link ⟨e, he⟩).eq_and_eq_or_eq_and_eq h
  rcases hends with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;>
    ext y <;> simp [column, he, ht, hh]

/-- Reversing a traversal multiplies its signed column by -1. -/
theorem traversal_coefficient {e : β} {a b : α} (h : G.IsLink e a b) :
    ∃ t : K, t ≠ 0 ∧ t • column G K o e =
      (fun x : G.vertexSet =>
        (if x.val = b then 1 else 0) - (if x.val = a then 1 else 0)) := by
  classical
  have he := h.edge_mem
  rcases (o.link ⟨e, he⟩).eq_and_eq_or_eq_and_eq h with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · refine ⟨1, one_ne_zero, ?_⟩
    ext x
    simp [column, he, ht, hh]
  · refine ⟨-1, neg_ne_zero.mpr one_ne_zero, ?_⟩
    ext x
    simp [column, he, ht, hh, sub_eq_add_neg]

/-- An indexed cycle gives a nontrivial telescoping dependence.
The coefficients are ±1, hence stay nonzero in characteristic two. -/
theorem cycle_dependent {n : ℕ} (c : Cycle G n) {A : Set β}
    (hA : Set.range c.edge ⊆ A) : ¬ LinearIndepOn K (column G K o) A := by
  classical
  intro hi
  let edge : Fin n → A := fun i => ⟨c.edge i, hA ⟨i, rfl⟩⟩
  have hinj : Function.Injective edge := by
    intro i j hij
    exact c.edge_injective (congrArg Subtype.val hij)
  have hli := hi.comp edge hinj
  choose t ht hcol using fun i => traversal_coefficient G K o (c.link i)
  have hsum : ∑ i, t i • column G K o (c.edge i) = 0 := by
    simp_rw [hcol]
    ext x
    simp only [Finset.sum_apply, Pi.zero_apply]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (Equiv.sum_comp (finRotate n)
      (fun i : Fin n => if x.val = c.vertex i then (1 : K) else 0))
  have hzero := (Fintype.linearIndependent_iff.mp hli) t hsum
  exact ht ⟨0, c.positive⟩ (hzero ⟨0, c.positive⟩)

theorem independent_forest {A : Set β} (hA : A ⊆ G.edgeSet)
    (hi : LinearIndepOn K (column G K o) A) : Forest G A :=
  ⟨hA, fun _ c hc => cycle_dependent G K o c hc hi⟩

/-- No incidence means a zero entry in that vertex coordinate. -/
theorem column_not_inc {e : β} (x : G.vertexSet) (h : ¬ G.Inc e x.val) :
    column G K o e x = 0 := by
  classical
  by_cases he : e ∈ G.edgeSet
  · have hh : x.val ≠ o.head ⟨e, he⟩ := fun hx =>
      h (hx ▸ (o.link ⟨e, he⟩).inc_right)
    have ht : x.val ≠ o.tail ⟨e, he⟩ := fun hx =>
      h (hx ▸ (o.link ⟨e, he⟩).inc_left)
    simp [column, he, hh, ht]
  · simp [column, he]

/-- A nonloop incidence entry is 1 or -1, and is therefore nonzero over
arbitrary fields, including characteristic two. -/
theorem column_inc_ne_zero {e : β} (x : G.vertexSet) (h : G.Inc e x.val)
    (hn : ¬ G.IsLink e x.val x.val) : column G K o e x ≠ 0 := by
  classical
  have he := h.edge_mem
  have hl := o.link ⟨e, he⟩
  have hne : o.tail ⟨e, he⟩ ≠ o.head ⟨e, he⟩ := by
    intro heq
    rcases h.eq_or_eq_of_isLink hl with hx | hx <;>
      apply hn <;> simpa [hx, heq] using hl
  rcases h.eq_or_eq_of_isLink hl with hx | hx
  · simpa [column, he, hx, hne] using (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))
  · simpa [column, he, hx, Ne.symm hne] using (one_ne_zero : (1 : K) ≠ 0)

/-- Apply the leaf argument to the nonzero support of a relation. This avoids
an induction hypothesis about the orientation of a smaller graph. -/
theorem forest_independent {A : Set β} (hV : G.vertexSet.Finite)
    (hA : Forest G A) : LinearIndepOn K (column G K o) A := by
  classical
  apply linearIndepOn_iff'.mpr
  intro s a hs hsum i hi
  by_contra hai
  let T : Set β := {e | e ∈ s ∧ a e ≠ 0}
  have hT : Forest G T := hA.mono G (fun _ h => hs h.1)
  obtain ⟨x, e, he, hinc, huni⟩ := hT.leaf G hV ⟨i, hi, hai⟩
  have heS : e ∈ s := he.1
  have heN : a e ≠ 0 := he.2
  have hentry : column G K o e x ≠ 0 :=
    column_inc_ne_zero G K o x hinc (fun hl => hT.no_loop G he hl)
  have hxsum : ∑ f ∈ s, a f * column G K o f x = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      using congrFun hsum x
  have hterm : ∀ f ∈ s, f ≠ e → a f * column G K o f x = 0 := by
    intro f hf hfe
    by_cases ha : a f = 0
    · simp [ha]
    · have hni : ¬ G.Inc f x.val := fun hfi => hfe (huni f ⟨hf, ha⟩ hfi)
      rw [column_not_inc G K o x hni, mul_zero]
  rw [Finset.sum_eq_single e hterm (by simp [heS])] at hxsum
  exact mul_ne_zero heN hentry hxsum

theorem columns_independent_iff_forest :
    Specs.FiniteCombinatorics.Matroid.GraphicIncidence.columns_independent_iff_forest := by
  intro α β G hG K _ o A hA
  exact ⟨independent_forest G K o hA, forest_independent G K o hG.1⟩

theorem incidenceMatroid_indep :
    Specs.FiniteCombinatorics.Matroid.GraphicIncidence.incidenceMatroid_indep := by
  intro α β G hG K _ o A
  change (A ⊆ G.edgeSet ∧ LinearIndepOn K (column G K o) A) ↔ Forest G A
  constructor
  · rintro ⟨hA, hi⟩
    exact independent_forest G K o hA hi
  · intro h
    exact ⟨h.1, forest_independent G K o hG.1 h⟩

theorem incidenceMatroid_invariant :
    Specs.FiniteCombinatorics.Matroid.GraphicIncidence.incidenceMatroid_invariant := by
  intro α β G hG K _ L _ o p
  refine _root_.Matroid.ext_indep (M₁ := incidenceMatroid G hG K o)
    (M₂ := incidenceMatroid G hG L p) rfl ?_
  intro A _
  exact (incidenceMatroid_indep G hG K o A).trans (incidenceMatroid_indep G hG L p A).symm

/-- The simple-graph signed matrix and the indexed columns agree exactly. -/
theorem simple_columns : Specs.FiniteCombinatorics.Matroid.GraphicIncidence.simple_columns := by
  intro α G K _ o
  let p : Orientation (_root_.Graph.ofSimpleGraph G) :=
    ⟨o.tail, o.head, fun e => (FiniteCombinatorics.Graph.Multigraph.ofSimpleGraph_isLink
      G e.val (o.tail e) (o.head e)).mpr ⟨(o.edge_eq e).symm,
        (FiniteCombinatorics.Graph.Trees.orientation_endpoints G o e).1⟩⟩
  refine ⟨p, ?_⟩
  intro e x
  have hne := (FiniteCombinatorics.Graph.Trees.orientation_endpoints G o e).2.1
  have he : e.val ∈ (_root_.Graph.ofSimpleGraph G).edgeSet := e.property
  simp only [column]
  rw [dite_eq_left he]
  change ((if x.val = o.head e then (1 : K) else 0) - (if x.val = o.tail e then 1 else 0)) = _
  dsimp [Specs.FiniteCombinatorics.Graph.Trees.Incidence.incidenceValue]
  by_cases hh : x.val = o.head e
  · have ht : x.val ≠ o.tail e := by rw [hh]; exact Ne.symm hne
    simp [hh, ht, hne, Ne.symm hne]
  · by_cases ht : x.val = o.tail e <;> simp [hh, ht, hne, Ne.symm hne]

/-- The indexed cycle convention specializes to the accepted acyclicity
predicate for simple graphs. -/
theorem simple_forest : Specs.FiniteCombinatorics.Matroid.GraphicIncidence.simple_forest := by
  intro α G
  constructor
  · intro h
    have ha := h.shadow_acyclic (_root_.Graph.ofSimpleGraph G)
    rw [show G.edgeSet = (_root_.Graph.ofSimpleGraph G).edgeSet from rfl,
      _root_.Graph.restrict_self] at ha
    exact (_root_.Graph.toSimpleGraphOfSimpleGraphIso G).isAcyclic_iff.mp ha
  · intro ha
    refine ⟨Subset.rfl, ?_⟩
    intro n c _
    have hn : 3 ≤ n := by
      match n with
      | 0 => exact False.elim (Nat.not_lt_zero _ c.positive)
      | 1 =>
        have h := c.link 0
        have hl : G.Adj (c.vertex 0) (c.vertex 0) :=
          (_root_.Graph.ofSimpleGraph_adj_iff _ _).mp ⟨c.edge 0, by simpa only [finRotate_one, Equiv.refl_apply] using h⟩
        exact False.elim (G.loopless.irrefl _ hl)
      | 2 =>
        have h0 : (_root_.Graph.ofSimpleGraph G).IsLink (c.edge 0) (c.vertex 0) (c.vertex 1) := by
          simpa [finRotate_apply] using c.link 0
        have h1 : (_root_.Graph.ofSimpleGraph G).IsLink (c.edge 1) (c.vertex 0) (c.vertex 1) := by
          simpa [finRotate_apply] using (c.link 1).symm
        have h01 : (0 : Fin 2) = 1 := c.edge_injective (h0.eq h1)
        exact False.elim (by simpa using h01)
      | _ + 3 => omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    apply (SimpleGraph.isAcyclic_iff_free_cycleGraph.mp ha) (m + 3) (by omega)
    refine ⟨⟨⟨c.vertex, ?_⟩, c.vertex_injective⟩⟩
    intro i j hij
    have hij' : j = i - 1 ∨ j = i + 1 := by
      have hj : j ∈ (SimpleGraph.cycleGraph (m + 3)).neighborSet i := hij
      rw [SimpleGraph.cycleGraph_neighborSet] at hj
      exact hj
    rcases hij' with rfl | rfl
    · have h := (c.link (i - 1)).symm
      have hr : finRotate (m + 3) (i - 1) = i := by simp [finRotate_apply]
      exact (_root_.Graph.ofSimpleGraph_adj_iff _ _).mp ⟨_, by simpa only [hr] using h⟩
    · exact (_root_.Graph.ofSimpleGraph_adj_iff _ _).mp ⟨_, by
        simpa only [finRotate_apply] using c.link i⟩

/-- Restricting to the proposed forest edges preserves exactly its cycles. -/
theorem forest_restrict (A : Set β) : Forest (G.restrict A) A ↔ Forest G A := by
  constructor
  · rintro ⟨hA, h⟩
    refine ⟨fun e he => (hA he).1, ?_⟩
    intro n c hc
    let d : Cycle (G.restrict A) n :=
      ⟨c.positive, c.vertex, c.edge, c.vertex_injective, c.edge_injective,
        fun i => ⟨hc ⟨i, rfl⟩, c.link i⟩⟩
    exact h n d hc
  · rintro ⟨hA, h⟩
    refine ⟨fun e he => ⟨hA he, he⟩, ?_⟩
    intro n c hc
    let d : Cycle G n :=
      ⟨c.positive, c.vertex, c.edge, c.vertex_injective, c.edge_injective,
        fun i => (c.link i).2⟩
    exact h n d hc

theorem simple_subset_forest :
    Specs.FiniteCombinatorics.Matroid.GraphicIncidence.simple_subset_forest := by
  intro α G A hA
  let H := SimpleGraph.fromEdgeSet A
  have hE : H.edgeSet = A := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    exact ⟨fun h => h.1, fun he => ⟨he, G.not_isDiag_of_mem_edgeSet (hA he)⟩⟩
  have hgraph : (_root_.Graph.ofSimpleGraph G).restrict A = _root_.Graph.ofSimpleGraph H := by
    refine _root_.Graph.ext (G₁ := (_root_.Graph.ofSimpleGraph G).restrict A)
      (G₂ := _root_.Graph.ofSimpleGraph H) rfl ?_
    intro e x y
    change (e ∈ A ∧ (e = s(x, y) ∧ e ∈ G.edgeSet)) ↔
      (e = s(x, y) ∧ e ∈ H.edgeSet)
    rw [hE]
    constructor
    · rintro ⟨he, hxy, _⟩
      exact ⟨hxy, he⟩
    · rintro ⟨hxy, he⟩
      exact ⟨he, hxy, hA he⟩
  rw [← forest_restrict (_root_.Graph.ofSimpleGraph G) A, hgraph]
  simpa only [hE] using simple_forest H

end FiniteCombinatorics.Matroid.Graphic
