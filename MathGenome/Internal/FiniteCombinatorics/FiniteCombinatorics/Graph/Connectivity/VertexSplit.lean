import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Connectivity.VertexSplit
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.Foundations

open scoped BigOperators
noncomputable section
universe u
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
namespace FiniteCombinatorics.Graph.VertexSplit
open FiniteCombinatorics.Directed FiniteCombinatorics.Graph.Flows
open VertexSplitSpec
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {s t : V}

@[simp] theorem input_source : input s t s = source s t := by
  classical
  simp [input]
@[simp] theorem output_source : output s t s = source s t := by
  classical
  simp [output]
@[simp] theorem input_sink (hst : s ≠ t) : input s t t = sink s t := by
  classical
  simp [input, Ne.symm hst]
@[simp] theorem output_sink (hst : s ≠ t) : output s t t = sink s t := by
  classical
  simp [output, Ne.symm hst]
@[simp] theorem input_internal (v : Internal s t) : input s t v.val = .inr (v, false) := by
  classical
  simp [input, v.property.1, v.property.2]
@[simp] theorem output_internal (v : Internal s t) : output s t v.val = .inr (v, true) := by
  classical
  simp [output, v.property.1, v.property.2]
@[simp] theorem original_source : original s t (source s t) = s := by simp [original, source]
@[simp] theorem original_sink : original s t (sink s t) = t := by simp [original, sink]
@[simp] theorem original_input (hst : s ≠ t) (v : V) : original s t (input s t v) = v := by
  classical
  by_cases hs : v = s
  · subst v; simp
  by_cases ht : v = t
  · subst v; simp [input_sink hst]
  simp [input, original, hs, ht]
@[simp] theorem original_output (hst : s ≠ t) (v : V) : original s t (output s t v) = v := by
  classical
  by_cases hs : v = s
  · subst v; simp
  by_cases ht : v = t
  · subst v; simp [output_sink hst]
  simp [output, original, hs, ht]

theorem output_injective (hst : s ≠ t) : Function.Injective (output s t) :=
  Function.LeftInverse.injective (original_output hst)

theorem input_injective (hst : s ≠ t) : Function.Injective (input s t) :=
  Function.LeftInverse.injective (original_input hst)

@[simp] theorem mem_splitArcs (a : VertexSplitSpec.Arc G s t) :
    a ∈ splitArcs G s t ↔ ∃ v : Internal s t, a = .inl v := by
  classical
  simp [splitArcs, eq_comm]

theorem capacities : VertexSplitSpec.capacities := by
  intro V _ G s t
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, mem_splitArcs⟩

theorem card_internal (hst : s ≠ t) : Fintype.card (Internal s t) = Fintype.card V - 2 := by
  classical
  have h := Fintype.card_subtype_compl (p := fun v : V => v = s ∨ v = t)
  have htwo : Fintype.card {v : V // v = s ∨ v = t} = 2 :=
    Fintype.card_subtype_eq_or_eq_of_ne hst
  have hc : Fintype.card (Internal s t) = Fintype.card {v : V // ¬(v = s ∨ v = t)} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun _ => not_or.symm)
  rw [hc, h, htwo]

theorem two_le_card (hst : s ≠ t) : 2 ≤ Fintype.card V := by
  classical
  have h := Finset.card_le_card (Finset.subset_univ ({s,t} : Finset V))
  simpa [hst] using h

@[simp] theorem mem_initialCut_input (v : V) :
    input s t v ∈ initialCut s t ↔ v ≠ t ∨ v = s := by
  classical
  by_cases hs : v = s
  · subst v; simp [input_source, initialCut]
  by_cases ht : v = t
  · subst v
    simp [input, hs, initialCut, source, sink]
  · simp [input, hs, ht, initialCut, source]

@[simp] theorem mem_initialCut_output (v : V) :
    output s t v ∈ initialCut s t ↔ v = s := by
  classical
  by_cases hs : v = s
  · subst v; simp [output_source, initialCut]
  by_cases ht : v = t
  · subst v
    simp [output, hs, initialCut, source, sink]
  · simp [output, hs, ht, initialCut, source]

theorem initial_outgoing (hst : s ≠ t) (hn : ¬G.Adj s t) :
    (network G s t).outgoing (initialCut s t) = splitArcs G s t := by
  classical
  ext a
  rcases a with v | ⟨⟨a,b⟩, hab⟩
  · simp [Network.mem_outgoing, network, graph, initialCut, source]
    exact ⟨v.val, v.property, rfl⟩
  · simp only [Network.mem_outgoing, network, graph, mem_initialCut_output,
      mem_initialCut_input, mem_splitArcs, reduceCtorEq, exists_false, iff_false]
    rintro ⟨rfl, hb⟩
    have hbt : b = t := by tauto
    subst b
    exact hn hab

theorem initial_cut : VertexSplitSpec.initial_cut := by
  intro V _ G s t hst hn
  have ho := initial_outgoing hst hn
  refine ⟨?_, ho, ?_⟩
  · constructor
    · exact Or.inl rfl
    · simp [network, initialCut, source, sink]
  · change (network G s t).cutCapacity (initialCut s t) = _
    classical
    rw [Network.cutCapacity_eq, ho]
    simp only [splitArcs, Finset.sum_map, Function.Embedding.coeFn_mk,
      network, capacityNat, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp [card_internal hst]

/-- Collapse only split steps, retaining every original transit in order. -/
def projectWalk (hst : s ≠ t) {x y : Vertex s t}
    (p : Directed.Walk (graph G s t) x y) :
    G.Walk (original s t x) (original s t y) := by
  induction p with
  | nil x => exact .nil
  | @cons x y z a p ih =>
    rcases a with ⟨v | e, hx, hy⟩
    · change Sum.inr (v, false) = x at hx
      change Sum.inr (v, true) = y at hy
      subst x; subst y
      exact ih
    · change output s t e.val.1 = x at hx
      change input s t e.val.2 = y at hy
      subst x; subst y
      exact (SimpleGraph.Walk.cons e.property
        (ih.copy (original_input hst _) rfl)).copy (original_output hst _).symm rfl

@[simp] theorem projectWalk_nil (hst : s ≠ t) (x : Vertex s t) :
    projectWalk (G := G) hst (Directed.Walk.nil x) = .nil := rfl

@[simp] theorem projectWalk_split (hst : s ≠ t) (v : Internal s t)
    {z : Vertex s t} (p : Directed.Walk (graph G s t) (.inr (v, true)) z) :
    projectWalk hst (Directed.Walk.cons ⟨Sum.inl v, rfl, rfl⟩ p) =
      projectWalk hst p := rfl

@[simp] theorem projectWalk_transit_support (hst : s ≠ t) (e : Edge G)
    {z : Vertex s t} (p : Directed.Walk (graph G s t) (input s t e.val.2) z) :
    (projectWalk hst (Directed.Walk.cons ⟨Sum.inr e, rfl, rfl⟩ p)).support =
      e.val.1 :: (projectWalk hst p).support := by
  change ((SimpleGraph.Walk.cons e.property
    ((projectWalk hst p).copy (original_input hst _) rfl)).copy
    (original_output hst _).symm rfl).support = _
  simp only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons]

/-- Output representatives occur in the projected order. At a split step we
skip the input copy; at a transit step we keep its tail. -/
theorem projectWalk_support_sublist (hst : s ≠ t) {x y : Vertex s t}
    (p : Directed.Walk (graph G s t) x y) (hy : output s t (original s t y) = y) :
    ((projectWalk hst p).support.map (output s t)).Sublist p.vertices := by
  induction p with
  | nil x => simp [hy]
  | @cons x y z a p ih =>
    rcases a with ⟨v | e, hx, hhead⟩
    · change Sum.inr (v, false) = x at hx
      change Sum.inr (v, true) = y at hhead
      subst x; subst y
      exact (ih hy).cons _
    · change output s t e.val.1 = x at hx
      change input s t e.val.2 = y at hhead
      subst x; subst y
      change ((projectWalk hst (Directed.Walk.cons ⟨Sum.inr e, rfl, rfl⟩ p)).support.map
        (output s t)).Sublist (output s t e.val.1 :: p.vertices)
      rw [projectWalk_transit_support, List.map_cons]
      exact (ih hy).cons_cons _


/-- The projection is a simple path because its output representatives form a
sublist of the directed path's distinct vertices. -/
def project (hst : s ≠ t) (p : DirectedPath G s t) : G.Path s t := by
  have hsub := projectWalk_support_sublist hst p.val (by simp [output_sink hst])
  have hn : ((projectWalk hst p.val).support.map (output s t)).Nodup := hsub.nodup p.property
  have hp : (projectWalk hst p.val).IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    exact List.Nodup.of_map _ hn
  exact ⟨(projectWalk hst p.val).copy original_source original_sink,
    (SimpleGraph.Walk.isPath_copy _ _ _).2 hp⟩

def copyWalk {W E : Type*} [Fintype W] [Fintype E] {H : Digraph W E}
    {x y x' y' : W} (p : Directed.Walk H x y) (hx : x = x') (hy : y = y') :
    Directed.Walk H x' y' := hx ▸ hy ▸ p

@[simp] theorem vertices_copyWalk {W E : Type*} [Fintype W] [Fintype E] {H : Digraph W E}
    {x y x' y' : W} (p : Directed.Walk H x y) (hx : x = x') (hy : y = y') :
    (copyWalk p hx hy).vertices = p.vertices := by subst_vars; rfl

@[simp] theorem arcs_copyWalk {W E : Type*} [Fintype W] [Fintype E] {H : Digraph W E}
    {x y x' y' : W} (p : Directed.Walk H x y) (hx : x = x') (hy : y = y') :
    (copyWalk p hx hy).arcs = p.arcs := by subst_vars; rfl

/-- Cross an internal vertex, and do nothing at the unsplit endpoints. -/
def bridge (G : SimpleGraph V) (s t v : V) :
    Directed.Walk (graph G s t) (input s t v) (output s t v) := by
  classical
  by_cases hs : v = s
  · exact copyWalk (Directed.Walk.nil (source s t))
      (by subst v; simp) (by subst v; simp)
  by_cases ht : v = t
  · exact copyWalk (Directed.Walk.nil (sink s t))
      (by subst v; simp [input, hs]) (by subst v; simp [output, hs])
  · let w : Internal s t := ⟨v, hs, ht⟩
    exact copyWalk (Directed.Walk.single (graph G s t) (Sum.inl w))
      (input_internal w).symm (output_internal w).symm

def copies (s t v : V) : List (Vertex s t) := by
  classical
  exact if v = s ∨ v = t then [output s t v] else [input s t v, output s t v]

theorem bridge_vertices (v : V) : (bridge G s t v).vertices = copies s t v := by
  classical
  by_cases hs : v = s
  · subst v
    simp [bridge, copies]
  by_cases ht : v = t
  · subst v
    simp only [bridge, dite_eq_right hs, dite_true, vertices_copyWalk,
      Directed.Walk.vertices_nil]
    simp [copies, output, hs]
  · simp only [bridge, dite_eq_right hs, dite_eq_right ht, vertices_copyWalk,
      Directed.Walk.vertices_single]
    simp [copies, hs, ht, input, output, graph]

theorem copies_nodup (v : V) : (copies s t v).Nodup := by
  classical
  by_cases hs : v = s
  · simp [copies, hs]
  by_cases ht : v = t
  · simp [copies, ht]
  · simp [copies, hs, ht, input, output]

theorem original_mem_copies (hst : s ≠ t) {v : V} {x : Vertex s t}
    (hx : x ∈ copies s t v) : original s t x = v := by
  classical
  by_cases h : v = s ∨ v = t
  · have hx' : x = output s t v := by simpa [copies, h] using hx
    rw [hx']; exact original_output hst v
  · simp only [copies, ite_eq_right h, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact original_input hst _
    · exact original_output hst _

theorem output_sublist_copies (v : V) : [output s t v].Sublist (copies s t v) := by
  classical
  by_cases h : v = s ∨ v = t
  · simp [copies, h]
  · simp only [copies, ite_eq_right h]
    exact (List.Sublist.refl _).cons _

/-- Orient each original edge, inserting the unique split step at its head. -/
def liftWalk {a b : V} : G.Walk a b → Directed.Walk (graph G s t) (output s t a) (output s t b)
  | .nil => .nil _
  | .cons' a v b h p =>
    .cons ⟨Sum.inr ⟨(a,v), h⟩, rfl, rfl⟩ ((bridge G s t v).append (liftWalk p))

/-- The lifted vertex sequence expands internal vertices in their original
order; the initial vertex is represented by its output copy. -/
theorem liftWalk_vertices {a b : V} (p : G.Walk a b) :
    (liftWalk (s := s) (t := t) p).vertices =
      output s t a :: p.support.tail.flatMap (copies s t) := by
  induction p with
  | nil => rfl
  | @cons a v b h p ih =>
    change output s t a :: ((bridge G s t v).append (liftWalk p)).vertices = _
    rw [Directed.Walk.vertices_append, bridge_vertices, ih]
    simp only [SimpleGraph.Walk.support_cons, List.tail_cons]
    let l := p.support.tail
    have hl : p.support = v :: l := p.cons_tail_support.symm
    rw [hl]
    simp only [List.flatMap_cons, List.tail_cons]
    classical
    by_cases hs : v = s
    · simp [copies, hs]
    by_cases ht : v = t
    · simp [copies, ht]
    · simp [copies, hs, ht]

theorem liftWalk_vertices_sublist {a b : V} (p : G.Walk a b) :
    (liftWalk (s := s) (t := t) p).vertices.Sublist (p.support.flatMap (copies s t)) := by
  rw [liftWalk_vertices]
  let l := p.support.tail
  have hl : p.support = a :: l := p.cons_tail_support.symm
  rw [hl]
  exact (output_sublist_copies a).append (List.Sublist.refl _)

theorem expanded_nodup (hst : s ≠ t) (l : List V) (hl : l.Nodup) :
    (l.flatMap (copies s t)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun v _ => copies_nodup v, hl.imp ?_⟩
  intro a b hab
  apply List.disjoint_left.2
  intro x hxa hxb
  exact hab ((original_mem_copies hst hxa).symm.trans (original_mem_copies hst hxb))

/-- The lift is a directed simple path, with the shared original arc identities. -/
def lift (hst : s ≠ t) (p : G.Path s t) : DirectedPath G s t := by
  have hp : (liftWalk (s := s) (t := t) p.val).IsPath :=
    (liftWalk_vertices_sublist p.val).nodup (expanded_nodup hst _ p.property.support_nodup)
  refine ⟨copyWalk (liftWalk p.val) output_source (output_sink hst), ?_⟩
  change (copyWalk (liftWalk p.val) output_source (output_sink hst)).vertices.Nodup
  rw [vertices_copyWalk]
  exact hp

@[simp] theorem projectWalk_copy_support (hst : s ≠ t) {x y x' y' : Vertex s t}
    (p : Directed.Walk (graph G s t) x y) (hx : x = x') (hy : y = y') :
    (projectWalk hst (copyWalk p hx hy)).support = (projectWalk hst p).support := by
  subst_vars
  rfl

theorem projectWalk_append_support (hst : s ≠ t) {x y z : Vertex s t}
    (p : Directed.Walk (graph G s t) x y) (q : Directed.Walk (graph G s t) y z) :
    (projectWalk hst (p.append q)).support =
      (projectWalk hst p).support ++ (projectWalk hst q).support.tail := by
  induction p with
  | nil x => exact (projectWalk hst q).cons_tail_support.symm
  | @cons x y z a p ih =>
    rcases a with ⟨v | e, hx, hy⟩
    · change Sum.inr (v, false) = x at hx
      change Sum.inr (v, true) = y at hy
      subst x; subst y
      exact ih q
    · change output s t e.val.1 = x at hx
      change input s t e.val.2 = y at hy
      subst x; subst y
      change (projectWalk hst (Directed.Walk.cons ⟨Sum.inr e, rfl, rfl⟩ (p.append q))).support = _
      rw [projectWalk_transit_support, projectWalk_transit_support, ih, List.cons_append]

theorem projectWalk_bridge_support (hst : s ≠ t) (v : V) :
    (projectWalk hst (bridge G s t v)).support = [v] := by
  classical
  by_cases hs : v = s
  · subst v
    simp [bridge, projectWalk_copy_support]
  by_cases ht : v = t
  · subst v
    simp [bridge, hs, projectWalk_copy_support]
  · simp only [bridge, dite_eq_right hs, dite_eq_right ht, projectWalk_copy_support]
    rfl

theorem projectWalk_liftWalk_support (hst : s ≠ t) {a b : V} (p : G.Walk a b) :
    (projectWalk hst (liftWalk (s := s) (t := t) p)).support = p.support := by
  induction p with
  | nil => simp [liftWalk, original_output hst]
  | @cons a v b h p ih =>
    change (projectWalk hst (Directed.Walk.cons ⟨Sum.inr ⟨(a,v),h⟩, rfl, rfl⟩
      ((bridge G s t v).append (liftWalk p)))).support = _
    rw [projectWalk_transit_support, projectWalk_append_support, projectWalk_bridge_support, ih]
    simpa using congrArg (List.cons a) p.cons_tail_support

@[simp] theorem project_support (hst : s ≠ t) (p : DirectedPath G s t) :
    (project hst p).val.support = (projectWalk hst p.val).support := by
  simp only [project, SimpleGraph.Walk.support_copy]

@[simp] theorem lift_vertices (hst : s ≠ t) (p : G.Path s t) :
    (lift hst p).val.vertices = (liftWalk (s := s) (t := t) p.val).vertices := by
  exact vertices_copyWalk _ _ _

theorem project_lift (hst : s ≠ t) (p : G.Path s t) : project hst (lift hst p) = p := by
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_support
  rw [project_support]
  change (projectWalk hst (copyWalk (liftWalk p.val) output_source (output_sink hst))).support = _
  rw [projectWalk_copy_support, projectWalk_liftWalk_support]

/-- Every original vertex in the directed walk remains in the collapsed walk. -/
theorem original_mem_projectWalk (hst : s ≠ t) {x y z : Vertex s t}
    (p : Directed.Walk (graph G s t) x y) (hz : z ∈ p.vertices) :
    original s t z ∈ (projectWalk hst p).support := by
  induction p with
  | nil x =>
    have hz' : z = x := by simpa using hz
    subst z
    exact (projectWalk hst (.nil x)).start_mem_support
  | @cons x y w a p ih =>
    rcases a with ⟨v | e, hx, hy⟩
    · change Sum.inr (v, false) = x at hx
      change Sum.inr (v, true) = y at hy
      subst x; subst y
      rw [Directed.Walk.vertices_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact (projectWalk hst p).start_mem_support
      · exact ih hz
    · change output s t e.val.1 = x at hx
      change input s t e.val.2 = y at hy
      subst x; subst y
      change original s t z ∈
        (projectWalk hst (Directed.Walk.cons ⟨Sum.inr e, rfl, rfl⟩ p)).support
      rw [projectWalk_transit_support, List.mem_cons]
      rw [Directed.Walk.vertices_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inl (original_output hst _)
      · exact Or.inr (ih hz)

/-- A noninitial vertex of a directed walk is the head of a traversed arc. -/
theorem exists_incoming_arc {W E : Type*} [Fintype W] [Fintype E] {H : Digraph W E}
    {x y z : W} (p : Directed.Walk H x y) (hz : z ∈ p.vertices) :
    z = x ∨ ∃ a ∈ p.arcs, H.head a = z := by
  induction p with
  | nil => exact Or.inl (by simpa using hz)
  | @cons x y w a p ih =>
    rw [Directed.Walk.vertices_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Or.inl rfl
    · rcases ih hz with rfl | ⟨b, hb, he⟩
      · exact Or.inr ⟨a.val, by simp, a.property.2⟩
      · exact Or.inr ⟨b, by simp [hb], he⟩

theorem arc_head_mem_vertices {W E : Type*} [Fintype W] [Fintype E] {H : Digraph W E}
    {x y : W} (p : Directed.Walk H x y) {a : E} (ha : a ∈ p.arcs) :
    H.head a ∈ p.vertices := by
  induction p with
  | nil => simp at ha
  | cons b p ih =>
    rw [Directed.Walk.arcs_cons, List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Directed.Walk.vertices_cons, b.property.2]
      exact List.mem_cons_of_mem _ (by
        obtain ⟨l, hl⟩ := p.vertices_eq_cons
        simp [hl])
    · exact List.mem_cons_of_mem _ (ih ha)

theorem input_ne_output_internal (v : V) (w : Internal s t) :
    input s t v ≠ Sum.inr (w, true) := by
  classical
  by_cases hs : v = s
  · simp [input, hs, source]
  by_cases ht : v = t
  · subst v; simp [input, hs, sink]
  · simp [input, hs, ht]

theorem head_output_iff (a : VertexSplitSpec.Arc G s t) (v : Internal s t) :
    (graph G s t).head a = .inr (v, true) ↔ a = .inl v := by
  cases a with
  | inl w => simp [graph]
  | inr e => simp [graph, input_ne_output_internal]

theorem project_mem_iff (hst : s ≠ t) (p : DirectedPath G s t) (v : Internal s t) :
    v.val ∈ (project hst p).val.support ↔ Sum.inl v ∈ Directed.Spec.arcs p.val := by
  rw [project_support]
  constructor
  · intro hv
    have hsub := projectWalk_support_sublist hst p.val (by simp [output_sink hst])
    have ho : Sum.inr (v,true) ∈ p.val.vertices := by
      rw [← output_internal v]
      exact hsub.subset (List.mem_map_of_mem hv)
    rcases exists_incoming_arc p.val ho with h | ⟨a, ha, he⟩
    · simp [source] at h
    · have he' := (head_output_iff a v).1 he
      subst a
      exact ha
  · intro ha
    have h := original_mem_projectWalk hst p.val (arc_head_mem_vertices p.val ha)
    exact h

theorem internal_on_walk (hst : s ≠ t) (hn : ¬G.Adj s t) (p : G.Walk s t) :
    ∃ v : Internal s t, v.val ∈ p.support := by
  cases p with
  | nil => exact (hst rfl).elim
  | @cons u v w h p =>
    have has : v ≠ s := h.ne.symm
    have hat : v ≠ t := by intro he; subst v; exact hn h
    exact ⟨⟨v, has, hat⟩, List.mem_cons_of_mem _ p.start_mem_support⟩

/-- The projection keeps precisely the transit edges, in their original order. -/
theorem projectWalk_transit_sequence (hst : s ≠ t) {x y : Vertex s t}
    (p : Directed.Walk (graph G s t) x y) :
    (projectWalk hst p).darts.map (fun d => (d.fst, d.snd)) =
      transitSequence G s t p.arcs := by
  induction p with
  | nil => rfl
  | @cons x y z a p ih =>
    rcases a with ⟨v | e, hx, hy⟩
    · change Sum.inr (v, false) = x at hx
      change Sum.inr (v, true) = y at hy
      subst x; subst y
      exact ih
    · change output s t e.val.1 = x at hx
      change input s t e.val.2 = y at hy
      subst x; subst y
      change (((SimpleGraph.Walk.cons e.property
        ((projectWalk hst p).copy (original_input hst _) rfl)).copy
        (original_output hst _).symm rfl).darts.map (fun d => (d.fst, d.snd))) = _
      simpa only [SimpleGraph.Walk.darts_copy, SimpleGraph.Walk.darts_cons, List.map_cons,
        Directed.Walk.arcs_cons, transitSequence, List.filterMap_cons, List.map_cons] using
        congrArg (List.cons e.val) ih

theorem path_transport : VertexSplitSpec.path_transport := by
  intro V _ G s t hst hn
  refine ⟨project hst, lift hst, project_lift hst, ?_, ?_, project_mem_iff hst, ?_⟩
  · intro p
    change ((projectWalk hst p.val).copy original_source original_sink).darts.map
      (fun d => (d.fst, d.snd)) = _
    rw [SimpleGraph.Walk.darts_copy]
    exact projectWalk_transit_sequence hst p.val
  · intro p
    rw [project_support]
    exact projectWalk_support_sublist hst p.val (by simp [output_sink hst])
  · intro p
    obtain ⟨v, hv⟩ := internal_on_walk hst hn (project hst p).val
    exact ⟨.inl v, (mem_splitArcs _).2 ⟨v,rfl⟩, (project_mem_iff hst p v).1 hv⟩

/-- A transit arc alone already exceeds the small-cut threshold. -/
theorem no_transit_of_small (hst : s ≠ t) (U : Set (Vertex s t))
    (hU : (network G s t).cutCapacity U ≤ ((Fintype.card V - 2 : ℕ) : ℝ))
    (e : Edge G) : Sum.inr e ∉ (network G s t).outgoing U := by
  classical
  intro he
  have hle : (Fintype.card V : ℝ) ≤ (network G s t).cutCapacity U :=
    Finset.single_le_sum (fun a _ => (network G s t).capacity_nonneg a) he
  have hlt : Fintype.card V - 2 < Fintype.card V := by
    have h := two_le_card hst
    omega
  exact (not_le_of_gt ((Nat.cast_lt (α := ℝ)).mpr hlt)) (hle.trans hU)

def cutVertices (U : Set (Vertex s t)) : Finset (Internal s t) := by
  classical
  exact Finset.univ.filter (fun v => Sum.inr (v,false) ∈ U ∧ Sum.inr (v,true) ∉ U)

@[simp] theorem mem_cutVertices (U : Set (Vertex s t)) (v : Internal s t) :
    v ∈ cutVertices U ↔ Sum.inr (v,false) ∈ U ∧ Sum.inr (v,true) ∉ U := by
  classical
  simp [cutVertices]

@[simp] theorem mem_separator_internal (U : Set (Vertex s t)) (v : Internal s t) :
    v.val ∈ separator G s t U ↔ Sum.inl v ∈ (network G s t).outgoing U := by
  classical
  change v.val ∈ (cutVertices U).image Subtype.val ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, he⟩
    have he' : w = v := Subtype.ext he
    subst w
    exact (Network.mem_outgoing _ _ _).2 ((mem_cutVertices U v).1 hw)
  · intro hv
    exact ⟨v, (mem_cutVertices U v).2 ((Network.mem_outgoing _ _ _).1 hv), rfl⟩

theorem separator_excludes (U : Set (Vertex s t)) :
    s ∉ separator G s t U ∧ t ∉ separator G s t U := by
  classical
  constructor <;> intro h
  all_goals
    obtain ⟨v, hv, he⟩ := Finset.mem_image.1 h
    first | exact v.property.1 he | exact v.property.2 he

theorem outgoing_eq_selected (U : Set (Vertex s t))
    (htrans : ∀ e : Edge G, Sum.inr e ∉ (network G s t).outgoing U) :
    (network G s t).outgoing U = (cutVertices U).map ⟨Sum.inl, Sum.inl_injective⟩ := by
  classical
  ext a
  cases a with
  | inl v => simp [Network.mem_outgoing, network, graph]
  | inr e => simp [htrans e]

theorem separator_card (U : Set (Vertex s t))
    (htrans : ∀ e : Edge G, Sum.inr e ∉ (network G s t).outgoing U) :
    ((separator G s t U).card : ℝ) = (network G s t).cutCapacity U := by
  classical
  have hcard : (separator G s t U).card = (cutVertices U).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  rw [Network.cutCapacity_eq, outgoing_eq_selected U htrans, hcard, Finset.sum_map]
  simp [network, capacityNat]

/-- Any walk from inside to outside a set traverses an outgoing original arc. -/
theorem exists_crossing {W E : Type*} [Fintype W] [Fintype E] (N : Network W E)
    {x y : W} (p : Directed.Walk N.graph x y) (U : Set W) (hx : x ∈ U) (hy : y ∉ U) :
    ∃ a ∈ p.arcs, a ∈ N.outgoing U := by
  classical
  induction p with
  | nil => exact (hy hx).elim
  | @cons x y z a p ih =>
    by_cases hy' : y ∈ U
    · obtain ⟨b, hb, hU⟩ := ih hy' hy
      exact ⟨b, by simp [hb], hU⟩
    · refine ⟨a.val, by simp, (Network.mem_outgoing _ _ _).2 ?_⟩
      rw [a.property.1, a.property.2]
      exact ⟨hx, hy'⟩

theorem small_cut : VertexSplitSpec.small_cut := by
  intro V _ G s t hst hn U hcut hbound
  have htrans := no_transit_of_small (G := G) hst U hbound
  obtain ⟨hs, ht⟩ := separator_excludes (G := G) U
  refine ⟨htrans, hs, ht, separator_card U htrans, ?_, mem_separator_internal U⟩
  intro p
  let q := lift hst p
  obtain ⟨a, ha, haU⟩ := exists_crossing (network G s t) q.val U hcut.1 hcut.2
  cases a with
  | inr e => exact (htrans e haU).elim
  | inl v =>
    refine ⟨v.val, (mem_separator_internal U v).2 haU, ?_⟩
    have hm := (project_mem_iff hst q v).2 ha
    rw [show q = lift hst p from rfl, project_lift] at hm
    exact hm

end FiniteCombinatorics.Graph.VertexSplit
