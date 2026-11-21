import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ResidualFoundation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

open scoped BigOperators Classical
universe u v
namespace P205.Networks
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows

noncomputable def arcSum := @BoundedSpec.arcSum

noncomputable def outgoing := @BoundedSpec.outgoing

noncomputable def incoming := @BoundedSpec.incoming

noncomputable def WithinBounds := @BoundedSpec.WithinBounds

noncomputable def Feasible := @BoundedSpec.Feasible

noncomputable def capacity := @BoundedSpec.capacity

noncomputable def ResidualArc := @BoundedSpec.ResidualArc

noncomputable def graph := @BoundedSpec.graph

noncomputable def cost := @BoundedSpec.cost

noncomputable def step := @BoundedSpec.step

noncomputable def adjustment := @BoundedSpec.adjustment

noncomputable def augment := @BoundedSpec.augment

noncomputable def Bottleneck := @BoundedSpec.Bottleneck

noncomputable def toLibrary := @BoundedSpec.toLibrary

noncomputable def fromLibrary := @BoundedSpec.fromLibrary

noncomputable def toLibraryWalk := @BoundedSpec.toLibraryWalk

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

noncomputable instance residualArcFintype (lo hi f : A → ℝ) :
    Fintype (ResidualArc lo hi f) := by
  change Fintype (BoundedSpec.ResidualArc lo hi f)
  infer_instance

/-- Summing incidence over a vertex subset cancels its internal arcs. -/
theorem cut_divergence : BoundedSpec.cut_divergence.{u,v} := by
  intro V A _ _ G f S
  have hs (g : A → V) :
      (∑ x ∈ Finset.univ.filter (fun x => x ∈ S),
        ∑ a : A, if g a = x then f a else 0) =
      ∑ a : A, if g a ∈ S then f a else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : g a ∈ S
    · rw [Finset.sum_eq_single (g a)]
      · simp [h]
      · intro x _ hx
        simp [Ne.symm hx]
      · simp [h]
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro x hx
      have hne : g a ≠ x := by
        intro he
        exact h (he.symm ▸ (Finset.mem_filter.mp hx).2)
      simp [hne]
  simp_rw [Digraph.divergence_eq]
  rw [Finset.sum_sub_distrib, hs, hs]
  simp only [BoundedSpec.arcSum, BoundedSpec.outgoing, BoundedSpec.incoming,
    Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

theorem sum_divergence : BoundedSpec.sum_divergence.{u,v} := by
  intro V A _ _ G f
  simp_rw [Digraph.divergence_eq]
  rw [Finset.sum_sub_distrib]
  have hs (g : A → V) :
      (∑ x : V, ∑ a : A, if g a = x then f a else 0) = ∑ a, f a := by
    rw [Finset.sum_comm]
    simp
  rw [hs, hs, sub_self]

theorem divergence_add (G : Digraph V A) (f g : A → ℝ) (z : V) :
    G.divergence (fun a => f a + g a) z = G.divergence f z + G.divergence g z := by
  simp only [Digraph.divergence_eq]
  have hs (t : A → V) :
      (∑ a : A, if t a = z then f a + g a else 0) =
      (∑ a : A, if t a = z then f a else 0) +
      ∑ a : A, if t a = z then g a else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [hs, hs]
  ring

theorem divergence_step (G : Digraph V A) (lo hi f : A → ℝ)
    (ε : ℝ) (r : BoundedSpec.ResidualArc lo hi f) (z : V) :
    G.divergence (BoundedSpec.step ε r.val) z =
      (if (BoundedSpec.graph G lo hi f).tail r = z then ε else 0) -
      (if (BoundedSpec.graph G lo hi f).head r = z then ε else 0) := by
  rw [Digraph.divergence_eq]
  have hs (t : A → V) :
      (∑ a : A, if t a = z then BoundedSpec.step ε r.val a else 0) =
        if t r.val.1 = z then (if r.val.2 then ε else -ε) else 0 := by
    rw [Finset.sum_eq_single r.val.1]
    · simp [BoundedSpec.step]
    · intro a _ ha
      simp [BoundedSpec.step, ha]
    · simp
  rw [hs, hs]
  cases hd : r.val.2 <;> simp only [BoundedSpec.graph, hd,
    Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> ring

theorem divergence_adjustment (G : Digraph V A) (lo hi f : A → ℝ) {x y : V}
    (p : Walk (BoundedSpec.graph G lo hi f) x y) (ε : ℝ) (z : V) :
    G.divergence (BoundedSpec.adjustment ε (p.arcs.map Subtype.val)) z =
      (if x = z then ε else 0) - (if y = z then ε else 0) := by
  induction p with
  | nil =>
    change G.divergence (fun _ => 0) z = _
    simp [Digraph.divergence_eq]
  | @cons x w y a p ih =>
    change G.divergence (fun b => BoundedSpec.step ε a.val.val b +
      BoundedSpec.adjustment ε (p.arcs.map Subtype.val) b) z = _
    rw [divergence_add, divergence_step, ih, a.property.1, a.property.2]
    ring

theorem augment_divergence : BoundedSpec.augment_divergence.{u,v} := by
  intro V A _ _ G lo hi f x y p ε z
  change G.divergence (fun a => f a +
    BoundedSpec.adjustment ε (p.arcs.map Subtype.val) a) z = _
  rw [divergence_add, divergence_adjustment]

/-- The tails in a walk are exactly its vertices with the final vertex removed. -/
theorem walk_tails {G : Digraph V A} {x y : V} (p : Walk G x y) :
    p.arcs.map G.tail = p.vertices.dropLast := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    obtain ⟨l, hl⟩ := p.vertices_eq_cons
    simp only [Walk.arcs_cons, List.map_cons, a.property.1, Walk.vertices_cons,
      hl, List.dropLast_cons_cons] at *
    rw [ih]

theorem path_arcs_nodup {G : Digraph V A} {x y : V} (p : Walk G x y)
    (hp : p.IsPath) : p.arcs.Nodup := by
  apply List.Nodup.of_map G.tail
  rw [walk_tails]
  exact List.Nodup.sublist (List.dropLast_sublist p.vertices) hp

theorem cycle_arcs_nodup {G : Digraph V A} {x : V} (p : Walk G x x)
    (hp : p.IsCycle) : p.arcs.Nodup := by
  apply List.Nodup.of_map G.tail
  rw [walk_tails]
  exact hp.2

private theorem indicator_sum {X : Type*} [DecidableEq X] (l : List X) (hl : l.Nodup) (t : X) (ε : ℝ) :
    (l.map (fun r => if r = t then ε else 0)).sum = if t ∈ l then ε else 0 := by
  induction l with
  | nil => simp [List.map_nil, List.sum_nil]
  | cons b l ih =>
    have hn := List.nodup_cons.mp hl
    simp only [List.map_cons, List.sum_cons, ih hn.2, List.mem_cons]
    by_cases h : b = t
    · subst b
      simp [hn.1]
    · simp [h, Ne.symm h]

omit [Fintype A] in
private theorem step_eq_indicators (ε : ℝ) (r : A × Bool) (a : A) :
    BoundedSpec.step ε r a =
      (if r = (a, true) then ε else 0) - (if r = (a, false) then ε else 0) := by
  rcases r with ⟨b, d⟩
  cases d <;> by_cases h : a = b
  all_goals
    first | subst b; simp [BoundedSpec.step] | simp [BoundedSpec.step, h, Ne.symm h]

omit [Fintype A] in
/-- At most one occurrence of each signed copy; both copies are permitted. -/
theorem adjustment_eq (l : List (A × Bool)) (hl : l.Nodup) (ε : ℝ) (a : A) :
    BoundedSpec.adjustment ε l a =
      (if (a, true) ∈ l then ε else 0) - (if (a, false) ∈ l then ε else 0) := by
  unfold BoundedSpec.adjustment
  simp_rw [step_eq_indicators]
  have hs (l : List (A × Bool)) (g h : A × Bool → ℝ) :
      (l.map (fun r => g r - h r)).sum = (l.map g).sum - (l.map h).sum := by
    induction l with
    | nil => simp only [List.map_nil, List.sum_nil, sub_self]
    | cons b l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring
  rw [hs l]
  exact congrArg₂ (fun x y : ℝ => x - y)
    (indicator_sum l hl (a, true) ε) (indicator_sum l hl (a, false) ε)

omit [Fintype A] in
theorem augmentation_bounds (lo hi f : A → ℝ) (hf : BoundedSpec.WithinBounds lo hi f)
    (l : List (A × Bool)) (hl : l.Nodup) (ε : ℝ) (hε : 0 ≤ ε)
    (hc : ∀ r ∈ l, ε ≤ BoundedSpec.capacity lo hi f r) :
    BoundedSpec.WithinBounds lo hi (fun a => f a + BoundedSpec.adjustment ε l a) := by
  intro a
  change lo a ≤ f a + BoundedSpec.adjustment ε l a ∧
    f a + BoundedSpec.adjustment ε l a ≤ hi a
  rw [adjustment_eq l hl]
  by_cases hp : (a, true) ∈ l <;> by_cases hm : (a, false) ∈ l
  · simpa [hp, hm] using hf a
  · have hc' := hc (a, true) hp
    simp only [BoundedSpec.capacity, ↓reduceIte] at hc'
    simp only [hp, hm, ↓reduceIte, sub_zero]
    constructor <;> linarith [(hf a).1, (hf a).2]
  · have hc' := hc (a, false) hm
    simp only [BoundedSpec.capacity, Bool.false_eq_true, ↓reduceIte] at hc'
    simp only [hp, hm, ↓reduceIte, zero_sub]
    constructor <;> linarith [(hf a).1, (hf a).2]
  · simpa [hp, hm] using hf a

/-- An attained positive minimum exists on every nonempty residual walk. -/
theorem exists_bottleneck : BoundedSpec.exists_bottleneck.{u,v} := by
  intro V A _ _ G lo hi f x y p hp
  let s : Finset ℝ := p.arcs.toFinset.image (fun r => BoundedSpec.capacity lo hi f r.val)
  have hs : s.Nonempty := by
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil p.arcs hp
    exact ⟨_, Finset.mem_image.mpr ⟨r, List.mem_toFinset.mpr hr, rfl⟩⟩
  obtain ⟨r, hr, he⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
  refine ⟨s.min' hs, ?_, ?_, r, List.mem_toFinset.mp hr, he.symm⟩
  · rw [← he]
    exact r.property
  · intro c hc
    exact Finset.min'_le s _ (Finset.mem_image.mpr ⟨c, List.mem_toFinset.mpr hc, rfl⟩)

theorem augment_path : BoundedSpec.augment_path.{u,v} := by
  intro V A _ _ G lo hi f x y p hp hf δ ε hδ hε hεδ
  refine ⟨?_, fun z => augment_divergence G lo hi f p ε z⟩
  apply augmentation_bounds lo hi f hf (p.arcs.map Subtype.val)
    ((path_arcs_nodup p hp).map Subtype.val_injective) ε hε
  intro r hr
  obtain ⟨s, hs, he⟩ := List.mem_map.mp hr
  subst r
  exact hεδ.trans (hδ.2.1 s hs)

theorem augment_cycle : BoundedSpec.augment_cycle.{u,v} := by
  intro V A _ _ G lo hi f b x p hp hf δ ε hδ hε hεδ
  constructor
  · apply augmentation_bounds lo hi f hf.1 (p.arcs.map Subtype.val)
      ((cycle_arcs_nodup p hp).map Subtype.val_injective) ε hε
    intro r hr
    obtain ⟨s, hs, he⟩ := List.mem_map.mp hr
    subst r
    exact hεδ.trans (hδ.2.1 s hs)
  · intro z
    rw [augment_divergence, sub_self, add_zero]
    exact hf.2 z

/-- Paired copies cancel even when separated by other increments. -/
theorem paired_cancellation : BoundedSpec.paired_cancellation.{v} := by
  intro A _ a ε l₁ l₂ l₃
  funext e
  simp only [BoundedSpec.adjustment, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [BoundedSpec.step, Bool.false_eq_true, ↓reduceIte]
  by_cases h : e = a <;> simp [h] <;> ring

theorem loop_cycle : BoundedSpec.loop_cycle.{u,v} := by
  intro V A _ _ G lo hi f r h
  exact Walk.loop_isCycle _ _ _

theorem toLibraryWalk_arcs (N : Network V A) (f : A → ℝ) {x y : V}
    (p : Walk (BoundedSpec.graph N.graph (fun _ => 0) N.capacity f) x y) :
    (BoundedSpec.toLibraryWalk N f p).arcs = p.arcs.map (BoundedSpec.toLibrary N f) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change BoundedSpec.toLibrary N f a.val :: (BoundedSpec.toLibraryWalk N f p).arcs =
      BoundedSpec.toLibrary N f a.val :: p.arcs.map (BoundedSpec.toLibrary N f)
    rw [ih]

theorem library_adjustment (N : Network V A) (f : A → ℝ) (ε : ℝ)
    (l : List (BoundedSpec.ResidualArc (fun _ => 0) N.capacity f)) (a : A) :
    BoundedSpec.adjustment ε (l.map Subtype.val) a =
      ResidualSpec.adjustment ε (l.map (BoundedSpec.toLibrary N f)) a := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    change BoundedSpec.step ε b.val a + BoundedSpec.adjustment ε (l.map Subtype.val) a =
      ResidualSpec.step ε (BoundedSpec.toLibrary N f b) a +
        ResidualSpec.adjustment ε (l.map (BoundedSpec.toLibrary N f)) a
    rw [ih]
    rfl

/-- Zero lower bounds recover the existing signed copies and the existing
walk augmentation exactly, with no identification of original labels. -/
theorem zero_lower_bridge : BoundedSpec.zero_lower_bridge.{u,v} := by
  intro V A _ _ N f
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    exact Subtype.ext rfl
  · intro r
    exact Subtype.ext rfl
  · intro r
    simp [BoundedSpec.capacity, Network.residualCapacity, ResidualSpec.capacity]
  · intro r
    exact ⟨rfl, rfl⟩
  · intro x y p ε
    funext a
    change f a + BoundedSpec.adjustment ε (p.arcs.map Subtype.val) a =
      f a + ResidualSpec.adjustment ε (BoundedSpec.toLibraryWalk N f p).arcs a
    rw [toLibraryWalk_arcs, library_adjustment]
  · rfl

/-- The bounds-only cycle statement also covers nonzero initial divergences. -/
theorem augment_cycle_bounds : BoundedSpec.augment_cycle_bounds.{u,v} := by
  intro V A _ _ G lo hi f x p hp hf δ ε hδ hε hεδ
  exact augment_cycle G lo hi f (G.divergence f) p hp
    ⟨hf, fun _ => rfl⟩ δ ε hδ hε hεδ

theorem cycle_bottleneck : BoundedSpec.cycle_bottleneck.{u,v} := by
  intro V A _ _ G lo hi f x p hp
  apply exists_bottleneck G lo hi f p
  intro h
  have hlen : p.length = 0 := by rw [Walk.length_eq_arcs_length, h]; rfl
  exact (Nat.ne_of_gt hp.1) hlen

end P205.Networks
