import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Augmentation
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

open scoped BigOperators Classical
universe u v
namespace FiniteCombinatorics.Graph.Flows
open FiniteCombinatorics.Directed
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

def Network.residualCapacity (N : Network V A) (f : A → ℝ) (b : A × Bool) : ℝ :=
  ResidualSpec.capacity N f b

def Network.residualGraph (N : Network V A) (f : A → ℝ) : Digraph V (N.ResidualArc f) :=
  ResidualSpec.graph N f

noncomputable def Network.augment (N : Network V A) (f : A → ℝ) {x y : V}
    (p : Walk (N.residualGraph f) x y) (ε : ℝ) : A → ℝ :=
  ResidualSpec.augment N f p ε

namespace Augmentation

variable {G : Digraph V A} {x y z : V}

private theorem start_mem (p : Walk G x y) : x ∈ p.vertices := by
  obtain ⟨l, hl⟩ := p.vertices_eq_cons
  simp [hl]

private theorem endpoints_mem (p : Walk G x y) {a : A} (ha : a ∈ p.arcs) :
    G.tail a ∈ p.vertices ∧ G.head a ∈ p.vertices := by
  induction p with
  | nil => simp at ha
  | @cons x y z b p ih =>
    simp only [Walk.arcs_cons, List.mem_cons] at ha
    rcases ha with rfl | ha
    · constructor
      · simp [b.property.1]
      · simp only [Walk.vertices_cons, List.mem_cons]
        exact Or.inr (b.property.2.symm ▸ start_mem p)
    · obtain ⟨ht, hh⟩ := ih ha
      exact ⟨List.mem_cons_of_mem _ ht, List.mem_cons_of_mem _ hh⟩

private theorem suffix_path (p : Walk G x y) (hp : p.IsPath)
    (z : V) (hz : z ∈ p.vertices) : ∃ q : Walk G z y, q.IsPath := by
  induction p with
  | nil x =>
    have : z = x := by simpa using hz
    subst z
    exact ⟨.nil x, Walk.nil_isPath G x⟩
  | @cons x w y a p ih =>
    change (x :: p.vertices).Nodup at hp
    rcases List.mem_cons.mp hz with h | h
    · subst z
      exact ⟨.cons a p, hp⟩
    · exact ih hp.of_cons h

/-- Remove repeated-vertex segments without forgetting original arc data. -/
theorem exists_path (p : Walk G x y) : ∃ q : Walk G x y, q.IsPath := by
  classical
  induction p with
  | nil x => exact ⟨.nil x, Walk.nil_isPath G x⟩
  | @cons x w y a p ih =>
    obtain ⟨q, hq⟩ := ih
    by_cases hx : x ∈ q.vertices
    · exact suffix_path q hq x hx
    · refine ⟨.cons a q, ?_⟩
      exact List.nodup_cons.mpr ⟨hx, hq⟩

variable (N : Network V A) (f : A → ℝ)

private theorem original_endpoints (b c : N.ResidualArc f)
    (h : b.original = c.original) :
    (N.residualGraph f).tail b = (N.residualGraph f).tail c ∨
    (N.residualGraph f).tail b = (N.residualGraph f).head c := by
  change (if b.forward then N.graph.tail b.original else N.graph.head b.original) = _ ∨ _
  cases hb : b.forward <;> cases hc : c.forward <;>
    simp [Network.residualGraph, ResidualSpec.graph, hb, hc, h]

/-- Simplicity excludes both copies of an original, as well as repeated copies. -/
theorem originals_nodup {x y : V} (p : Walk (N.residualGraph f) x y)
    (hp : p.IsPath) : (p.arcs.map Network.ResidualArc.original).Nodup := by
  induction p with
  | nil => simp
  | @cons x w y a p ih =>
    change (x :: p.vertices).Nodup at hp
    simp only [Walk.arcs_cons, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hp.of_cons⟩
    intro h
    obtain ⟨b, hb, heq⟩ := List.mem_map.mp h
    obtain ⟨ht, hh⟩ := endpoints_mem p hb
    have he := original_endpoints N f a.val b heq.symm
    rcases he with he | he
    · exact (List.nodup_cons.mp hp).1 ((a.property.1 ▸ he) ▸ ht)
    · exact (List.nodup_cons.mp hp).1 ((a.property.1 ▸ he) ▸ hh)

private theorem no_residual_loop {x y : V} (p : Walk (N.residualGraph f) x y)
    (hp : p.IsPath) {b : N.ResidualArc f} (hb : b ∈ p.arcs) :
    (N.residualGraph f).tail b ≠ (N.residualGraph f).head b := by
  induction p with
  | nil => simp at hb
  | @cons x w y a p ih =>
    change (x :: p.vertices).Nodup at hp
    rcases List.mem_cons.mp hb with h | h
    · subst b
      intro heq
      have hxw : x = w := a.property.1.symm.trans (heq.trans a.property.2)
      exact (List.nodup_cons.mp hp).1 (hxw ▸ start_mem p)
    · exact ih hp.of_cons h

theorem no_original_loop {x y : V} (p : Walk (N.residualGraph f) x y)
    (hp : p.IsPath) {b : N.ResidualArc f} (hb : b ∈ p.arcs) :
    N.graph.tail b.original ≠ N.graph.head b.original := by
  intro he
  apply no_residual_loop N f p hp hb
  change (if b.forward then _ else _) = (if b.forward then _ else _)
  cases b.forward <;> simp [he]


private theorem adjustment_cons (ε : ℝ) (b : N.ResidualArc f)
    (l : List (N.ResidualArc f)) (a : A) :
    ResidualSpec.adjustment ε (b :: l) a =
      ResidualSpec.step ε b a + ResidualSpec.adjustment ε l a := rfl

private theorem adjustment_zero (ε : ℝ) (l : List (N.ResidualArc f)) (a : A)
    (ha : a ∉ l.map Network.ResidualArc.original) :
    ResidualSpec.adjustment ε l a = 0 := by
  classical
  apply List.sum_eq_zero
  intro r hr
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
  have hne : a ≠ b.original := by
    intro h
    exact ha (List.mem_map.mpr ⟨b, hb, h.symm⟩)
  simp [ResidualSpec.step, hne]

private theorem augmentation_bounds (hf : N.Feasible f) (ε : ℝ) (hε : 0 ≤ ε)
    (l : List (N.ResidualArc f))
    (hl : (l.map Network.ResidualArc.original).Nodup)
    (hc : ∀ b ∈ l, ε ≤ ResidualSpec.capacity N f b.val) (a : A) :
    0 ≤ f a + ResidualSpec.adjustment ε l a ∧
      f a + ResidualSpec.adjustment ε l a ≤ N.capacity a := by
  classical
  induction l with
  | nil => simpa [ResidualSpec.adjustment] using hf.1 a
  | cons b l ih =>
    have hn := List.nodup_cons.mp hl
    have ht := ih hn.2 (fun c h => hc c (List.mem_cons_of_mem _ h))
    rw [adjustment_cons]
    by_cases ha : a = b.original
    · subst a
      rw [adjustment_zero N f ε l b.original hn.1]
      have hb := hc b (by simp)
      change ε ≤ (if b.forward then N.capacity b.original - f b.original
        else f b.original) at hb
      have hf' := hf.1 b.original
      cases hd : b.forward <;> simp [ResidualSpec.step, hd] at * <;> constructor <;> linarith
    · simpa [ResidualSpec.step, ha] using ht

private theorem divergence_add (g h : A → ℝ) (w : V) :
    N.graph.divergence (fun a => g a + h a) w =
      N.graph.divergence g w + N.graph.divergence h w := by
  classical
  simp only [Digraph.divergence_eq]
  have ho : (∑ a : A, if N.graph.tail a = w then g a + h a else 0) =
      (∑ a : A, if N.graph.tail a = w then g a else 0) +
      ∑ a : A, if N.graph.tail a = w then h a else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have hi : (∑ a : A, if N.graph.head a = w then g a + h a else 0) =
      (∑ a : A, if N.graph.head a = w then g a else 0) +
      ∑ a : A, if N.graph.head a = w then h a else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [ho, hi]
  ring

private theorem divergence_step (ε : ℝ) (b : N.ResidualArc f) (w : V) :
    N.graph.divergence (ResidualSpec.step ε b) w =
      (if (N.residualGraph f).tail b = w then ε else 0) -
      (if (N.residualGraph f).head b = w then ε else 0) := by
  classical
  rw [Digraph.divergence_eq]
  have hs (g : A → V) :
      (∑ a : A, if g a = w then ResidualSpec.step ε b a else 0) =
        if g b.original = w then (if b.forward then ε else -ε) else 0 := by
    rw [Finset.sum_eq_single b.original]
    · simp [ResidualSpec.step]
    · intro a _ ha
      simp [ResidualSpec.step, ha]
    · simp
  rw [hs, hs]
  cases hd : b.forward <;>
    simp only [Network.residualGraph, ResidualSpec.graph, hd, Bool.false_eq_true,
      ↓reduceIte]; split_ifs <;> ring

/-- Signed changes telescope along any residual walk; simplicity is unnecessary
for this identity, and backward copies contribute with reversed incidence. -/
theorem divergence_adjustment {x y : V} (p : Walk (N.residualGraph f) x y)
    (ε : ℝ) (w : V) :
    N.graph.divergence (ResidualSpec.adjustment ε p.arcs) w =
      (if x = w then ε else 0) - (if y = w then ε else 0) := by
  classical
  induction p with
  | nil => simp [ResidualSpec.adjustment, Digraph.divergence_eq]
  | @cons x z y a p ih =>
    change N.graph.divergence
      (fun b => ResidualSpec.step ε a.val b + ResidualSpec.adjustment ε p.arcs b) w = _
    rw [divergence_add, divergence_step, ih, a.property.1, a.property.2]
    ring

theorem divergence_augment {x y : V} (p : Walk (N.residualGraph f) x y)
    (ε : ℝ) (w : V) :
    N.graph.divergence (N.augment f p ε) w = N.graph.divergence f w +
      ((if x = w then ε else 0) - (if y = w then ε else 0)) := by
  change N.graph.divergence (fun a => f a + ResidualSpec.adjustment ε p.arcs a) w = _
  rw [divergence_add, divergence_adjustment]

private theorem exists_bottleneck {x y : V} (p : Walk (N.residualGraph f) x y)
    (hxy : x ≠ y) : ∃ ε, ResidualSpec.bottleneck N f p ε := by
  classical
  have hl : p.arcs ≠ [] := by
    intro h
    cases p with
    | nil => exact hxy rfl
    | cons a p => simp at h
  let s : Finset ℝ := p.arcs.toFinset.image (fun b => ResidualSpec.capacity N f b.val)
  have hs : s.Nonempty := by
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil p.arcs hl
    exact ⟨_, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb, rfl⟩⟩
  obtain ⟨b, hb, he⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
  refine ⟨s.min' hs, ?_, ?_, b, List.mem_toFinset.mp hb, he.symm⟩
  · rw [← he]
    exact b.property
  · intro c hc
    exact Finset.min'_le s _ (Finset.mem_image.mpr ⟨c, List.mem_toFinset.mpr hc, rfl⟩)

/-- Augment by the attained positive minimum residual capacity. -/
theorem augment_feasible {x y : V} (p : Walk (N.residualGraph f) x y)
    (hp : p.IsPath) (hf : N.Feasible f) (hx : x = N.source) (hy : y = N.sink)
    (ε : ℝ) (hε : ResidualSpec.bottleneck N f p ε) :
    N.Feasible (N.augment f p ε) ∧ N.value (N.augment f p ε) = N.value f + ε := by
  classical
  subst x
  subst y
  constructor
  · constructor
    · exact augmentation_bounds N f hf ε hε.1.le p.arcs
        (originals_nodup N f p hp) hε.2.1
    · intro w hs ht
      change N.graph.divergence (N.augment f p ε) w = 0
      rw [divergence_augment]
      have hw : N.graph.divergence f w = 0 := hf.2 w hs ht
      simp [Ne.symm hs, Ne.symm ht, hw]
  · rw [Network.value_eq, divergence_augment, Network.value_eq]
    simp [Ne.symm N.source_ne_sink]

end Augmentation

/-- Source `p204:residual-path`, first assertion, with all witnesses exposed. -/
theorem Network.residual_augmentation : ResidualSpec.augmentation.{u,v} := by
  intro V A _ _ N f hf hwalk
  obtain ⟨p⟩ := hwalk
  obtain ⟨q, hq⟩ := Augmentation.exists_path p
  obtain ⟨ε, hε⟩ := Augmentation.exists_bottleneck N f q N.source_ne_sink
  obtain ⟨hfeas, hval⟩ := Augmentation.augment_feasible N f q hq hf rfl rfl ε hε
  exact ⟨q, hq, Augmentation.originals_nodup N f q hq,
    fun b hb => Augmentation.no_original_loop N f q hq hb, ε, hε, hfeas, hval⟩

end FiniteCombinatorics.Graph.Flows
