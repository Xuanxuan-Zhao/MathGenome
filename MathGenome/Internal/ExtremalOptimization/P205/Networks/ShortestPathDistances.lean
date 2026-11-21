import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ShortestPathDistances
import MathGenome.Internal.ExtremalOptimization.P205.Networks.ResidualFoundation
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

open scoped Classical
universe u v
namespace P205.Networks
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows

noncomputable def distance := @DistanceSpec.distance

def IsShortest := @DistanceSpec.IsShortest

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

namespace ShortestDistances

variable {G : Digraph V A} {s t : V}

theorem distance_le_walk (p : Walk G s t) : DistanceSpec.distance G s t ≤ p.length :=
  iInf_le _ p

@[simp] theorem distance_self (G : Digraph V A) (s : V) : DistanceSpec.distance G s s = 0 :=
  le_antisymm (distance_le_walk (.nil s)) bot_le

/-- Split at an occurrence of a labelled arc, preserving its actual endpoints. -/
theorem split_at_arc (p : Walk G s t) {r : A} (hr : r ∈ p.arcs) :
    ∃ (q : Walk G s (G.tail r)) (z : Walk G (G.head r) t),
      p.length = q.length + 1 + z.length := by
  induction p with
  | nil => simp at hr
  | @cons x y z a p ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst r
      rcases a with ⟨a, ht, hh⟩
      cases ht
      cases hh
      refine ⟨.nil _, p, ?_⟩
      change p.length + 1 = 0 + 1 + p.length
      omega
    · obtain ⟨q, z, hz⟩ := ih h
      exact ⟨.cons a q, z, by simp only [Walk.length_cons]; omega⟩

/-- On a shortest walk the old distance cannot decrease along any selected arc.
This weaker form of the familiar level equality suffices for monotonicity. -/
theorem selected_arc_bound (p : Walk G s t) (hp : DistanceSpec.IsShortest p)
    {r : A} (hr : r ∈ p.arcs) :
    DistanceSpec.distance G s (G.tail r) ≤ DistanceSpec.distance G s (G.head r) := by
  obtain ⟨q, z, hz⟩ := split_at_arc p hr
  apply (distance_le_walk q).trans
  apply le_iInf
  intro q'
  have h := hp (q'.append z)
  rw [Walk.length_append] at h
  have hle : q.length ≤ q'.length := by omega
  exact_mod_cast hle

/-- The usual triangle inequality, including an unreachable tail. -/
theorem arc_bound (G : Digraph V A) (s : V) (r : A) :
    DistanceSpec.distance G s (G.head r) ≤ DistanceSpec.distance G s (G.tail r) + 1 := by
  unfold DistanceSpec.distance
  rw [ENat.iInf_add]
  apply le_iInf
  intro p
  have h := distance_le_walk (p.append (Walk.single G r))
  change DistanceSpec.distance G s (G.head r) ≤ _
  simpa only [Walk.length_append, Walk.length_single, Nat.cast_add, Nat.cast_one] using h

/-- A potential satisfying the unit edge inequalities bounds every walk. -/
theorem walk_bound {B : Type*} [Fintype B] (H : Digraph V B) (d : V → ℕ∞)
    (hd : ∀ r, d (H.head r) ≤ d (H.tail r) + 1) {x y : V} (p : Walk H x y) :
    d y ≤ d x + p.length := by
  induction p with
  | nil => simp
  | @cons x z y a p ih =>
    have h := hd a.val
    rw [a.property.1, a.property.2] at h
    calc
      d y ≤ d z + p.length := ih
      _ ≤ (d x + 1) + p.length := add_le_add h le_rfl
      _ = d x + (Walk.cons a p).length := by
        simp only [Walk.length_cons, Nat.cast_add, Nat.cast_one]
        ac_rfl

theorem distance_mono_of_arc_bound {B : Type*} [Fintype B] (H : Digraph V B)
    (h : ∀ r, DistanceSpec.distance G s (H.head r) ≤
      DistanceSpec.distance G s (H.tail r) + 1) :
    ∀ x, DistanceSpec.distance G s x ≤ DistanceSpec.distance H s x := by
  intro x
  apply le_iInf
  intro p
  simpa only [distance_self, zero_add] using walk_bound H (DistanceSpec.distance G s) h p

/-- A newly positive signed copy must be paired with a used copy. Labels are
retained even in the presence of parallel and opposite original arcs. -/
theorem new_copy (G : Digraph V A) (lo hi f : A → ℝ) {x y : V}
    (p : Walk (BoundedSpec.graph G lo hi f) x y) (hp : p.IsPath)
    (ε : ℝ) (hε : 0 ≤ ε)
    (r : BoundedSpec.ResidualArc lo hi (BoundedSpec.augment G lo hi f p ε)) :
    (∃ q : BoundedSpec.ResidualArc lo hi f, q.val = r.val) ∨
      ∃ q ∈ p.arcs, q.val = (r.val.1, !r.val.2) := by
  by_cases hold : 0 < BoundedSpec.capacity lo hi f r.val
  · exact Or.inl ⟨⟨r.val, hold⟩, rfl⟩
  right
  have hn : (p.arcs.map Subtype.val).Nodup :=
    (path_arcs_nodup p hp).map Subtype.val_injective
  have hnew := r.property
  change 0 < BoundedSpec.capacity lo hi
    (fun a => f a + BoundedSpec.adjustment ε (p.arcs.map Subtype.val) a) r.val at hnew
  have hm : (r.val.1, !r.val.2) ∈ p.arcs.map Subtype.val := by
    by_contra hnone
    rw [BoundedSpec.capacity, adjustment_eq _ hn] at hnew
    cases hd : r.val.2
    · simp only [hd, Bool.not_false] at hnone
      simp only [hd, Bool.false_eq_true, ↓reduceIte, hnone, zero_sub] at hnew
      simp only [BoundedSpec.capacity, hd, Bool.false_eq_true, ↓reduceIte] at hold
      split_ifs at hnew <;> linarith
    · simp only [hd, Bool.not_true] at hnone
      simp only [hd, ↓reduceIte, hnone, sub_zero] at hnew
      simp only [BoundedSpec.capacity, hd, ↓reduceIte] at hold
      split_ifs at hnew <;> linarith
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  exact ⟨q, hq, he⟩

/-- The old distance is a unit-edge potential on the entire new residual graph. -/
theorem augmented_arc_bound (G : Digraph V A) (lo hi f : A → ℝ) {s t : V}
    (p : Walk (BoundedSpec.graph G lo hi f) s t) (hp : p.IsPath)
    (hshort : DistanceSpec.IsShortest p) (ε : ℝ) (hε : 0 ≤ ε)
    (r : BoundedSpec.ResidualArc lo hi (BoundedSpec.augment G lo hi f p ε)) :
    DistanceSpec.distance (BoundedSpec.graph G lo hi f) s
      ((BoundedSpec.graph G lo hi (BoundedSpec.augment G lo hi f p ε)).head r) ≤
    DistanceSpec.distance (BoundedSpec.graph G lo hi f) s
      ((BoundedSpec.graph G lo hi (BoundedSpec.augment G lo hi f p ε)).tail r) + 1 := by
  rcases new_copy G lo hi f p hp ε hε r with ⟨q, hq⟩ | ⟨q, hq, he⟩
  · have h := arc_bound (BoundedSpec.graph G lo hi f) s q
    simpa only [BoundedSpec.graph, hq] using h
  · have h := selected_arc_bound p hshort hq
    have hh : (BoundedSpec.graph G lo hi (BoundedSpec.augment G lo hi f p ε)).head r =
        (BoundedSpec.graph G lo hi f).tail q := by
      simp only [BoundedSpec.graph, he]
      cases r.val.2 <;> rfl
    have ht : (BoundedSpec.graph G lo hi (BoundedSpec.augment G lo hi f p ε)).tail r =
        (BoundedSpec.graph G lo hi f).head q := by
      simp only [BoundedSpec.graph, he]
      cases r.val.2 <;> rfl
    rw [hh, ht]
    exact h.trans (le_add_right le_rfl)

/-- In fact every nonnegative augmentation along a shortest simple walk has
nondecreasing residual distances; bottleneck feasibility is needed only by the
algorithm, not by this stronger distance statement. -/
theorem shortest_augmentation_distance_mono (G : Digraph V A) (lo hi f : A → ℝ)
    {s t : V} (p : Walk (BoundedSpec.graph G lo hi f) s t) (hp : p.IsPath)
    (hshort : DistanceSpec.IsShortest p) (ε : ℝ) (hε : 0 ≤ ε) (x : V) :
    DistanceSpec.distance (BoundedSpec.graph G lo hi f) s x ≤
      DistanceSpec.distance
        (BoundedSpec.graph G lo hi (BoundedSpec.augment G lo hi f p ε)) s x := by
  exact distance_mono_of_arc_bound _ (augmented_arc_bound G lo hi f p hp hshort ε hε) x

end ShortestDistances

/-- W37 distance monotonicity at any feasible real flow and any shortest path. -/
theorem residual_distance_mono : DistanceSpec.residual_distance_mono.{u,v} := by
  intro V A _ _ N f _ p hp hshort δ hδ x
  exact ShortestDistances.shortest_augmentation_distance_mono N.graph
    (fun _ => 0) N.capacity f p hp hshort δ (le_of_lt hδ.1) x

end P205.Networks
