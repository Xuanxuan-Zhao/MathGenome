import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Directed.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Foundations
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith

/-! W44: finite real networks on the shared directed multigraph interface.
Loop deletion preserves all attainable signed values and maximum flows. -/

open scoped BigOperators
universe u v
namespace FiniteCombinatorics.Graph.Flows
open FiniteCombinatorics.Directed
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

def Network.Feasible (N : Network V A) (f : A → ℝ) : Prop := Spec.feasible N f

def Flow (N : Network V A) : Type v := Spec.flow N

noncomputable def Network.value (N : Network V A) (f : A → ℝ) : ℝ := Spec.value N f

def Network.IsCut (N : Network V A) (S : Set V) : Prop := Spec.isCut N S

def Cut (N : Network V A) : Type u := Spec.cut N

noncomputable def Network.outgoing (N : Network V A) (S : Set V) : Finset A := Spec.outgoing N S

noncomputable def Network.incoming (N : Network V A) (S : Set V) : Finset A := Spec.incoming N S

noncomputable def Network.cutCapacity (N : Network V A) (S : Set V) : ℝ := Spec.cutCapacity N S

def Network.withoutLoops (N : Network V A) : Network V N.NonloopArc := Spec.withoutLoops N

def Network.restrictLoad (N : Network V A) (f : A → ℝ) : N.NonloopArc → ℝ := Spec.restrictLoad N f

noncomputable def Network.extendLoad (N : Network V A) (g : N.NonloopArc → ℝ) : A → ℝ := Spec.extendLoad N g

def Network.attainableValues (N : Network V A) : Set ℝ := Spec.attainableValues N

def Network.IsMaximum (N : Network V A) (f : A → ℝ) : Prop := Spec.isMaximum N f

namespace Network

variable (N : Network V A)

@[simp] theorem feasible_iff (f : A → ℝ) : N.Feasible f ↔
    (∀ a, 0 ≤ f a ∧ f a ≤ N.capacity a) ∧
    ∀ x, x ≠ N.source → x ≠ N.sink → N.graph.divergence f x = 0 := Iff.rfl

@[simp] theorem isCut_iff (S : Set V) : N.IsCut S ↔ N.source ∈ S ∧ N.sink ∉ S := Iff.rfl

@[simp] theorem value_eq (f : A → ℝ) : N.value f = N.graph.divergence f N.source := rfl

@[simp] theorem mem_outgoing (S : Set V) (a : A) :
    a ∈ N.outgoing S ↔ N.graph.tail a ∈ S ∧ N.graph.head a ∉ S := by
  classical
  simp [outgoing, Spec.outgoing]

@[simp] theorem mem_incoming (S : Set V) (a : A) :
    a ∈ N.incoming S ↔ N.graph.tail a ∉ S ∧ N.graph.head a ∈ S := by
  classical
  simp [incoming, Spec.incoming]

@[simp] theorem cutCapacity_eq (S : Set V) :
    N.cutCapacity S = ∑ a ∈ N.outgoing S, N.capacity a := rfl

/-- Each original arc contributes its load once with each sign. -/
theorem sum_divergence (f : A → ℝ) : ∑ x : V, N.graph.divergence f x = 0 := by
  classical
  simp_rw [Digraph.divergence_eq]
  rw [Finset.sum_sub_distrib]
  have ho : (∑ x : V, ∑ a : A, if N.graph.tail a = x then f a else 0) = ∑ a, f a := by
    rw [Finset.sum_comm]
    simp
  have hi : (∑ x : V, ∑ a : A, if N.graph.head a = x then f a else 0) = ∑ a, f a := by
    rw [Finset.sum_comm]
    simp
  rw [ho, hi, sub_self]

/-- The only possible nonzero divergences are at the two distinguished vertices. -/
theorem sink_divergence (f : A → ℝ) (hf : N.Feasible f) :
    N.graph.divergence f N.sink = -N.value f := by
  classical
  have hsum : (∑ x : V, N.graph.divergence f x) =
      N.graph.divergence f N.source + N.graph.divergence f N.sink := by
    calc
      _ = ∑ x ∈ ({N.source, N.sink} : Finset V), N.graph.divergence f x := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro x _ hx
        have hx' : x ≠ N.source ∧ x ≠ N.sink := by simpa using hx
        exact hf.2 x hx'.1 hx'.2
      _ = _ := by simp [N.source_ne_sink]
  rw [N.sum_divergence] at hsum
  rw [value_eq]
  linarith

@[simp] theorem zero_feasible : N.Feasible (fun _ => 0) := by
  constructor
  · intro a
    exact ⟨le_refl 0, N.capacity_nonneg a⟩
  · intro x _ _
    change N.graph.divergence (fun _ => 0) x = 0
    simp [Digraph.divergence_eq]

@[simp] theorem value_zero : N.value (fun _ => 0) = 0 := by
  simp [value_eq, Digraph.divergence_eq]

theorem loop_not_outgoing (a : A) (ha : N.graph.tail a = N.graph.head a) (S : Set V) :
    a ∉ N.outgoing S := by
  simp [mem_outgoing, ha]

theorem loop_not_incoming (a : A) (ha : N.graph.tail a = N.graph.head a) (S : Set V) :
    a ∉ N.incoming S := by
  simp [mem_incoming, ha]

open scoped Classical in
/-- Express divergence as a sum of per-arc contributions. -/
theorem divergence_eq_sum (f : A → ℝ) (x : V) :
    N.graph.divergence f x = ∑ a : A,
      ((if N.graph.tail a = x then f a else 0) -
       (if N.graph.head a = x then f a else 0)) := by
  rw [Digraph.divergence_eq, Finset.sum_sub_distrib]

@[simp] theorem withoutLoops_no_loop (a : N.NonloopArc) :
    N.withoutLoops.graph.tail a ≠ N.withoutLoops.graph.head a := a.property

/-- Deleting loops preserves divergence even for arbitrary signed arc loads. -/
theorem divergence_restrict (f : A → ℝ) (x : V) :
    N.withoutLoops.graph.divergence (N.restrictLoad f) x = N.graph.divergence f x := by
  classical
  rw [N.withoutLoops.divergence_eq_sum, N.divergence_eq_sum]
  symm
  apply Finset.sum_congr_set {a : A | N.graph.tail a ≠ N.graph.head a}
  · intro a ha
    rfl
  · intro a ha
    have heq : N.graph.tail a = N.graph.head a := by simpa using ha
    simp [heq]

/-- Any changes supported on loops leave every divergence unchanged. -/
theorem divergence_congr_nonloops (f g : A → ℝ)
    (h : ∀ a, N.graph.tail a ≠ N.graph.head a → f a = g a) (x : V) :
    N.graph.divergence f x = N.graph.divergence g x := by
  rw [← N.divergence_restrict f, ← N.divergence_restrict g]
  congr 1
  funext a
  exact h a.val a.property

@[simp] theorem restrict_extend (g : N.NonloopArc → ℝ) :
    N.restrictLoad (N.extendLoad g) = g := by
  classical
  funext a
  rcases a with ⟨a, ha⟩
  change (if h : N.graph.tail a ≠ N.graph.head a then g ⟨a, h⟩ else 0) = g ⟨a, ha⟩
  rw [dite_eq_left ha]

@[simp] theorem extend_eq_zero_of_loop (g : N.NonloopArc → ℝ) (a : A)
    (ha : N.graph.tail a = N.graph.head a) : N.extendLoad g a = 0 := by
  classical
  simp [extendLoad, Spec.extendLoad, ha]

theorem divergence_extend (g : N.NonloopArc → ℝ) (x : V) :
    N.graph.divergence (N.extendLoad g) x = N.withoutLoops.graph.divergence g x := by
  rw [← N.divergence_restrict, N.restrict_extend]

theorem feasible_restrict (f : A → ℝ) (hf : N.Feasible f) :
    N.withoutLoops.Feasible (N.restrictLoad f) := by
  constructor
  · intro a
    exact hf.1 a.val
  · intro x hs ht
    change N.withoutLoops.graph.divergence (N.restrictLoad f) x = 0
    rw [N.divergence_restrict]
    exact hf.2 x hs ht

theorem feasible_extend_iff (g : N.NonloopArc → ℝ) :
    N.Feasible (N.extendLoad g) ↔ N.withoutLoops.Feasible g := by
  classical
  constructor
  · intro hf
    have h := N.feasible_restrict (N.extendLoad g) hf
    rwa [N.restrict_extend] at h
  · intro hg
    constructor
    · intro a
      by_cases ha : N.graph.tail a ≠ N.graph.head a
      · simp only [extendLoad, Spec.extendLoad, dite_eq_left ha]
        exact hg.1 ⟨a, ha⟩
      · simp only [extendLoad, Spec.extendLoad, dite_eq_right ha]
        exact ⟨le_refl 0, N.capacity_nonneg a⟩
    · intro x hs ht
      change N.graph.divergence (N.extendLoad g) x = 0
      rw [N.divergence_extend]
      exact hg.2 x hs ht

@[simp] theorem value_restrict (f : A → ℝ) :
    N.withoutLoops.value (N.restrictLoad f) = N.value f :=
  N.divergence_restrict f N.source

@[simp] theorem value_extend (g : N.NonloopArc → ℝ) :
    N.value (N.extendLoad g) = N.withoutLoops.value g :=
  N.divergence_extend g N.source

open scoped Classical in
/-- Only outgoing crossing arcs enter the capacity sum. -/
theorem cutCapacity_eq_sum (S : Set V) :
    N.cutCapacity S = ∑ a : A,
      if N.graph.tail a ∈ S ∧ N.graph.head a ∉ S then N.capacity a else 0 := by
  classical
  simp [cutCapacity, Spec.cutCapacity, Spec.outgoing, Finset.sum_filter]

/-- Every cut keeps exactly its capacity when loops are deleted. -/
theorem cutCapacity_withoutLoops (S : Set V) :
    N.withoutLoops.cutCapacity S = N.cutCapacity S := by
  classical
  rw [N.withoutLoops.cutCapacity_eq_sum, N.cutCapacity_eq_sum]
  symm
  apply Finset.sum_congr_set {a : A | N.graph.tail a ≠ N.graph.head a}
  · intro a ha
    rfl
  · intro a ha
    have heq : N.graph.tail a = N.graph.head a := by simpa using ha
    simp [heq]

/-- The complete feasible objective sets agree, including negative values. -/
theorem attainableValues_withoutLoops :
    N.withoutLoops.attainableValues = N.attainableValues := by
  ext r
  constructor
  · rintro ⟨g, hg, hv⟩
    exact ⟨N.extendLoad g, (N.feasible_extend_iff g).2 hg, (N.value_extend g).trans hv⟩
  · rintro ⟨f, hf, hv⟩
    exact ⟨N.restrictLoad f, N.feasible_restrict f hf, (N.value_restrict f).trans hv⟩

/-- Restriction preserves and reflects maximality for every original feasible flow. -/
theorem maximum_restrict_iff (f : A → ℝ) (hf : N.Feasible f) :
    N.withoutLoops.IsMaximum (N.restrictLoad f) ↔ N.IsMaximum f := by
  constructor
  · intro h
    refine ⟨hf, fun g hg => ?_⟩
    have hle := h.2 (N.restrictLoad g) (N.feasible_restrict g hg)
    change N.withoutLoops.value (N.restrictLoad g) ≤ N.withoutLoops.value (N.restrictLoad f) at hle
    change N.value g ≤ N.value f
    simpa only [value_restrict] using hle
  · intro h
    refine ⟨N.feasible_restrict f hf, fun g hg => ?_⟩
    have hle := h.2 (N.extendLoad g) ((N.feasible_extend_iff g).2 hg)
    change N.value (N.extendLoad g) ≤ N.value f at hle
    change N.withoutLoops.value g ≤ N.withoutLoops.value (N.restrictLoad f)
    simpa only [value_extend, value_restrict] using hle

/-- A reduced maximum extends to an original maximum by zero on all deleted loops. -/
theorem maximum_extend_iff (g : N.NonloopArc → ℝ) :
    N.IsMaximum (N.extendLoad g) ↔ N.withoutLoops.IsMaximum g := by
  constructor
  · intro h
    have hm := (N.maximum_restrict_iff _ h.1).2 h
    rwa [N.restrict_extend] at hm
  · intro h
    have hf := (N.feasible_extend_iff g).2 h.1
    apply (N.maximum_restrict_iff _ hf).1
    simpa only [restrict_extend] using h

end Network
end FiniteCombinatorics.Graph.Flows
