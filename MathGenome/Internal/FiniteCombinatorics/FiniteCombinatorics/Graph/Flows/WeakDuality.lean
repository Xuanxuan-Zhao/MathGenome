import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.WeakDuality
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! Weak flow–cut duality (W45), including the equality characterization. -/

open scoped BigOperators
universe u v
namespace FiniteCombinatorics.Graph.Flows.Network
open FiniteCombinatorics.Directed
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]
variable (N : Network V A)

open scoped Classical in
/-- Internal arcs cancel when divergence is summed over any vertex set.
No sign, feasibility, or cut hypotheses are needed for this identity. -/
theorem sum_divergence_set (f : A → ℝ) (S : Set V) :
    (∑ x ∈ Finset.univ.filter (fun x => x ∈ S), N.graph.divergence f x) =
      (∑ a ∈ N.outgoing S, f a) - ∑ a ∈ N.incoming S, f a := by
  classical
  have hs (b : A → V) :
      (∑ x ∈ Finset.univ.filter (fun x => x ∈ S),
        ∑ a : A, if b a = x then f a else 0) =
      ∑ a : A, if b a ∈ S then f a else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp
  simp_rw [Digraph.divergence_eq]
  rw [Finset.sum_sub_distrib, hs N.graph.tail, hs N.graph.head]
  simp only [outgoing, incoming, Spec.outgoing, Spec.incoming, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ht : N.graph.tail a ∈ S <;>
    by_cases hh : N.graph.head a ∈ S <;> simp [ht, hh]

/-- The net flow across a cut equals the signed source divergence. -/
theorem value_eq_cut_net (f : A → ℝ) (S : Set V)
    (hf : N.Feasible f) (hS : N.IsCut S) :
    N.value f = (∑ a ∈ N.outgoing S, f a) - ∑ a ∈ N.incoming S, f a := by
  classical
  rw [← N.sum_divergence_set]
  symm
  rw [Finset.sum_eq_single N.source]
  · rfl
  · intro x hx hxs
    exact hf.2 x hxs (fun hxt => hS.2 (hxt ▸ (Finset.mem_filter.mp hx).2))
  · intro hs
    exact (hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS.1⟩)).elim

/-- The capacity minus the signed value is the sum of outgoing slacks and
incoming flows. Both families are nonnegative for a feasible flow. -/
theorem cutCapacity_sub_value (f : A → ℝ) (S : Set V)
    (hf : N.Feasible f) (hS : N.IsCut S) :
    N.cutCapacity S - N.value f =
      (∑ a ∈ N.outgoing S, (N.capacity a - f a)) + ∑ a ∈ N.incoming S, f a := by
  rw [N.value_eq_cut_net f S hf hS, N.cutCapacity_eq, Finset.sum_sub_distrib]
  linarith

/-- Every feasible flow is bounded by every s–t cut. -/
theorem weak_duality (f : A → ℝ) (S : Set V)
    (hf : N.Feasible f) (hS : N.IsCut S) : N.value f ≤ N.cutCapacity S := by
  have ho : 0 ≤ ∑ a ∈ N.outgoing S, (N.capacity a - f a) :=
    Finset.sum_nonneg (fun a _ => sub_nonneg.mpr (hf.1 a).2)
  have hi : 0 ≤ ∑ a ∈ N.incoming S, f a :=
    Finset.sum_nonneg (fun a _ => (hf.1 a).1)
  have h := N.cutCapacity_sub_value f S hf hS
  linarith

/-- Equality is equivalent to saturation on outgoing cut arcs and zero flow
on incoming cut arcs. The conditions are vacuous for empty arc families. -/
theorem value_eq_cutCapacity_iff (f : A → ℝ) (S : Set V)
    (hf : N.Feasible f) (hS : N.IsCut S) :
    N.value f = N.cutCapacity S ↔
      (∀ a ∈ N.outgoing S, f a = N.capacity a) ∧
      (∀ a ∈ N.incoming S, f a = 0) := by
  have ho : 0 ≤ ∑ a ∈ N.outgoing S, (N.capacity a - f a) :=
    Finset.sum_nonneg (fun a _ => sub_nonneg.mpr (hf.1 a).2)
  have hi : 0 ≤ ∑ a ∈ N.incoming S, f a :=
    Finset.sum_nonneg (fun a _ => (hf.1 a).1)
  have h := N.cutCapacity_sub_value f S hf hS
  constructor
  · intro heq
    have hoz : (∑ a ∈ N.outgoing S, (N.capacity a - f a)) = 0 := by linarith
    have hiz : (∑ a ∈ N.incoming S, f a) = 0 := by linarith
    constructor
    · intro a ha
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun a (_ : a ∈ N.outgoing S) => sub_nonneg.mpr (hf.1 a).2)).mp hoz a ha
      exact (sub_eq_zero.mp hz).symm
    · exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun a (_ : a ∈ N.incoming S) => (hf.1 a).1)).mp hiz
  · rintro ⟨hout, hin⟩
    have hoz : (∑ a ∈ N.outgoing S, (N.capacity a - f a)) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [hout a ha, sub_self]
    have hiz : (∑ a ∈ N.incoming S, f a) = 0 := Finset.sum_eq_zero hin
    linarith

end FiniteCombinatorics.Graph.Flows.Network
