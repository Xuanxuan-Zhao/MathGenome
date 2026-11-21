import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.RealAttainment

/-! Attainment of a maximum signed real flow value (the first part of W46).
The feasible set is a closed subset of the compact product of capacity
intervals. Conservation and value are finite linear sums of coordinates.
The argument includes loops, zero capacities, and an empty arc type. -/

open scoped BigOperators
universe u v
namespace FiniteCombinatorics.Graph.Flows.Network
open FiniteCombinatorics.Directed

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]
variable (N : Network V A)

/-- Divergence at any vertex is continuous on the full space of real loads. -/
theorem continuous_divergence (x : V) :
    Continuous (fun f : A → ℝ => N.graph.divergence f x) := by
  classical
  simp only [Digraph.divergence_eq]
  apply Continuous.sub
  · apply continuous_finsetSum
    intro a _
    by_cases h : N.graph.tail a = x
    · simpa only [ite_eq_left h] using (continuous_apply a : Continuous (fun f : A → ℝ => f a))
    · simpa only [ite_eq_right h] using (continuous_const : Continuous (fun _ : A → ℝ => (0 : ℝ)))
  · apply continuous_finsetSum
    intro a _
    by_cases h : N.graph.head a = x
    · simpa only [ite_eq_left h] using (continuous_apply a : Continuous (fun f : A → ℝ => f a))
    · simpa only [ite_eq_right h] using (continuous_const : Continuous (fun _ : A → ℝ => (0 : ℝ)))

/-- The zero flow witnesses nonemptiness even when there are no arcs. -/
theorem feasible_nonempty : Set.Nonempty {f : A → ℝ | N.Feasible f} :=
  ⟨fun _ => 0, N.zero_feasible⟩

/-- Every internal-vertex conservation equation defines a closed constraint. -/
theorem isClosed_conservation :
    IsClosed {f : A → ℝ | ∀ x, x ≠ N.source → x ≠ N.sink →
      N.graph.divergence f x = 0} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_eq (N.continuous_divergence x) continuous_const

/-- Both capacity bounds and conservation are closed conditions. -/
theorem isClosed_feasible : IsClosed {f : A → ℝ | N.Feasible f} := by
  change IsClosed ({f : A → ℝ | ∀ a, 0 ≤ f a ∧ f a ≤ N.capacity a} ∩
    {f : A → ℝ | ∀ x, x ≠ N.source → x ≠ N.sink → N.graph.divergence f x = 0})
  apply IsClosed.inter _ N.isClosed_conservation
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a =>
    (isClosed_le continuous_const (continuous_apply a)).inter
      (isClosed_le (continuous_apply a) continuous_const)

/-- The feasible set lies in the compact coordinatewise capacity box. -/
theorem isCompact_feasible : IsCompact {f : A → ℝ | N.Feasible f} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : A => (0 : ℝ)) N.capacity)).of_isClosed_subset
    N.isClosed_feasible
  intro f hf
  exact ⟨fun a => (hf.1 a).1, fun a => (hf.1 a).2⟩

/-- The objective is signed divergence at the source. -/
theorem continuous_value : Continuous N.value :=
  N.continuous_divergence N.source

/-- Every finite network admits a feasible real flow of greatest signed value. -/
theorem exists_maximum : ∃ f : A → ℝ, N.IsMaximum f := by
  obtain ⟨f, hf, hmax⟩ := N.isCompact_feasible.exists_isMaxOn N.feasible_nonempty
    N.continuous_value.continuousOn
  exact ⟨f, hf, hmax⟩

end FiniteCombinatorics.Graph.Flows.Network
