import MathGenome.Internal.MultivariableAnalysis.D04.C01.EuclideanInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.TopologicalTests
import Mathlib.Topology.Sequences

/-! Basic topological tests for the paper's Euclidean topology.
The upstream bridges identify the ball definitions with the metric topology.
Metric spaces are first countable, so their closure is their sequential
closure. Accumulation uses the closure of the punctured set `A \ {a}`.
No positivity assumption on the dimension or nonemptiness assumption on
any set is used. -/

open Set Filter Topology
namespace D04

theorem open_sUnion {n : ℕ} (S : Set (Set (E n)))
    (hS : ∀ U ∈ S, Open U) : Open (⋃₀ S) := by
  apply (open_iff_isOpen _).mpr
  exact isOpen_sUnion fun U hU => (open_iff_isOpen U).mp (hS U hU)

theorem open_sInter {n : ℕ} (S : Set (Set (E n)))
    (hfin : S.Finite) (hS : ∀ U ∈ S, Open U) : Open (⋂₀ S) := by
  apply (open_iff_isOpen _).mpr
  exact hfin.isOpen_sInter fun U hU => (open_iff_isOpen U).mp (hS U hU)

theorem closed_iff_seq_limits {n : ℕ} (F : Set (E n)) : Closed F ↔
    ∀ (s : ℕ → E n) (a : E n),
      (∀ k, s k ∈ F) → Tendsto s atTop (𝓝 a) → a ∈ F := by
  rw [closed_iff_isClosed]
  constructor
  · intro h s a hs ha
    exact h.mem_of_tendsto ha (Eventually.of_forall hs)
  · intro h
    have hseq : IsSeqClosed F := by
      intro s a hs ha
      exact h s a hs ha
    exact hseq.isClosed

theorem mem_closure_iff_sequence {n : ℕ} (A : Set (E n)) (a : E n) :
    a ∈ Closure A ↔
      ∃ s : ℕ → E n, (∀ k, s k ∈ A) ∧ Tendsto s atTop (𝓝 a) := by
  rw [closure_eq]
  exact mem_closure_iff_seq_limit

theorem accumulationPoint_iff_sequence {n : ℕ} (A : Set (E n)) (a : E n) :
    AccumulationPoint A a ↔
      ∃ s : ℕ → E n, (∀ k, s k ∈ A \ {a}) ∧ Tendsto s atTop (𝓝 a) := by
  rw [accumulationPoint_iff_accPt, accPt_principal_iff_clusterPt,
    ← mem_closure_iff_clusterPt]
  exact mem_closure_iff_seq_limit

theorem closed_closure {n : ℕ} (A : Set (E n)) : Closed (Closure A) := by
  rw [closed_iff_isClosed, closure_eq]
  exact isClosed_closure

theorem open_interior {n : ℕ} (A : Set (E n)) : Open (Interior A) := by
  rw [open_iff_isOpen, interior_eq]
  exact isOpen_interior

theorem boundary_eq_closure_inter_compl {n : ℕ} (A : Set (E n)) :
    Boundary A = Closure A ∩ Closure Aᶜ := by
  rw [boundary_eq_frontier, closure_eq, closure_eq]
  exact frontier_eq_closure_inter_closure

theorem closed_boundary {n : ℕ} (A : Set (E n)) : Closed (Boundary A) := by
  rw [closed_iff_isClosed, boundary_eq_frontier]
  exact isClosed_frontier

end D04
