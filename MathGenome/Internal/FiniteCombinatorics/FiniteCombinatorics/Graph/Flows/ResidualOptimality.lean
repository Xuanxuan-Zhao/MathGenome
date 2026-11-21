import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.Augmentation
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.WeakDuality
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.ResidualOptimality

/-! The reachable-cut certificate and residual optimality, without assuming
existence of a maximum or termination of augmentation for real capacities. -/

universe u v
namespace FiniteCombinatorics.Graph.Flows
open FiniteCombinatorics.Directed
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- The entire positive-residual reachable set, including the source itself. -/
def Network.residualReachableSet (N : Network V A) (f : A → ℝ) : Set V :=
  ResidualOptimalitySpec.reachableSet N f

namespace Network
variable (N : Network V A) (f : A → ℝ)

/-- Reachability is closed under each tagged positive residual arc. -/
theorem residualReachableSet_closed (b : N.ResidualArc f)
    (h : (N.residualGraph f).tail b ∈ N.residualReachableSet f) :
    (N.residualGraph f).head b ∈ N.residualReachableSet f := by
  obtain ⟨p⟩ := h
  exact ⟨p.append (Walk.single (N.residualGraph f) b)⟩

/-- Removing repeated vertices bridges walk reachability and simple paths. -/
theorem residual_walk_iff_path :
    Nonempty (Walk (N.residualGraph f) N.source N.sink) ↔
      Nonempty (Path (N.residualGraph f) N.source N.sink) := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨q, hq⟩ := Augmentation.exists_path p
    exact ⟨⟨q, hq⟩⟩
  · rintro ⟨p⟩
    exact ⟨p.val⟩

/-- Source `p204:residual-path`, second assertion, with the cut and all
crossing-arc conditions exposed. -/
theorem residual_reachable_cut (hf : N.Feasible f)
    (hwalk : ¬ Nonempty (Walk (N.residualGraph f) N.source N.sink)) :
    N.IsCut (N.residualReachableSet f) ∧
    (∀ a ∈ N.outgoing (N.residualReachableSet f), f a = N.capacity a) ∧
    (∀ a ∈ N.incoming (N.residualReachableSet f), f a = 0) ∧
    N.cutCapacity (N.residualReachableSet f) = N.value f := by
  have hS : N.IsCut (N.residualReachableSet f) :=
    ⟨⟨Walk.nil N.source⟩, hwalk⟩
  have hout : ∀ a ∈ N.outgoing (N.residualReachableSet f), f a = N.capacity a := by
    intro a ha
    obtain ⟨ht, hh⟩ := (N.mem_outgoing _ a).mp ha
    have hn : ¬ 0 < N.capacity a - f a := by
      intro hpos
      let b : N.ResidualArc f := ⟨(a, true), hpos⟩
      exact hh (N.residualReachableSet_closed f b ht)
    have hb := (hf.1 a).2
    linarith
  have hin : ∀ a ∈ N.incoming (N.residualReachableSet f), f a = 0 := by
    intro a ha
    obtain ⟨ht, hh⟩ := (N.mem_incoming _ a).mp ha
    have hn : ¬ 0 < f a := by
      intro hpos
      let b : N.ResidualArc f := ⟨(a, false), hpos⟩
      exact ht (N.residualReachableSet_closed f b hh)
    have hb := (hf.1 a).1
    linarith
  exact ⟨hS, hout, hin,
    ((N.value_eq_cutCapacity_iff f _ hf hS).mpr ⟨hout, hin⟩).symm⟩

/-- The cut certificate also follows from absence of a vertex-simple path. -/
theorem residual_reachable_cut_of_no_path (hf : N.Feasible f)
    (hpath : ¬ Nonempty (Path (N.residualGraph f) N.source N.sink)) :
    N.IsCut (N.residualReachableSet f) ∧
    (∀ a ∈ N.outgoing (N.residualReachableSet f), f a = N.capacity a) ∧
    (∀ a ∈ N.incoming (N.residualReachableSet f), f a = 0) ∧
    N.cutCapacity (N.residualReachableSet f) = N.value f :=
  N.residual_reachable_cut f hf (fun hw => hpath ((N.residual_walk_iff_path f).mp hw))

/-- A feasible real flow is maximum exactly when no residual walk joins s to t. -/
theorem maximum_iff_no_residual_walk (hf : N.Feasible f) :
    N.IsMaximum f ↔ ¬ Nonempty (Walk (N.residualGraph f) N.source N.sink) := by
  constructor
  · intro hmax hw
    obtain ⟨p, _, _, _, ε, hε, hg, hv⟩ := Network.residual_augmentation N f hf hw
    have hle := hmax.2 (N.augment f p ε) hg
    change N.value (N.augment f p ε) ≤ N.value f at hle
    change N.value (N.augment f p ε) = N.value f + ε at hv
    have hpos := hε.1
    linarith
  · intro hw
    obtain ⟨hS, _, _, heq⟩ := N.residual_reachable_cut f hf hw
    refine ⟨hf, fun g hg => ?_⟩
    change N.value g ≤ N.value f
    exact (N.weak_duality g _ hg hS).trans_eq heq

/-- Source `p204:W47`, residual-optimality assertion, for simple paths. -/
theorem maximum_iff_no_residual_path (hf : N.Feasible f) :
    N.IsMaximum f ↔ ¬ Nonempty (Path (N.residualGraph f) N.source N.sink) := by
  rw [N.maximum_iff_no_residual_walk f hf, N.residual_walk_iff_path f]

end Network
end FiniteCombinatorics.Graph.Flows
