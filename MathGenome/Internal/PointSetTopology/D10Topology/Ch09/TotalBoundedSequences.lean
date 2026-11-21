import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.TotalBoundedSequences
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.Sequences

/-! The Cauchy-subsequence characterization of total boundedness
(paper.tex, d10:09:total-bounded-basics).

For the forward direction we use the compact closure in the metric completion;
convergence there supplies a Cauchy subsequence in the original metric by the
isometry of the completion map. For the converse a failure of a finite ball
cover supplies a separated sequence. Neither direction assumes the space is
nonempty, infinite, or complete. -/

open Set Filter
open UniformSpace
universe u

namespace D10Topology.Ch09

theorem totallyBounded_iff_cauchy_subsequence {X : Type u} [d : MetricSpace X] :
    TotallyBounded d.toPseudoMetricSpace ↔
      ∀ s : ℕ → X, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        CauchySequence d.toPseudoMetricSpace (s ∘ φ) := by
  rw [totallyBounded_iff_mathlib]
  constructor
  · intro ht s
    let j : X → Completion X := (↑)
    have hcompact : IsCompact (closure (j '' (univ : Set X))) :=
      (ht.image (Completion.uniformContinuous_coe X)).closure.isCompact_of_isClosed
        isClosed_closure
    obtain ⟨a, _, φ, hφ, hlim⟩ :=
      hcompact.isSeqCompact (fun n => subset_closure (mem_image_of_mem j (mem_univ (s n))))
    refine ⟨φ, hφ, (cauchySequence_iff_mathlib _ _).mpr ?_⟩
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [Function.comp_apply, j, Completion.dist_eq] using hN m hm n hn
  · intro h
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    by_contra hn
    have hex : ∀ F : Set X, F.Finite → ∃ x : X, ∀ y ∈ F, ε ≤ dist x y := by
      intro F hF
      have hnot : ¬ (univ : Set X) ⊆ ⋃ y ∈ F, Metric.ball y ε :=
        fun hc => hn ⟨F, hF, hc⟩
      obtain ⟨x, _, hx⟩ := Set.not_subset.mp hnot
      refine ⟨x, fun y hy => ?_⟩
      exact le_of_not_gt (fun hxy => hx (mem_iUnion₂.mpr ⟨y, hy, hxy⟩))
    obtain ⟨s, hs⟩ := Set.seq_of_forall_finite_exists hex
    obtain ⟨φ, hφ, hc⟩ := h s
    obtain ⟨N, hN⟩ := hc ε hε
    have hsep : ε ≤ dist (s (φ (N + 1))) (s (φ N)) :=
      hs (φ (N + 1)) (s (φ N))
        (mem_image_of_mem s (hφ (Nat.lt_succ_self N)))
    exact (not_lt_of_ge hsep) (hN (N + 1) N.le_succ N le_rfl)

end D10Topology.Ch09
