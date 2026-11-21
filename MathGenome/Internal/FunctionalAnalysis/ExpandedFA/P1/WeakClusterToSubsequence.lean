import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WeakClusterToSubsequence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.SeparableWeakCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07WeakBoundedness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12ConvexClosure
import Mathlib.Topology.Sequences

namespace ExpandedFA.P1.WeakClusterToSubsequence

universe u v
open Filter TopologicalSpace
open scoped Topology
noncomputable section

/-- The scalar images must be bounded: an escaping scalar sequence cannot
have a cluster point. Uniform boundedness then bounds A in its original norm. -/
theorem cluster_implies_bounded : Spec.ClusterImpliesBounded.{u, v} := by
  intro 𝕜 E _ _ _ A hA
  classical
  apply (C07WeakBoundedness.weak_boundedness 𝕜 E A).mpr
  intro f
  by_contra hb
  have hn : ∀ n : ℕ, ∃ x ∈ A, (n : ℝ) < ‖f x‖ := by
    intro n
    by_contra! h
    apply hb
    exact isBounded_iff_forall_norm_le.mpr ⟨n, by
      rintro _ ⟨x, hx, rfl⟩
      exact h x hx⟩
  choose s hs hnorm using hn
  obtain ⟨x, hx⟩ := hA s hs
  letI : TopologicalSpace E :=
    C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
  have heval := C12BoundedSequences.weak_evaluation_continuous 𝕜 E f
  have hfreq : ∃ᶠ n in atTop, ‖f (s n)‖ < ‖f x‖ + 1 :=
    hx.frequently ((heval.norm.tendsto x).eventually
      (eventually_lt_nhds (show ‖f x‖ < ‖f x‖ + 1 by linarith)))
  have hlarge : ∀ᶠ n : ℕ in atTop, ‖f x‖ + 1 ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop (‖f x‖ + 1))
  obtain ⟨n, hn, hn'⟩ := (hfreq.and_eventually hlarge).exists
  linarith [hnorm n]

/-- The norm-closed span of a sequence is separable and weakly closed.
Project to the countable scalar tests. A cluster point in that metrizable
product supplies the diagonal subsequence. Every further subsequence has a
weak cluster point in E; all such points lie in the closed span and have the
same tests, hence coincide. The neighborhood criterion then gives convergence.
-/
theorem cluster_implies_subsequence : Spec.ClusterImpliesSubsequence.{u, v} := by
  intro 𝕜 E _ _ _ A hA s hs
  classical
  let Y : Submodule 𝕜 E := (Submodule.span 𝕜 (Set.range s)).topologicalClosure
  have hYs : ∀ n, s n ∈ Y := fun n =>
    (Submodule.span 𝕜 (Set.range s)).le_topologicalClosure
      (Submodule.subset_span (Set.mem_range_self n))
  have hYsep : IsSeparable (Y : Set E) := by
    rw [show (Y : Set E) = closure (Submodule.span 𝕜 (Set.range s) : Set E) from
      Submodule.topologicalClosure_coe _]
    exact (Set.countable_range s).isSeparable.span.closure
  letI : SeparableSpace Y := hYsep.separableSpace
  obtain ⟨f, _, hsep⟩ := SeparableWeakCompact.countable_separating_family 𝕜 E Y
  have hYclosed := C12ConvexClosure.isWeaklyClosed_of_isClosed_submodule 𝕜 E Y
    (Submodule.isClosed_topologicalClosure _)
  letI : TopologicalSpace E :=
    C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
  let g : E → (ℕ → 𝕜) := fun x j => f j x
  have hg : Continuous g := continuous_pi fun j =>
    C12BoundedSequences.weak_evaluation_continuous 𝕜 E (f j)
  obtain ⟨y, hy⟩ := hA s hs
  change MapClusterPt y atTop s at hy
  have hyY : y ∈ Y := hYclosed.mem_of_mapClusterPt hy (.of_forall hYs)
  obtain ⟨φ, hφ, hconv⟩ := (hy.continuousAt_comp hg.continuousAt).tendsto_subseq
  refine ⟨y, φ, hφ, ?_⟩
  apply tendsto_def.mpr
  intro U hU
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, s (φ n) ∉ U := not_eventually.mp hnot
  obtain ⟨ψ, hψ, hout⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨z, hz⟩ := hA (s ∘ φ ∘ ψ) (fun n => hs (φ (ψ n)))
  change MapClusterPt z atTop (s ∘ φ ∘ ψ) at hz
  have hzY : z ∈ Y := hYclosed.mem_of_mapClusterPt hz
    (.of_forall fun n => hYs (φ (ψ n)))
  obtain ⟨ξ, hξ, hzconv⟩ := (hz.continuousAt_comp hg.continuousAt).tendsto_subseq
  have heq : g z = g y := tendsto_nhds_unique hzconv
    ((hconv.comp hψ.tendsto_atTop).comp hξ.tendsto_atTop)
  have hzy : z = y := by
    by_contra hne
    obtain ⟨j, hj⟩ := hsep ⟨z, hzY⟩ ⟨y, hyY⟩ (fun h => hne (congrArg Subtype.val h))
    exact hj (congrFun heq j)
  subst z
  obtain ⟨n, hn⟩ := (hz.frequently hU).exists
  exact hout n hn

end
end ExpandedFA.P1.WeakClusterToSubsequence
