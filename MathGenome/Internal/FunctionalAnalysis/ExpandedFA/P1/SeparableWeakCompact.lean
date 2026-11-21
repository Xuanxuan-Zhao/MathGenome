import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SeparableWeakCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12BoundedSequences
import Mathlib.Topology.MetricSpace.PiNat

/-!
The countable test family and weak metrizability lemma. We norm the points of
a dense sequence in Y directly by ambient Hahn–Banach functionals. Approximation
in norm shows that their common kernel in Y is zero. On a weakly compact subset
these tests give a continuous injection into a countable scalar product, hence
the original weak topology on that subset is metrizable.
-/

namespace ExpandedFA.P1.SeparableWeakCompact

universe u v
open scoped Topology
noncomputable section

theorem countable_separating_family : Spec.CountableSeparatingFamily.{u, v} := by
  intro 𝕜 E _ _ _ Y _
  classical
  let d : ℕ → Y := TopologicalSpace.denseSeq Y
  choose f hf hfd using fun n => exists_dual_vector'' 𝕜 (d n : E)
  have hzero : ∀ y : Y, (∀ n, f n (y : E) = 0) → y = 0 := by
    intro y hy
    by_contra hne
    have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hne
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq Y).exists_dist_lt y
      (show 0 < ‖y‖ / 3 by linarith)
    have hnorm : ‖f n (d n : E)‖ = ‖d n‖ := by
      rw [hfd n, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      rfl
    have hb : ‖d n‖ ≤ ‖d n - y‖ := by
      calc
        ‖d n‖ = ‖f n ((d n : E) - (y : E))‖ := by
          rw [map_sub, hy n, sub_zero, hnorm]
        _ ≤ ‖f n‖ * ‖(d n : E) - (y : E)‖ := (f n).le_opNorm _
        _ ≤ ‖d n - y‖ := by
          simpa only [one_mul, ← Submodule.coe_sub, Submodule.norm_coe] using
            mul_le_mul_of_nonneg_right (hf n) (norm_nonneg ((d n : E) - (y : E)))
    have hc := norm_le_norm_sub_add y (d n)
    rw [norm_sub_rev] at hb
    change dist y (d n) < ‖y‖ / 3 at hn
    rw [dist_eq_norm] at hn
    linarith
  refine ⟨f, hf, ?_⟩
  intro x y hxy
  by_contra! h
  apply hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  intro n
  change f n ((x : E) - (y : E)) = 0
  rw [map_sub, h n, sub_self]

theorem weak_compact_metrizable : Spec.WeakCompactMetrizable.{u, v} := by
  intro 𝕜 E _ _ _ Y _ K hKY
  obtain ⟨f, _, hsep⟩ := countable_separating_family 𝕜 E Y
  let : TopologicalSpace E :=
    C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
  intro hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
    (fun n (k : K) => f n (k : E))
  · intro n
    exact (C12BoundedSequences.weak_evaluation_continuous 𝕜 E (f n)).comp
      continuous_subtype_val
  · intro x y hxy
    apply hsep ⟨x.val, hKY x.property⟩ ⟨y.val, hKY y.property⟩
    intro heq
    exact hxy (Subtype.ext (congrArg (fun z : Y => (z : E)) heq))

theorem weak_sequence_bounded : Spec.WeakSequenceBounded.{u, v} :=
  C12BoundedSequences.weak_sequence_bounded

end
end ExpandedFA.P1.SeparableWeakCompact
