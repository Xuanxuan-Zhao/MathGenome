import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.CompactWeakSequences
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.SchauderAdjoints
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12BoundedSequences
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
Compact operators preserve weak limits of sequences as norm limits.
Weak boundedness gives compact closure of the image range. Each subsequence
has a norm-convergent further subsequence, whose limit is identified by every
continuous scalar-linear functional. This proves convergence of the whole
image sequence, without completeness of either space.
-/
namespace ExpandedFA.Compactness.CompactWeakSequences

universe u v w z
open Filter
open scoped Topology

/-- The sequence clause of Schauder's theorem in the scalar-test formulation. -/
theorem compact_completelyContinuous : Spec.CompactCompletelyContinuous.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ T hT s x hs
  have hweak := (weak_convergence_iff_tests s x).mpr hs
  obtain ⟨C, _, hC⟩ := P1.C12BoundedSequences.weak_sequence_bounded 𝕜 X s x hweak
  have hb : Bornology.IsBounded (Set.range s) :=
    (isBounded_iff_forall_norm_le).mpr ⟨C, by
      rintro _ ⟨n, rfl⟩
      exact hC n⟩
  have hK : IsCompact (closure (T '' Set.range s)) :=
    (compact_iff_bounded_images T.toLinearMap).mp hT (Set.range s) hb
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨y, _, k, hk, hlim⟩ := hK.tendsto_subseq (fun n =>
    subset_closure (Set.mem_image_of_mem T (Set.mem_range_self (ns n))))
  have hy : y = T x := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).mpr
    intro f
    have hfy := (f.continuous.tendsto y).comp hlim
    have hfx := (hs (f.comp T)).comp (hns.comp hk.tendsto_atTop)
    exact tendsto_nhds_unique hfy hfx
  exact ⟨k, hy ▸ hlim⟩

/-- The shared weak topology formulation, still exclusively about sequences. -/
theorem compact_weak_to_norm : Spec.CompactWeakToNorm.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ T hT s x hs
  exact compact_completelyContinuous 𝕜 X Y T hT s x
    ((weak_convergence_iff_tests s x).mp hs)

/-- Assemble all clauses of the source theorem from the accepted ideal and
Schauder results and the sequence theorem above. -/
theorem schauder_and_compact_ideal : Spec.SchauderAndCompactIdeal.{u, v, w, z} := by
  intro 𝕜 X Y _ _ _ _ _ _ _
  refine ⟨compact_maps_form_closed_subspace, ?_, ?_⟩
  · intro T
    exact ⟨SchauderAdjoints.compact_iff_compact_banachTranspose 𝕜 X Y T,
      compact_completelyContinuous 𝕜 X Y T⟩
  · intro Z _ _ _ T hT
    exact ⟨fun A => compact_precomp T.toLinearMap A hT,
      fun B => compact_postcomp T.toLinearMap B hT⟩

end ExpandedFA.Compactness.CompactWeakSequences
