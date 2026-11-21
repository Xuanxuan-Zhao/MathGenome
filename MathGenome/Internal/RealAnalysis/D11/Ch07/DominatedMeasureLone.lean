import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.DominatedMeasureLone
import MathGenome.Internal.RealAnalysis.D11.Ch07.SubsequenceUniqueness
import MathGenome.Internal.RealAnalysis.D11.Ch06.DominatedConvergence

/-!
Dominated convergence in global measure, paper.tex:2362–2381.

Every subsequence whose indices tend to infinity still converges globally in
measure. Extract an a.e. convergent further subsequence and apply the accepted
scalar dominated convergence theorem. One such extraction proves integrability
of the limit. The subsequence criterion for convergence then gives both full
integral limits. No finite-measure or completeness assumption is used.
-/
open Filter MeasureTheory
open scoped Topology
universe u

namespace D11.Ch07.DominatedMeasureLone

open D11.Ch07.ConvergenceDefinitions
open D11.Ch07.SubsequenceUniqueness
open D11.Ch06.ScalarIntegral
open D11.Ch04.AeCommonException

/-- Dominated global convergence in measure gives absolute-integral and
scalar-integral convergence, with integrability of all functions involved. -/
theorem dominated_convergence_in_measure :
    Specs.D11.Ch07.DominatedMeasureLone.dominated_convergence_in_measure := by
  intro X 𝕜 _ _ _ _ μ F f g hFm hfm hg hg0 hbound hlim
  have hnative := (inMeasureConverges_iff_native μ F f).mp hlim
  have hsubseq : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ,
        Specs.D11.Ch06.DominatedConvergence.convergenceConclusions
          μ (fun n => F (ns (ms n))) f := by
    intro ns hns
    obtain ⟨ms, _, hms⟩ := (hnative.comp hns).exists_seq_tendsto_ae
    refine ⟨ms, D11.Ch06.DominatedConvergence.dominated_convergence
      μ (fun n => F (ns (ms n))) f g (fun n => hFm _) hfm hg hg0
      (fun n => hbound _) ?_⟩
    exact (almostEverywhere_iff_native μ _).mpr hms
  obtain ⟨ms, _, hfi, _⟩ := hsubseq id tendsto_id
  have hgi := ((scalarIntegrable_iff μ g).mp hg).2
  have hFi : ∀ n, scalarIntegrable μ (F n) := by
    intro n
    exact (scalarIntegrable_iff μ _).mpr ⟨hFm n,
      hgi.mono' (hFm n).aestronglyMeasurable
        ((almostEverywhere_iff_native μ _).mp (hbound n))⟩
  refine ⟨hFi, hfi, ?_, ?_, ?_⟩
  · intro n
    exact (scalarIntegrable_iff μ _).mpr
      ⟨((hFm n).sub hfm).norm,
        (((scalarIntegrable_iff μ _).mp (hFi n)).2.sub
          ((scalarIntegrable_iff μ f).mp hfi).2).norm⟩
  · apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, _, _, _, habs, _⟩ := hsubseq ns hns
    exact ⟨ms, habs⟩
  · apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, _, _, _, _, hint⟩ := hsubseq ns hns
    exact ⟨ms, hint⟩

end D11.Ch07.DominatedMeasureLone
