import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.RCLike.Lemmas

/-!
Completeness and scalar identification in paper.tex:17036–17040.
The upstream quotient is definitionally `MeasureTheory.Lp`. Mathlib's
completeness instance assumes only completeness of the codomain and `1 ≤ p`;
in particular it includes the essential-supremum endpoint and arbitrary measures.

For scalars, second countability makes ordinary measurable functions strongly
measurable. Conversely an a.e. strongly measurable function has a strongly
measurable, hence Borel measurable, representative. A.e. replacement preserves
the extended p-norm, so it preserves membership and the quotient norm as well.
-/

noncomputable section
open Filter MeasureTheory
open scoped ENNReal
universe u v

namespace ExpandedFA.FunctionSpaces

theorem bochnerLp_complete : BochnerLpCompletenessSpec.LpComplete.{u,v} := by
  intro X E _ _ _ p _ μ
  exact MeasureTheory.Lp.instCompleteSpace

theorem scalar_strongMeasurable_representative :
    BochnerLpCompletenessSpec.ScalarStrongMeasurableRepresentative.{u,v} := by
  intro X 𝕜 _ _ _ _ μ f
  rw [strongMeasurable_identification]
  constructor
  · intro hf
    exact ⟨hf.mk f, hf.stronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩
  · rintro ⟨g, hg, hfg⟩
    exact hg.stronglyMeasurable.aestronglyMeasurable.congr hfg.symm

theorem scalar_lp_membership : BochnerLpCompletenessSpec.ScalarLpMembership.{u,v} := by
  intro X 𝕜 _ _ _ _ p _ μ f
  constructor
  · intro hf
    obtain ⟨g, hg, hfg⟩ := (scalar_strongMeasurable_representative μ f).mp
      ((strongMeasurable_identification μ f).mpr hf.aestronglyMeasurable)
    refine ⟨g, hg, ?_, hfg⟩
    exact (eLpNorm_congr_ae hfg ▸ hf.eLpNorm_lt_top)
  · rintro ⟨g, _hg, hgnorm, hfg⟩
    exact (memLp_congr_ae hfg).mpr hgnorm

theorem scalar_lp_representative :
    BochnerLpCompletenessSpec.ScalarLpRepresentative.{u,v} := by
  intro X 𝕜 _ _ _ _ p _ μ f
  obtain ⟨g, hg, hgnorm, hfg⟩ := (scalar_lp_membership p μ f).mp (Lp.memLp f)
  refine ⟨g, hg, hgnorm, hfg, ?_⟩
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae hfg)

end ExpandedFA.FunctionSpaces
