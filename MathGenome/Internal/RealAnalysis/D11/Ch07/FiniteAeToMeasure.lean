import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.FiniteAeToMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch07.ConvergenceDefinitions
import MathGenome.Internal.RealAnalysis.D11.Ch01.ExhaustionRestriction
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
Almost-everywhere convergence implies convergence in measure on finite spaces
(paper.tex:2143–2155), and local convergence on arbitrary spaces (2395–2403).

Mathlib's finite-measure theorem bounds non-strict deviation sets. The strict
sets used in the paper are subsets, so squeezing their ENNReal-valued measures
gives the required literal global convergence. Restriction then proves both
the trace-space assertion and the local assertion, with no total-mass condition
on the original space.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u

namespace D11.Ch07.FiniteAeToMeasure

open D11.Ch07.ConvergenceDefinitions
open D11.Ch04.AeCommonException
open D11.Ch01.ExhaustionRestriction

theorem finite_ae_to_measure :
    Specs.D11.Ch07.FiniteAeToMeasure.finite_ae_to_measure := by
  intro X 𝕜 _ _ _ _ μ F f hμ hF hf hlim
  let : IsFiniteMeasure μ := ⟨hμ⟩
  have hnative : TendstoInMeasure μ F atTop f :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hF n).aestronglyMeasurable)
      ((almostEverywhere_iff_native μ _).mp hlim)
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendstoInMeasure_iff_norm.mp hnative ε hε) (fun _ => bot_le)
    ?_
  intro n
  apply measure_mono
  intro x hx
  exact (show ε < ‖F n x - f x‖ from hx).le

theorem ae_to_measure_restrict :
    Specs.D11.Ch07.FiniteAeToMeasure.ae_to_measure_restrict := by
  intro X 𝕜 _ _ _ _ μ F f A _hA hAfin hF hf hlim
  apply finite_ae_to_measure (restrictOnSpace μ A) F f
    (by simpa [restrictOnSpace] using hAfin) hF hf
  apply (almostEverywhere_iff_native (μ.restrict A) _).mpr
  exact ae_restrict_of_ae ((almostEverywhere_iff_native μ _).mp hlim)

theorem ae_to_measure_subtype :
    Specs.D11.Ch07.FiniteAeToMeasure.ae_to_measure_subtype := by
  intro X 𝕜 _ _ _ _ μ F f A hA hAfin hF hf hlim
  apply finite_ae_to_measure (restrictToSubtype μ A)
    (fun n x => F n x.val) (fun x => f x.val)
    (by rw [(restriction_mass μ A hA).2]; exact hAfin)
    (fun n => (hF n).comp measurable_subtype_coe) (hf.comp measurable_subtype_coe)
  apply (almostEverywhere_iff_native (restrictToSubtype μ A) _).mpr
  exact (ae_restrict_iff_subtype hA).mp
    (ae_restrict_of_ae ((almostEverywhere_iff_native μ _).mp hlim))

theorem ae_to_local_measure :
    Specs.D11.Ch07.FiniteAeToMeasure.ae_to_local_measure := by
  intro X 𝕜 _ _ _ _ μ F f hF hf hlim A hA hAfin ε hε
  have h := ae_to_measure_restrict μ F f A hA hAfin hF hf hlim ε hε
  change Tendsto (fun n => (μ.restrict A) (deviationSet (F n) f ε)) atTop (𝓝 0) at h
  change Tendsto (fun n => μ (A ∩ deviationSet (F n) f ε)) atTop (𝓝 0)
  simpa only [Measure.restrict_apply
    (measurable_deviationSet _ _ ε (hF _) hf), inter_comm] using h

end D11.Ch07.FiniteAeToMeasure
