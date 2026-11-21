import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.LawsAndTransfer
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions

/-! Measurable versions and preservation of laws and expectations (Proposition 1.13).
The countably generated measurable target result is stronger than the requested
separable metric case. In particular it imposes no completeness assumption.
-/

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace ProbabilityFoundations.Ch01

universe u v

theorem completed_measurable_version :
    Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions.countablyGeneratedVersionType := by
  intro Ω S _ _ _ P X hX
  have h : AEMeasurable X P := (show NullMeasurable X P from hX).aemeasurable
  obtain ⟨N, hN, hzero, hEq⟩ :=
    (almostSurely_iff_measurable_null P (fun ω => h.mk X ω = X ω)).mp h.ae_eq_mk.symm
  exact ⟨h.mk X, h.measurable_mk, h.ae_eq_mk, N, hN, hzero, hEq⟩

theorem completed_metric_measurable_version :
    Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions.metricVersionType := by
  intro Ω S _ _ _ _ _ _ P X hX
  exact completed_measurable_version P X hX

theorem completed_real_measurable_version :
    Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions.realVersionType := by
  intro Ω _ P X hX
  exact completed_measurable_version P X hX

theorem completed_extendedReal_measurable_version :
    Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions.extendedRealVersionType := by
  intro Ω _ P X hX
  exact completed_measurable_version P X hX

theorem completed_nonnegative_measurable_version :
    Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions.nonnegativeVersionType := by
  intro Ω _ P X hX
  exact completed_measurable_version P X hX

theorem completed_version_law :
    Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions.lawPreservedType := by
  intro Ω S _ _ P X X0 hX hX0 hEq
  ext B hB
  rw [Measure.map_apply hX hB, Measure.map_apply hX0 hB]
  exact measure_congr (hEq.preimage B)

theorem completed_version_lintegral :
    Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions.nonnegativeExpectationPreservedType := by
  intro Ω S _ _ P X X0 hX hX0 hEq f hf
  rw [← law_lintegral P.completion X hX f hf,
    ← law_lintegral P X0 hX0 f hf]
  change (∫⁻ s, f s ∂@Measure.map (NullMeasurableSpace Ω P) S _ _ X P.completion) = ∫⁻ s, f s ∂Measure.map X0 P
  rw [completed_version_law P X X0 hX hX0 hEq]

theorem completed_version_real_integrable_iff :
    Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions.realIntegrabilityPreservedType := by
  intro Ω S _ _ P X X0 hX hX0 hEq f hf
  have hLaw : law P.completion X = law P X0 :=
    completed_version_law P X X0 hX hX0 hEq
  have hmid : Integrable f (law P.completion X) ↔ Integrable f (law P X0) := by
    rw [hLaw]
  exact (law_real_integrable_iff P.completion X hX f hf).symm.trans
    (hmid.trans (law_real_integrable_iff P X0 hX0 f hf))

theorem completed_version_real_integral :
    Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions.realExpectationPreservedType := by
  intro Ω S _ _ P X X0 hX hX0 hEq f hf hint
  have h0 : Integrable f (law P X0) :=
    (law_real_integrable_iff P X0 hX0 f hf).mpr hint
  have h : Integrable f (law P.completion X) := by
    change Integrable f (@Measure.map (NullMeasurableSpace Ω P) S _ _ X P.completion)
    rw [completed_version_law P X X0 hX hX0 hEq]
    exact h0
  rw [← law_real_integral P.completion X hX f h,
    ← law_real_integral P X0 hX0 f h0]
  change (∫ s, f s ∂@Measure.map (NullMeasurableSpace Ω P) S _ _ X P.completion) = ∫ s, f s ∂Measure.map X0 P
  rw [completed_version_law P X X0 hX hX0 hEq]

theorem completed_version_complex_integrable_iff :
    Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions.complexIntegrabilityPreservedType := by
  intro Ω S _ _ P X X0 hX hX0 hEq f hf
  have hLaw : law P.completion X = law P X0 :=
    completed_version_law P X X0 hX hX0 hEq
  have hmid : Integrable f (law P.completion X) ↔ Integrable f (law P X0) := by
    rw [hLaw]
  exact (law_complex_integrable_iff P.completion X hX f hf).symm.trans
    (hmid.trans (law_complex_integrable_iff P X0 hX0 f hf))

theorem completed_version_complex_integral :
    Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions.complexExpectationPreservedType := by
  intro Ω S _ _ P X X0 hX hX0 hEq f hf hint
  have h0 : Integrable f (law P X0) :=
    (law_complex_integrable_iff P X0 hX0 f hf).mpr hint
  have h : Integrable f (law P.completion X) := by
    change Integrable f (@Measure.map (NullMeasurableSpace Ω P) S _ _ X P.completion)
    rw [completed_version_law P X X0 hX hX0 hEq]
    exact h0
  rw [← law_complex_integral P.completion X hX f h,
    ← law_complex_integral P X0 hX0 f h0]
  change (∫ s, f s ∂@Measure.map (NullMeasurableSpace Ω P) S _ _ X P.completion) = ∫ s, f s ∂Measure.map X0 P
  rw [completed_version_law P X X0 hX hX0 hEq]

end ProbabilityFoundations.Ch01
