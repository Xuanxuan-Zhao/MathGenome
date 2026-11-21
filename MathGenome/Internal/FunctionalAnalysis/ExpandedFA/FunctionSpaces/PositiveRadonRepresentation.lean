import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! The positive Riesz–Markov theorem on arbitrary locally compact Hausdorff
spaces, with the paper's three explicit regularity conditions. -/

namespace ExpandedFA.FunctionSpaces

open Set MeasureTheory
open scoped ENNReal CompactlySupported

namespace PositiveRadonRepresentation

open PositiveRadonRepresentationSpec

universe u

/-- Identifies the three explicit source conditions with Mathlib's `Regular`,
which does not impose inner regularity on arbitrary infinite-mass Borel sets. -/
theorem positiveRadon_iff_regular {X : Type u} [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) : PositiveRadon μ ↔ μ.Regular := by
  constructor
  · rintro ⟨hcompact, houter, hinner⟩
    refine { lt_top_of_isCompact := fun K hK => hcompact K hK
             outerRegular := ?_
             innerRegular := ?_ }
    · intro A hA r hr
      rw [houter A hA] at hr
      simpa only [iInf_lt_iff, exists_prop] using hr
    · intro U hU r hr
      rw [hinner U hU] at hr
      simpa only [lt_iSup_iff, exists_prop] using hr
  · intro h
    have : μ.Regular := h
    exact ⟨fun _ hK => hK.measure_lt_top,
      fun A _ => A.measure_eq_iInf_isOpen μ,
      fun _ hU => hU.measure_eq_iSup_isCompact μ⟩

/-- Positivity alone suffices: no global bound on the functional is needed. -/
theorem positive_radon_representation : PositiveRepresentation.{u} := by
  intro X _ _ _ _ _ I hI
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ I (fun f hf => hI f hf)
  let μ : Measure X := RealRMK.rieszMeasure Λ
  have hμ : PositiveRadon μ := (positiveRadon_iff_regular μ).mpr inferInstance
  have hrep (f : C_c(X, ℝ)) : Integrable f μ ∧ I f = ∫ x, f x ∂μ :=
    ⟨f.integrable, (RealRMK.integral_rieszMeasure Λ f).symm⟩
  refine ⟨μ, ⟨hμ, hrep⟩, ?_⟩
  intro ν hν
  have : ν.Regular := (positiveRadon_iff_regular ν).mp hν.1
  exact Measure.ext_of_integral_eq_on_compactlySupported
    (fun f => (hν.2 f).2.symm.trans (hrep f).2)

/-- Finiteness upgrades open-set inner regularity to Borel inner regularity. -/
theorem finite_radon_inner_regular : FiniteInnerRegularity.{u} := by
  intro X _ _ _ _ _ μ hμ hfinite A hA
  have : μ.Regular := (positiveRadon_iff_regular μ).mp hμ
  have : IsFiniteMeasure μ := ⟨hfinite⟩
  exact hA.measure_eq_iSup_isCompact μ

end PositiveRadonRepresentation

end ExpandedFA.FunctionSpaces
