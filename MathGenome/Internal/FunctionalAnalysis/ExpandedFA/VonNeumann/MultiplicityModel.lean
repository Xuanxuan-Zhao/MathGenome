import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.MultiplicityModel
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ComplexConjugate

namespace ExpandedFA.VonNeumann.MultiplicityModel

abbrev SequenceSpace := Spec.SequenceSpace
abbrev Multiplicity := Spec.Multiplicity
abbrev fiber := Spec.fiber
abbrev directIntegralSubmodule := Spec.directIntegralSubmodule
abbrev DirectIntegral := Spec.DirectIntegral
abbrev OperatorField := Spec.OperatorField
abbrev EssentialOperatorField := Spec.EssentialOperatorField
abbrev fieldENorm := @Spec.fieldENorm
abbrev fieldNorm := @Spec.fieldNorm
abbrev BoundedCoordinate := Spec.BoundedCoordinate

theorem fiber_closed (d : ℕ∞) : IsClosed (fiber d : Set SequenceSpace) := by
  have h : (fiber d : Set SequenceSpace) =
      ⋂ (k : ℕ) (_ : ¬ (k : ℕ∞) < d), {x : SequenceSpace | x k = 0} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq]
    rfl
  rw [h]
  exact isClosed_iInter fun k => isClosed_iInter fun _ =>
    isClosed_eq (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 k).continuous continuous_const

instance fiber_complete (d : ℕ∞) : CompleteSpace (fiber d) :=
  (fiber_closed d).completeSpace_coe

theorem section_membership : Spec.SectionMembership := by
  intro μ m f
  rfl

theorem closed_section_space : Spec.ClosedSectionSpace := by
  intro μ m
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  filter_upwards [ae_all_iff.mpr hf, hφ] with z hz hlim
  exact (fiber_closed (m z)).mem_of_tendsto hlim (Eventually.of_forall fun n => hz (φ n))

instance directIntegral_complete (μ : Measure ℂ) (m : Multiplicity μ) :
    CompleteSpace (DirectIntegral μ m) :=
  (closed_section_space μ m).completeSpace_coe

theorem multiplicity_invariance : Spec.MultiplicityInvariance := by
  intro μ m n h
  ext f
  constructor <;> intro hf
  · filter_upwards [hf, h] with z hz heq
    simpa only [heq] using hz
  · filter_upwards [hf, h] with z hz heq
    simpa only [heq] using hz

/-- Zero extension using the orthogonal projection onto the coordinate fiber. -/
def extendFiber (d : ℕ∞) (B : fiber d →L[ℂ] fiber d) :
    SequenceSpace →L[ℂ] SequenceSpace :=
  (fiber d).subtypeL ∘L B ∘L (fiber d).orthogonalProjectionOnto

@[simp] theorem extendFiber_apply (d : ℕ∞) (B : fiber d →L[ℂ] fiber d)
    (x : fiber d) : extendFiber d B x = (B x : SequenceSpace) := by
  simp [extendFiber]

theorem extendFiber_supported (d : ℕ∞) (B : fiber d →L[ℂ] fiber d) :
    Spec.IsFiberOperator d (extendFiber d B) := by
  constructor
  · intro x
    exact (B ((fiber d).orthogonalProjectionOnto x)).property
  · intro x hx
    simp [extendFiber, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hx]

theorem extendFiber_norm (d : ℕ∞) (B : fiber d →L[ℂ] fiber d) :
    ‖extendFiber d B‖ = ‖B‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
    intro x
    change ‖B ((fiber d).orthogonalProjectionOnto x)‖ ≤ _
    exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((fiber d).norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg B))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (extendFiber d B).le_opNorm (x : SequenceSpace)
    simpa only [extendFiber_apply, Submodule.norm_coe] using h

theorem fiber_extension : Spec.FiberExtension := by
  intro d B
  exact ⟨extendFiber d B, extendFiber_supported d B, extendFiber_apply d B,
    extendFiber_norm d B⟩


abbrev fieldAction : Spec.FieldActionType := @Spec.fieldActionValue
abbrev coordinateOperator : Spec.CoordinateOperatorType := Spec.coordinateOperatorValue
abbrev essentialFieldNorm := @Spec.essentialFieldNormValue
abbrev essentialFieldAction := @Spec.essentialFieldActionValue
abbrev restrictFiber := @Spec.restrictFiberValue

/-- The ambient representation includes every operator on the fiber and does
not change its norm. This identifies the essential-sup norm with fiber norms. -/
theorem extend_restrictFiber (d : ℕ∞) (B : SequenceSpace →L[ℂ] SequenceSpace)
    (hB : Spec.IsFiberOperator d B) : extendFiber d (restrictFiber B hB) = B := by
  apply ContinuousLinearMap.ext
  intro x
  change B ((fiber d).starProjection x) = B x
  have h := hB.2 (x - (fiber d).starProjection x)
    ((fiber d).sub_starProjection_mem_orthogonal x)
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem fiber_operator_norm : Spec.FiberOperatorNorm := by
  intro d B hB
  rw [← extendFiber_norm d (restrictFiber B hB), extend_restrictFiber d B hB]

theorem field_action_property : Spec.FieldActionProperty (@fieldAction) := by
  intro μ m B f
  exact Spec.applyLpValue_ae B f

theorem field_action_bound : Spec.FieldActionBound := by
  intro μ m B
  apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
  intro f
  exact Spec.applyLpValue_bound B f

theorem coordinate_operator_property : Spec.CoordinateOperatorProperty coordinateOperator := by
  intro μ m h f
  exact Spec.coordinateLpValue_ae h f

theorem coordinate_bound : Spec.CoordinateBound := by
  intro μ m h R hR
  apply ContinuousLinearMap.opNorm_le_bound _ R.coe_nonneg
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Spec.coordinateLpValue_ae h f, hR] with z hz hRz
  change ‖Spec.coordinateLpValue h (f : Lp SequenceSpace 2 μ) z‖ ≤ _
  rw [hz, norm_smul]
  exact mul_le_mul_of_nonneg_right hRz (norm_nonneg _)

theorem field_norm_finite : Spec.FieldNormFinite := by
  intro μ m B
  exact Spec.fieldENorm_lt_top B

theorem field_norm_zero : Spec.FieldNormZero := by
  intro μ m B
  rw [Spec.fieldNorm, ENNReal.toReal_eq_zero_iff]
  have hfin := (Spec.fieldENorm_lt_top B).ne
  simp only [hfin, or_false]
  rw [Spec.fieldENorm, ENNReal.essSup_eq_zero_iff]
  constructor
  · intro h
    filter_upwards [h] with z hz
    simpa using hz
  · intro h
    filter_upwards [h] with z hz
    simp [hz]

theorem coordinate_support_measurable {μ : Measure ℂ} (m : Multiplicity μ) (k : ℕ) :
    MeasurableSet {z | (k : ℕ∞) < m z} :=
  m.measurable_toFun (Set.to_countable {d : ℕ∞ | (k : ℕ∞) < d}).measurableSet

/-- The common-conull-set and coordinate-by-coordinate formulations agree. -/
theorem section_mem_iff_coordinates (μ : Measure ℂ) (m : Multiplicity μ)
    (f : Lp SequenceSpace 2 μ) :
    f ∈ directIntegralSubmodule μ m ↔
      ∀ k : ℕ, ∀ᵐ z ∂μ, ¬ (k : ℕ∞) < m z → f z k = 0 := by
  rw [section_membership μ m f, ae_all_iff]

/-- Null measure gives the zero Hilbert space, with no separate normalization. -/
theorem zero_measure_sections (m : Multiplicity (0 : Measure ℂ)) :
    Subsingleton (DirectIntegral 0 m) := by
  constructor
  intro f g
  apply Subtype.ext
  apply Lp.ext
  rw [Filter.EventuallyEq, ae_zero]
  exact Filter.eventually_bot

end ExpandedFA.VonNeumann.MultiplicityModel
