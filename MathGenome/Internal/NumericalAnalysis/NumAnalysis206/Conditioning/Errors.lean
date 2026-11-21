import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Errors

/-! Forward and backward errors, with no attainment assumption (W12). -/

open scoped NNReal ENNReal

noncomputable section

set_option linter.unusedVariables false
set_option linter.checkUnivs false

universe u v w

namespace NumAnalysis206.Conditioning

def absoluteForwardError : Specs.NumAnalysis206.Conditioning.Errors.absoluteForwardErrorType :=
  @Specs.NumAnalysis206.Conditioning.Errors.absoluteForwardError

def relativeForwardError : Specs.NumAnalysis206.Conditioning.Errors.relativeForwardErrorType :=
  @Specs.NumAnalysis206.Conditioning.Errors.relativeForwardError

def feasiblePerturbation : Specs.NumAnalysis206.Conditioning.Errors.feasiblePerturbationType :=
  @Specs.NumAnalysis206.Conditioning.Errors.feasiblePerturbation

def backwardError : Specs.NumAnalysis206.Conditioning.Errors.backwardErrorType :=
  @Specs.NumAnalysis206.Conditioning.Errors.backwardError

def isBackwardCertificate : Specs.NumAnalysis206.Conditioning.Errors.isBackwardCertificateType :=
  @Specs.NumAnalysis206.Conditioning.Errors.isBackwardCertificate

def normwiseSize : Specs.NumAnalysis206.Conditioning.Errors.normwiseSizeType :=
  @Specs.NumAnalysis206.Conditioning.Errors.normwiseSize

def relativeNormwiseSize : Specs.NumAnalysis206.Conditioning.Errors.relativeNormwiseSizeType :=
  @Specs.NumAnalysis206.Conditioning.Errors.relativeNormwiseSize

def componentwiseSize : Specs.NumAnalysis206.Conditioning.Errors.componentwiseSizeType :=
  @Specs.NumAnalysis206.Conditioning.Errors.componentwiseSize

def normwiseBackwardError : Specs.NumAnalysis206.Conditioning.Errors.normwiseBackwardErrorType :=
  @Specs.NumAnalysis206.Conditioning.Errors.normwiseBackwardError

def relativeNormwiseBackwardError : Specs.NumAnalysis206.Conditioning.Errors.relativeNormwiseBackwardErrorType :=
  @Specs.NumAnalysis206.Conditioning.Errors.relativeNormwiseBackwardError

def componentwiseBackwardError : Specs.NumAnalysis206.Conditioning.Errors.componentwiseBackwardErrorType :=
  @Specs.NumAnalysis206.Conditioning.Errors.componentwiseBackwardError


theorem backwardError_le_of_feasible :
    Specs.NumAnalysis206.Conditioning.Errors.backwardError_le_of_feasibleStatement := by
  intro X Y _ U f x yhat D size v hv
  exact sInf_le ⟨v, hv, rfl⟩

theorem backwardError_eq_top_of_infeasible :
    Specs.NumAnalysis206.Conditioning.Errors.backwardError_eq_top_of_infeasibleStatement := by
  intro X Y _ U f x yhat D size h
  apply top_unique
  apply le_sInf
  rintro r ⟨v, hv, _⟩
  exact (h ⟨v, hv⟩).elim

theorem certificate_bounds_backwardError :
    Specs.NumAnalysis206.Conditioning.Errors.certificate_bounds_backwardErrorStatement := by
  intro X Y _ U f x yhat D size v bound h
  exact (backwardError_le_of_feasible f x yhat D size v h.1).trans h.2

theorem exists_feasible_size_lt :
    Specs.NumAnalysis206.Conditioning.Errors.exists_feasible_size_ltStatement := by
  intro X Y _ U f x yhat D size b h
  obtain ⟨r, ⟨v, hv, rfl⟩, hr⟩ := sInf_lt_iff.mp h
  exact ⟨v, hv, hr⟩

theorem exists_near_feasible_size :
    Specs.NumAnalysis206.Conditioning.Errors.exists_near_feasible_sizeStatement := by
  intro X Y _ U f x yhat D size hfinite ε hε
  apply exists_feasible_size_lt f x yhat D size
  exact ENNReal.lt_add_right hfinite (by simpa using ne_of_gt hε)

theorem componentwiseSize_le_iff :
    Specs.NumAnalysis206.Conditioning.Errors.componentwiseSize_le_iffStatement := by
  intro I K _ scale v bound
  change (⨆ i, (‖v i‖₊ : ℝ≥0∞) / (scale i : ℝ≥0∞)) ≤ (bound : ℝ≥0∞) ↔ _
  rw [iSup_le_iff]
  apply forall_congr'
  intro i
  rw [ENNReal.div_le_iff_le_mul (.inr ENNReal.coe_ne_top) (.inl ENNReal.coe_ne_top)]
  exact ENNReal.coe_le_coe

theorem componentwiseSize_zero_scale :
    Specs.NumAnalysis206.Conditioning.Errors.componentwiseSize_zero_scaleStatement := by
  intro I K _ scale v i hs hv
  apply top_unique
  change ⊤ ≤ ⨆ j, (‖v j‖₊ : ℝ≥0∞) / (scale j : ℝ≥0∞)
  have hi : (‖v i‖₊ : ℝ≥0∞) / (scale i : ℝ≥0∞) = ⊤ := by
    rw [hs, ENNReal.coe_zero]
    exact ENNReal.div_zero (by simpa using hv)
  rw [← hi]
  exact le_iSup (fun j => (‖v j‖₊ : ℝ≥0∞) / (scale j : ℝ≥0∞)) i

end NumAnalysis206.Conditioning
