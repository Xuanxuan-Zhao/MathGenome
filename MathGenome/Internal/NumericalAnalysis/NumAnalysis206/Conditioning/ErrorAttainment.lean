import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Conditioning.Errors
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.ErrorAttainment
import Mathlib.Analysis.RCLike.Lemmas

/-! Attainment of norm-sized backward error in finite dimension (after W12).
Intersect the feasible set with a norm ball through one feasible point.
The intersection is compact, so the continuous norm attains its minimum.
Points outside the ball cannot improve it. -/

open scoped NNReal ENNReal

universe u v w

namespace NumAnalysis206.Conditioning

private theorem exists_norm_minimizer {X : Type*} [NormedAddCommGroup X]
    [ProperSpace X] {F : Set X} (hne : F.Nonempty) (hclosed : IsClosed F) :
    ∃ v ∈ F, ∀ w ∈ F, ‖v‖ ≤ ‖w‖ := by
  obtain ⟨a, ha⟩ := hne
  let K := F ∩ Metric.closedBall (0 : X) ‖a‖
  have hcompact : IsCompact K := (isCompact_closedBall (0 : X) ‖a‖).inter_left hclosed
  have hK : K.Nonempty := ⟨a, ha, by simp⟩
  obtain ⟨v, hv, hmin⟩ := hcompact.exists_isMinOn hK continuous_norm.continuousOn
  refine ⟨v, hv.1, fun w hw => ?_⟩
  by_cases hball : w ∈ Metric.closedBall (0 : X) ‖a‖
  · exact hmin ⟨hw, hball⟩
  · have hva : ‖v‖ ≤ ‖a‖ := by simpa using hv.2
    have haw : ‖a‖ < ‖w‖ := by simpa using hball
    exact hva.trans haw.le

/-- The chosen norm attains the backward-error infimum on a nonempty closed
feasible set. The scalar field can be real or complex. -/
theorem normwiseBackwardError_attained :
    Specs.NumAnalysis206.Conditioning.ErrorAttainment.normwiseBackwardError_attainedStatement := by
  intro 𝕜 _ X Y _ _ _ U f x yhat D hne hclosed
  have : ProperSpace X := FiniteDimensional.proper_rclike 𝕜 X
  obtain ⟨v, hv, hmin⟩ := exists_norm_minimizer hne hclosed
  have heq : normwiseBackwardError f x yhat D = normwiseSize v := by
    apply le_antisymm
    · exact backwardError_le_of_feasible f x yhat D normwiseSize v hv
    · apply le_sInf
      rintro r ⟨w, hw, rfl⟩
      exact ENNReal.coe_le_coe.mpr (show ‖v‖₊ ≤ ‖w‖₊ from hmin w hw)
  refine ⟨v, hv, hmin, heq, ?_⟩
  change normwiseBackwardError f x yhat D < ⊤
  rw [heq]
  exact ENNReal.coe_lt_top

/-- Attainment for an explicit functional equal to the chosen norm. -/
theorem backwardError_attained_of_norm :
    Specs.NumAnalysis206.Conditioning.ErrorAttainment.backwardError_attained_of_normStatement := by
  intro 𝕜 _ X Y _ _ _ U f x yhat D size hsize hne hclosed
  obtain ⟨v, hv, hmin, heq, hfinite⟩ :=
    normwiseBackwardError_attained (𝕜 := 𝕜) f x yhat D hne hclosed
  have hs : size = normwiseSize := funext hsize
  subst size
  refine ⟨v, hv, ?_, heq, hfinite⟩
  intro w hw
  exact ENNReal.coe_le_coe.mpr (show ‖v‖₊ ≤ ‖w‖₊ from hmin w hw)

end NumAnalysis206.Conditioning
