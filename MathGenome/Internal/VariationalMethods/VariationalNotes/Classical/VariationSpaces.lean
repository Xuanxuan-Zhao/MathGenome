import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.VariationSpaces
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace VariationalNotes.Classical.VariationSpaces

def curveSpace : VariationSpacesSpec.curveSpaceType := VariationSpacesSpec.curveSpaceValue

def lagrangians : VariationSpacesSpec.lagrangiansType := VariationSpacesSpec.lagrangiansValue

def variationSpace : VariationSpacesSpec.variationSpaceType := VariationSpacesSpec.variationSpaceValue

def graphAdmissible : VariationSpacesSpec.graphAdmissibleType := VariationSpacesSpec.graphAdmissibleValue

def fixedEndpointClass : VariationSpacesSpec.fixedEndpointClassType := VariationSpacesSpec.fixedEndpointClassValue

def action : VariationSpacesSpec.actionType := VariationSpacesSpec.actionValue

def momentum : VariationSpacesSpec.momentumType := VariationSpacesSpec.momentumValue

def stateGradient : VariationSpacesSpec.stateGradientType := VariationSpacesSpec.stateGradientValue

def regularNearGraph : VariationSpacesSpec.regularNearGraphType := VariationSpacesSpec.regularNearGraphValue

def uniformDistance : VariationSpacesSpec.uniformDistanceType := VariationSpacesSpec.uniformDistanceValue

def weakLocalMinimum : VariationSpacesSpec.weakLocalMinimumType := VariationSpacesSpec.weakLocalMinimumValue

def strongLocalMinimum : VariationSpacesSpec.strongLocalMinimumType := VariationSpacesSpec.strongLocalMinimumValue

def piecewiseC1 : VariationSpacesSpec.piecewiseC1Type := VariationSpacesSpec.piecewiseC1Value

def piecewiseAdmissible : VariationSpacesSpec.piecewiseAdmissibleType := VariationSpacesSpec.piecewiseAdmissibleValue

def piecewiseFixedEndpointClass : VariationSpacesSpec.piecewiseFixedEndpointClassType := VariationSpacesSpec.piecewiseFixedEndpointClassValue

def piecewiseAction : VariationSpacesSpec.piecewiseActionType := VariationSpacesSpec.piecewiseActionValue

def piecewiseStrongLocalMinimum : VariationSpacesSpec.piecewiseStrongLocalMinimumType := VariationSpacesSpec.piecewiseStrongLocalMinimumValue

def smoothStateTest : VariationSpacesSpec.smoothStateTestType := VariationSpacesSpec.smoothStateTestValue

def smoothTimeTest : VariationSpacesSpec.smoothTimeTestType := VariationSpacesSpec.smoothTimeTestValue

def stateStationary : VariationSpacesSpec.stateStationaryType := VariationSpacesSpec.stateStationaryValue

def innerTimeAction : VariationSpacesSpec.innerTimeActionType := VariationSpacesSpec.innerTimeActionValue

def innerTimeStationary : VariationSpacesSpec.innerTimeStationaryType := VariationSpacesSpec.innerTimeStationaryValue

def affineTime : VariationSpacesSpec.affineTimeType := VariationSpacesSpec.affineTimeValue

def movingEndpointVariations : VariationSpacesSpec.movingEndpointVariationsType := VariationSpacesSpec.movingEndpointVariationsValue

def endpointDisplacements : VariationSpacesSpec.endpointDisplacementsType := VariationSpacesSpec.endpointDisplacementsValue

def endpointTimeDisplacements : VariationSpacesSpec.endpointTimeDisplacementsType := VariationSpacesSpec.endpointTimeDisplacementsValue

theorem curve_derivative : VariationSpacesSpec.curve_derivativeType := by
  intro I m u t
  exact u.property t

theorem velocity_eq_derivWithin : VariationSpacesSpec.velocity_eq_derivWithinType := by
  intro I m u t
  exact ((u.property t).derivWithin (uniqueDiffOn_Icc I.increasing t t.property)).symm

theorem curve_norm : VariationSpacesSpec.curve_normType := by
  intro I m u
  rfl

theorem momentum_pairing : VariationSpacesSpec.momentum_pairingType := by
  intro I m L u t w
  exact InnerProductSpace.toDual_symm_apply

theorem stateGradient_pairing : VariationSpacesSpec.stateGradient_pairingType := by
  intro I m L u t w
  exact InnerProductSpace.toDual_symm_apply

theorem affineTime_endpoints : VariationSpacesSpec.affineTime_endpointsType := by
  intro I aₛ bₛ
  have h : I.b - I.a ≠ 0 := ne_of_gt (sub_pos.mpr I.increasing)
  constructor
  · simp [Classical.affineTime]
  · simp [Classical.affineTime, h]

theorem affineTime_increasing : VariationSpacesSpec.affineTime_increasingType := by
  intro I aₛ bₛ hab x y hxy
  dsimp [Classical.affineTime]
  simp only [add_lt_add_iff_left]
  apply mul_lt_mul_of_pos_right _ (sub_pos.mpr hab)
  exact (div_lt_div_iff_of_pos_right (sub_pos.mpr I.increasing)).2
    (sub_lt_sub_right hxy I.a)

theorem piecewiseAdmissible_regular : VariationSpacesSpec.piecewiseAdmissible_regularType := by
  intro I m L u h
  obtain ⟨knots, ha, hb, hk, hpieces⟩ := h
  refine ⟨knots, ha, hb, hk, ?_⟩
  intro c hc d hd hcd hnone
  exact (hpieces c hc d hd hcd hnone).1

/-- Position evaluation is bounded in the C¹ norm. -/
def stateEvaluation (I : Interval) (m : ℕ) (t : I.Points) :
    C1Curve I m →L[ℝ] State m :=
  (ContinuousMap.evalCLM ℝ t).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp (curveJets I m).subtypeL)

theorem rescaled_state_derivative (I : Interval) (m : ℕ) (u : C1Curve I m)
    (v : MovingEndpointVariation u) (t : I.Points) :
    HasDerivAt (fun s => (v.rescaled s).state t)
      ((deriv v.rescaled 0).state t) 0 := by
  have he := (stateEvaluation I m t).hasFDerivAt (x := v.rescaled 0)
  have hv := DifferentiableAt.hasDerivAt (𝕜 := ℝ) (F := C1Curve I m)
    (f := v.rescaled) (x := 0) v.rescaled_differentiable
  exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) he hv

theorem endpointDisplacements_total : VariationSpacesSpec.endpointDisplacements_totalType := by
  intro I m u v
  have hl : (fun s => v.physicalCurve s (v.leftTime s)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => (v.rescaled s).state I.left) := by
    apply v.rescaling_near.mono
    intro s hs
    have h := hs I.left
    change (v.rescaled s).state I.left =
      v.physicalCurve s (Classical.affineTime I (v.leftTime s) (v.rightTime s) I.a) at h
    rw [(affineTime_endpoints I (v.leftTime s) (v.rightTime s)).1] at h
    exact h.symm
  have hr : (fun s => v.physicalCurve s (v.rightTime s)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => (v.rescaled s).state I.right) := by
    apply v.rescaling_near.mono
    intro s hs
    have h := hs I.right
    change (v.rescaled s).state I.right =
      v.physicalCurve s (Classical.affineTime I (v.leftTime s) (v.rightTime s) I.b) at h
    rw [(affineTime_endpoints I (v.leftTime s) (v.rightTime s)).2] at h
    exact h.symm
  exact Prod.ext
    ((rescaled_state_derivative I m u v I.left).congr_of_eventuallyEq hl).deriv.symm
    ((rescaled_state_derivative I m u v I.right).congr_of_eventuallyEq hr).deriv.symm

theorem c1_contDiffOn : VariationSpacesSpec.c1_contDiffOnType := by
  intro I m u
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc I.increasing)).2
  constructor
  · intro t ht
    exact (u.property ⟨t, ht⟩).differentiableWithinAt
  · have hv : ContinuousOn (velocityField I m u) (Set.Icc I.a I.b) := by
      rw [continuousOn_iff_continuous_domRestrict]
      change Continuous (fun t : I.Points => velocityField I m u t)
      convert u.velocity.continuous using 1
      funext t
      simp [velocityField, extendState, t.property]
    apply hv.congr
    intro t ht
    rw [← velocity_eq_derivWithin I m u ⟨t, ht⟩]
    simp [velocityField, extendState, ht]

theorem piecewiseAction_of_C1 : VariationSpacesSpec.piecewiseAction_of_C1Type := by
  intro I m L u
  unfold Classical.piecewiseAction Classical.action
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le I.increasing.le] at ht
  change L.value (t, stateField I m u t,
      derivWithin (stateField I m u) (Set.Icc I.a I.b) t) =
    L.value (t, stateField I m u t, velocityField I m u t)
  rw [← velocity_eq_derivWithin I m u ⟨t, ht⟩]
  simp [velocityField, extendState, ht]

theorem graphAdmissible_piecewise : VariationSpacesSpec.graphAdmissible_piecewiseType := by
  intro I m L u hu
  refine ⟨{I.a, I.b}, by simp, by simp, ?_, ?_⟩
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact I.left.property
    · exact I.right.property
  · intro c hc d hd hcd hnone
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · exact (lt_irrefl _ hcd).elim
    · refine ⟨c1_contDiffOn I m u, ?_⟩
      intro t ht
      change (t, stateField I m u t,
        derivWithin (stateField I m u) (Set.Icc I.a I.b) t) ∈ L.domain
      rw [← velocity_eq_derivWithin I m u ⟨t, ht⟩]
      simpa [graphPoint, stateField, extendState, ht] using hu ⟨t, ht⟩
    · exact (I.increasing.asymm hcd).elim
    · exact (lt_irrefl _ hcd).elim

end VariationalNotes.Classical.VariationSpaces
