import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.DegenerateData
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.SegmentRemainder
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.Definitions
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

noncomputable section
universe u v w

namespace NumAnalysis206.Newton

/-- Zero preconditioned residual gives a certified root at radius zero. -/
theorem zero_residual : Specs.NumAnalysis206.Newton.ZeroResidualStatement := by
  intro 𝕜 _ X Y _ _ _ _ _ _ F U x₀ e hU hF hx₀ he hres
  have hz : e.symm (F x₀) = 0 := norm_eq_zero.mp (le_antisymm hres (norm_nonneg _))
  have hroot : F x₀ = 0 := e.symm.injective (by simpa using hz)
  refine ⟨hroot, Metric.closedBall_zero, ⟨x₀, by simp, hroot⟩, ?_⟩
  simp [Specs.NumAnalysis206.Newton.operatorNewtonValue, hroot]

/-- The zero derivative-difference bound makes the preconditioned function affine
on the prescribed ball, including a ball of radius zero. -/
theorem constant_derivative : Specs.NumAnalysis206.Newton.ConstantDerivativeStatement := by
  intro 𝕜 _ X Y _ _ _ _ _ _ F U x₀ e η hU hF hx₀ he hη hres hball hLip
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  let G : X → X := fun x => e.symm (F x)
  have hFd (x : X) (hx : x ∈ U) : DifferentiableAt 𝕜 F x :=
    (hF x hx).differentiableAt (hU.mem_nhds hx)
  have hGd (x : X) (hx : x ∈ U) :
      HasFDerivAt G ((e.symm : Y →L[𝕜] X).comp (fderiv 𝕜 F x)) x :=
    (e.symm : Y →L[𝕜] X).hasFDerivAt.comp x (hFd x hx).hasFDerivAt
  have hG : DifferentiableOn 𝕜 G U := fun x hx => (hGd x hx).differentiableAt.differentiableWithinAt
  have hG₀ : fderiv 𝕜 G x₀ = ContinuousLinearMap.id 𝕜 X := by
    rw [(hGd x₀ hx₀).fderiv, he]
    exact e.coe_symm_comp_coe
  have hGdiff : ∀ x ∈ Metric.closedBall x₀ η, ∀ y ∈ Metric.closedBall x₀ η,
      ‖fderiv 𝕜 G x - fderiv 𝕜 G y‖ ≤ 0 * ‖x - y‖ := by
    intro x hx y hy
    rw [(hGd x (hball hx)).fderiv, (hGd y (hball hy)).fderiv,
      ← ContinuousLinearMap.comp_sub]
    exact hLip x hx y hy
  have haffine : ∀ d : X, ‖d‖ ≤ η → G (x₀ + d) = G x₀ + d := by
    intro d hd
    have hx : x₀ ∈ Metric.closedBall x₀ η := Metric.mem_closedBall_self hη
    have hy : x₀ + d ∈ Metric.closedBall x₀ η := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hd
    have H := segment_remainder 𝕜 X X G U (Metric.closedBall x₀ η) 0
      hU hG hball (convex_closedBall x₀ η) (le_refl 0) hGdiff x₀ hx (x₀ + d) hy
    have hz : G (x₀ + d) - G x₀ - d = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa [hG₀] using H
    exact sub_eq_zero.mp (by simpa [sub_sub] using hz)
  have hstep : Specs.NumAnalysis206.Newton.operatorNewtonValue (𝕜 := 𝕜) F x₀ =
      x₀ - e.symm (F x₀) := by
    exact operatorNewton_eq_of_hasFDerivAt F x₀ e
      (by simpa [he] using (hFd x₀ hx₀).hasFDerivAt)
  have hmem : x₀ - e.symm (F x₀) ∈ Metric.closedBall x₀ η := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hres
  have hroot : F (x₀ - e.symm (F x₀)) = 0 := by
    apply e.symm.injective
    have H := haffine (-e.symm (F x₀)) (by simpa using hres)
    simpa [G, sub_eq_add_neg] using H
  refine ⟨haffine, ?_, hstep, hmem, hroot, ?_⟩
  · exact ⟨hx₀, hFd x₀ hx₀, by rw [he]; exact ⟨e, rfl⟩⟩
  · intro y hy hzero
    have H := haffine (y - x₀) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hy)
    have heq : (0 : X) = G x₀ + (y - x₀) := by simpa [G, hzero] using H
    have hd : y - x₀ = -G x₀ := (eq_neg_iff_add_eq_zero).mpr (by simpa [add_comm] using heq.symm)
    calc
      y = (y - x₀) + x₀ := (sub_add_cancel y x₀).symm
      _ = x₀ - e.symm (F x₀) := by rw [hd]; simp [G, sub_eq_add_neg, add_comm]

end NumAnalysis206.Newton
