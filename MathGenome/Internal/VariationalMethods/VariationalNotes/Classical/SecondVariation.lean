import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.SecondVariation
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.FirstVariation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace VariationalNotes.Classical.SecondVariation

def hessianZZ : Specs.VariationalNotes.Classical.SecondVariation.hessianZZType :=
  Specs.VariationalNotes.Classical.SecondVariation.hessianZZValue

def hessianZV : Specs.VariationalNotes.Classical.SecondVariation.hessianZVType :=
  Specs.VariationalNotes.Classical.SecondVariation.hessianZVValue

def hessianVV : Specs.VariationalNotes.Classical.SecondVariation.hessianVVType :=
  Specs.VariationalNotes.Classical.SecondVariation.hessianVVValue

def quadraticForm : Specs.VariationalNotes.Classical.SecondVariation.quadraticFormType :=
  Specs.VariationalNotes.Classical.SecondVariation.quadraticFormValue

end VariationalNotes.Classical.SecondVariation

namespace VariationalNotes.Classical

theorem mixedHessian_symmetric :
    Specs.VariationalNotes.Classical.SecondVariation.mixedHessian_symmetric := by
  intro I m L u hreg t z v
  obtain ⟨U, hU, hu, _, hL⟩ := hreg
  have hc := (hL (graphPoint u t) (hu t)).contDiffAt (hU.mem_nhds (hu t))
  exact hc.isSymmSndFDerivAt (by norm_num) (0, z, 0) (0, 0, v)

/-- Bilinearity and symmetry give the coefficient 2 in the mixed block. -/
theorem hessian_direction_eq_blocks {m : ℕ} (L : Lagrangian m)
    (x : ℝ × State m × State m) (z v : State m)
    (hs : IsSymmSndFDerivAt ℝ L.value x) :
    fderiv ℝ (fderiv ℝ L.value) x (0, z, v) (0, z, v) =
      secondVariationZZ L x z z + 2 * secondVariationZV L x z v +
        secondVariationVV L x v v := by
  have he : ((0 : ℝ), z, v) = (0, z, (0 : State m)) + (0, (0 : State m), v) := by
    simp
  rw [he, map_add]
  simp only [add_apply, map_add]
  rw [hs (0, 0, v) (0, z, 0)]
  simp only [secondVariationZZ, secondVariationZV, secondVariationVV]
  ring

/-- The first derivative along the affine family, locally as a function of its
parameter. The open regularity neighborhood may depend on the base curve. -/
theorem affine_action_deriv_eventually {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u η : C1Curve I m) (hreg : regularNearGraph L u 1) :
    ∀ᶠ s : ℝ in 𝓝 0,
      HasDerivAt (fun s : ℝ => action L (u + s • η))
        (∫ t in I.a..I.b,
          fderiv ℝ L.value (affineGraphField u η s t) (affineGraphDirection η t)) s := by
  obtain ⟨U, hU, hu, hsub, hL⟩ := hreg
  filter_upwards [affine_graph_eventually u η hU hu] with s hs
  have hr : regularNearGraph L (u + s • η) 1 := ⟨U, hU, hs, hsub, hL⟩
  have hd := action_hasDerivAt_total L (u + s • η) η hr
  have he : affineGraphField (u + s • η) η 0 = affineGraphField u η s := by
    funext t
    by_cases ht : t ∈ Icc I.a I.b
    · simp only [affineGraphField, stateField, velocityField, extendState, dite_eq_left ht,
        zero_smul, add_zero]
      rfl
    · simp [affineGraphField, stateField, velocityField, extendState, ht]
  rw [he] at hd
  have ht := hd.comp_of_eq s ((hasDerivAt_id s).sub_const s) (sub_self s).symm
  simp only [mul_one, Function.comp_def, id_eq] at ht
  convert ht using 1
  funext x
  congr 1
  module

/-- Twice differentiating under the integral gives the full Hessian applied
to the state-velocity direction in both slots. -/
theorem action_second_derivative_total {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u η : C1Curve I m) (hreg : regularNearGraph L u 2) :
    HasDerivAt (deriv (fun s : ℝ => action L (u + s • η)))
      (∫ t in I.a..I.b,
        fderiv ℝ (fderiv ℝ L.value) (affineGraphField u η 0 t)
          (affineGraphDirection η t) (affineGraphDirection η t)) 0 := by
  obtain ⟨U, hU, hu, hsubU, hL⟩ := hreg
  have hL' : ContDiffOn ℝ 1 (fderiv ℝ L.value) U :=
    hL.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp (affine_graph_eventually u η hU hu)
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hmaps : MapsTo (Function.uncurry (affineGraphField u η))
      (Metric.closedBall (0 : ℝ) r ×ˢ Icc I.a I.b) U := by
    intro x hx
    have hs : x.1 ∈ Metric.ball (0 : ℝ) R :=
      lt_of_le_of_lt hx.1 (half_lt_self hR)
    have h := hsub hs ⟨x.2, hx.2⟩
    change (x.2, u.state ⟨x.2, hx.2⟩ + x.1 • η.state ⟨x.2, hx.2⟩,
      u.velocity ⟨x.2, hx.2⟩ + x.1 • η.velocity ⟨x.2, hx.2⟩) ∈ U at h
    simpa only [Function.uncurry, affineGraphField, stateField, velocityField, extendState,
      dite_eq_left hx.2] using h
  have hG := affineGraphField_continuousOn u η (Metric.closedBall (0 : ℝ) r)
  have hA := hL'.continuousOn.comp hG hmaps
  have hB := (hL'.continuousOn_fderiv_of_isOpen hU (by simp)).comp hG hmaps
  have hW : ContinuousOn (fun x : ℝ × ℝ => affineGraphDirection η x.2)
      (Metric.closedBall (0 : ℝ) r ×ˢ Icc I.a I.b) := by
    exact continuousOn_const.prodMk
      (((stateField_continuousOn I m η).comp continuousOn_snd (fun _ h => h.2)).prodMk
        ((velocityField_continuousOn I m η).comp continuousOn_snd (fun _ h => h.2)))
  have hd := compactStrip_hasDerivAt I
    (F := fun s t => fderiv ℝ L.value (affineGraphField u η s t) (affineGraphDirection η t))
    (F' := fun s t => fderiv ℝ (fderiv ℝ L.value) (affineGraphField u η s t)
      (affineGraphDirection η t) (affineGraphDirection η t))
    hr (hA.clm_apply hW) ((hB.clm_apply hW).clm_apply hW) (by
      intro s hs t ht
      have hp := hmaps (x := (s, t)) ⟨Metric.ball_subset_closedBall hs, ht⟩
      have hl := (hL'.differentiableOn (by simp) _ hp).differentiableAt (hU.mem_nhds hp)
      convert! (by
        simpa only [Function.comp_apply, map_zero, add_zero] using
        (hl.hasFDerivAt.comp_hasDerivAt s
          (affineGraphField_hasDerivAt u η s t)).clm_apply
            (hasDerivAt_const s (affineGraphDirection η t))) using 1)
  apply hd.congr_of_eventuallyEq
  have hr1 : regularNearGraph L u 1 := ⟨U, hU, hu, hsubU, hL.of_le (by norm_num)⟩
  filter_upwards [affine_action_deriv_eventually L u η hr1] with s hs
  exact hs.deriv

theorem classicalSecondActionDerivative :
    Specs.VariationalNotes.Classical.SecondVariation.classicalSecondActionDerivative := by
  intro I m L u η hreg
  have hd := action_second_derivative_total L u η hreg
  have he : (∫ t in I.a..I.b,
      fderiv ℝ (fderiv ℝ L.value) (affineGraphField u η 0 t)
        (affineGraphDirection η t) (affineGraphDirection η t)) = secondVariationForm L u η := by
    unfold secondVariationForm
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le I.increasing.le] at ht
    obtain ⟨U, hU, hu, _, hL⟩ := hreg
    have hc := (hL _ (hu ⟨t, ht⟩)).contDiffAt (hU.mem_nhds (hu ⟨t, ht⟩))
    have hs := hc.isSymmSndFDerivAt (by norm_num)
    simpa only [affineGraphField, affineGraphDirection, zero_smul, add_zero,
      graphPoint, stateField, velocityField, extendState, dite_eq_left ht] using
      hessian_direction_eq_blocks L (graphPoint u ⟨t, ht⟩)
        (η.state ⟨t, ht⟩) (η.velocity ⟨t, ht⟩) hs
  exact he ▸ hd

/-- A two-sided local minimum has nonnegative second derivative. Only
local differentiability of the original scalar function is used. -/
theorem second_derivative_nonneg_of_localMinimum {f : ℝ → ℝ} {q : ℝ}
    (hmin : IsLocalMin f 0)
    (hdf : ∀ᶠ x in 𝓝 (0 : ℝ), DifferentiableAt ℝ f x)
    (hd2 : HasDerivAt (deriv f) q 0) : 0 ≤ q := by
  by_contra hq
  have hq : q < 0 := lt_of_not_ge hq
  have hn : ∀ᶠ x in 𝓝[>] (0 : ℝ), deriv f x < 0 := by
    filter_upwards [hd2.tendsto_slope_zero_right (gt_mem_nhds hq),
      self_mem_nhdsWithin] with x hx hpos
    have hx' : x⁻¹ * deriv f x < 0 := by
      simpa [hmin.deriv_eq_zero] using hx
    exact neg_of_mul_neg_right hx' (inv_nonneg.mpr hpos.le)
  have hall : ∀ᶠ x in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ f x ∧ (0 < x → deriv f x < 0) ∧ f 0 ≤ f x :=
    hdf.and ((eventually_nhdsWithin_iff.mp hn).and hmin)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hall
  have hb : ∀ x ∈ Icc 0 (r / 2), x ∈ Metric.ball (0 : ℝ) r := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    exact lt_of_le_of_lt hx.2 (half_lt_self hr)
  have hfc : ContinuousOn f (Icc 0 (r / 2)) := by
    intro x hx
    exact (hsub (hb x hx)).1.continuousAt.continuousWithinAt
  have hfd : DifferentiableOn ℝ f (Ioo 0 (r / 2)) := by
    intro x hx
    exact (hsub (hb x (Ioo_subset_Icc_self hx))).1.differentiableWithinAt
  obtain ⟨c, hc, he⟩ := exists_deriv_eq_slope f (half_pos hr) hfc hfd
  have hcneg := (hsub (hb c (Ioo_subset_Icc_self hc))).2.1 hc.1
  have hminr := (hsub (hb (r / 2) ⟨(half_pos hr).le, le_rfl⟩)).2.2
  have hquot : 0 ≤ (f (r / 2) - f 0) / (r / 2 - 0) :=
    div_nonneg (sub_nonneg.mpr hminr) (by linarith)
  rw [← he] at hquot
  exact (not_lt_of_ge hquot) hcneg

theorem classicalSecondVariation :
    Specs.VariationalNotes.Classical.SecondVariation.classicalSecondVariation := by
  intro I m L xₐ xᵦ u hmin hreg η hη
  have hd := classicalSecondActionDerivative I m L u η hreg
  refine ⟨hd, ?_⟩
  apply second_derivative_nonneg_of_localMinimum
    (affine_action_localMinimum L xₐ xᵦ u η (Or.inl hmin) hη) _ hd
  obtain ⟨U, hU, hu, hsub, hL⟩ := hreg
  have hr1 : regularNearGraph L u 1 := ⟨U, hU, hu, hsub, hL.of_le (by norm_num)⟩
  filter_upwards [affine_action_deriv_eventually L u η hr1] with s hs
  exact hs.differentiableAt

end VariationalNotes.Classical
