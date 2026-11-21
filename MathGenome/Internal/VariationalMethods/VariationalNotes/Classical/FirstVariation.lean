import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.FirstVariation
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.VariationSpaces
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.DistributionalPrimitive
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.MetricSpace.ProperSpace

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace VariationalNotes.Classical

/-- Measurability of the derivative follows from measurable difference quotients;
it is not an additional regularity assumption on the first variation. -/
theorem aestronglyMeasurable_directional_derivative {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : ℝ → α → ℝ} {D : α → ℝ}
    (hF : ∀ᶠ s in 𝓝 (0 : ℝ), AEStronglyMeasurable (F s) μ)
    (h0 : AEStronglyMeasurable (F 0) μ)
    (hD : ∀ᵐ t ∂μ, HasDerivAt (fun s => F s t) (D t) 0) :
    AEStronglyMeasurable D μ := by
  classical
  let G : ℝ → α → ℝ := fun s =>
    if AEStronglyMeasurable (F s) μ then fun t => s⁻¹ * (F s t - F 0 t) else 0
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℝ)) (f := G)
  · intro s
    dsimp [G]
    split_ifs with hs
    · exact (hs.sub h0).const_mul _
    · exact aestronglyMeasurable_zero
  · filter_upwards [hD] with t ht
    apply ht.tendsto_slope.congr'
    filter_upwards [hF.filter_mono nhdsWithin_le_nhds] with s hs
    simp [G, hs, slope_def_field, div_eq_mul_inv, mul_comm]

/-- Dominated differentiation in a single direction, retaining integrability
of the resulting density as well as the actual derivative of the action. -/
theorem dominatedDirection_hasDerivAt (I : Interval) (F : ℝ → ℝ → ℝ) (D : ℝ → ℝ)
    (h0 : IntegrableOn (F 0) (Ioo I.a I.b)) (h : DominatedDirection I F D) :
    IntegrableOn D (Ioo I.a I.b) ∧
      HasDerivAt (fun s => ∫ t in Ioo I.a I.b, F s t)
        (∫ t in Ioo I.a I.b, D t) 0 := by
  obtain ⟨hmeas, r, hr, B, hB, F', heq, hdiff⟩ := h
  have hd0 : ∀ᵐ t ∂volume.restrict (Ioo I.a I.b),
      HasDerivAt (fun s => F s t) (F' 0 t) 0 :=
    hdiff.mono fun t ht => (ht 0 (Metric.mem_ball_self hr)).1
  have hm := aestronglyMeasurable_directional_derivative hmeas h0.aestronglyMeasurable hd0
  obtain ⟨hi, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) hr) hmeas h0 hm
    (hdiff.mono fun t ht s hs => (ht s hs).2) hB
    (hdiff.mono fun t ht s hs => (ht s hs).1)
  have he : (∫ t in Ioo I.a I.b, F' 0 t) = ∫ t in Ioo I.a I.b, D t :=
    integral_congr_ae heq
  exact ⟨hi.congr heq, he ▸ hd⟩

theorem dominatedFirstVariation : Specs.VariationalNotes.Classical.FirstVariation.dominatedFirstVariation := by
  intro I m L u v p q h0 hmin hdom η hη
  have hzero : IntegrableOn
      ((fun (s : ℝ) t => L (t, u t + s • η t, v t + s • deriv η t)) 0) (Ioo I.a I.b) := by
    simpa using h0
  obtain ⟨hi, hd⟩ := dominatedDirection_hasDerivAt I _ _ hzero (hdom η hη)
  exact ⟨hi, hd, (hmin η hη).hasDerivAt_eq_zero hd⟩

/-- A compact reference graph stays in an open set for all sufficiently small
parameters. This controls the whole interval, including its endpoints. -/
theorem affine_graph_eventually {I : Interval} {m : ℕ} (u η : C1Curve I m)
    {U : Set (ℝ × State m × State m)} (hU : IsOpen U)
    (hu : ∀ t : I.Points, graphPoint u t ∈ U) :
    ∀ᶠ s : ℝ in 𝓝 0, ∀ t : I.Points, graphPoint (u + s • η) t ∈ U := by
  have hc : Continuous (fun x : ℝ × I.Points =>
      ((x.2 : ℝ), u.state x.2 + x.1 • η.state x.2,
        u.velocity x.2 + x.1 • η.velocity x.2)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk
      (((u.state.continuous.comp continuous_snd).add
          (continuous_fst.smul (η.state.continuous.comp continuous_snd))).prodMk
        ((u.velocity.continuous.comp continuous_snd).add
          (continuous_fst.smul (η.velocity.continuous.comp continuous_snd))))
  have he := (isCompact_univ : IsCompact (univ : Set I.Points)).eventually_forall_of_forall_eventually
    (x₀ := (0 : ℝ)) (P := fun s t => graphPoint (u + s • η) t ∈ U) (by
      intro t _
      have ht : ((t : ℝ), u.state t + (0 : ℝ) • η.state t,
          u.velocity t + (0 : ℝ) • η.velocity t) ∈ U := by simpa [graphPoint] using hu t
      exact hc.continuousAt.eventually (hU.mem_nhds ht))
  simpa using he

theorem strongLocalMinimum_weak {I : Interval} {m : ℕ} (L : Lagrangian m)
    (xₐ xᵦ : State m) (u : C1Curve I m)
    (h : strongLocalMinimum L xₐ xᵦ u) : weakLocalMinimum L xₐ xᵦ u := by
  obtain ⟨hu, ε, hε, hmin⟩ := h
  refine ⟨hu, ε, hε, fun v hv hdist => hmin v hv (lt_of_le_of_lt ?_ hdist)⟩
  change ‖(v - u).state‖ ≤ ‖v - u‖
  rw [VariationSpaces.curve_norm]
  exact le_max_left _ _

/-- Both notions of minimum give a genuine two-sided minimum along every
endpoint-zero affine C¹ path. -/
theorem affine_action_localMinimum {I : Interval} {m : ℕ} (L : Lagrangian m)
    (xₐ xᵦ : State m) (u η : C1Curve I m)
    (hmin : weakLocalMinimum L xₐ xᵦ u ∨ strongLocalMinimum L xₐ xᵦ u)
    (hη : η ∈ endpointZero I m) :
    IsLocalMin (fun s : ℝ => action L (u + s • η)) 0 := by
  have hw : weakLocalMinimum L xₐ xᵦ u := hmin.elim id (strongLocalMinimum_weak L xₐ xᵦ u)
  obtain ⟨hu, ε, hε, hm⟩ := hw
  have hadm := affine_graph_eventually u η L.isOpen_domain hu.1
  have hn : ∀ s : ℝ, ‖(u + s • η) - u‖ = |s| * ‖η‖ := by
    intro s
    have he : (u + s • η) - u = s • η := by
      apply Subtype.ext
      apply Prod.ext <;> ext t <;>
        exact add_sub_cancel_left _ _
    rw [he]
    change ‖s • η.val‖ = |s| * ‖η.val‖
    rw [norm_smul, Real.norm_eq_abs]
  have hc : Continuous (fun s : ℝ => ‖(u + s • η) - u‖) := by
    simp_rw [hn]
    exact continuous_abs.mul continuous_const
  have hsmall : ∀ᶠ s : ℝ in 𝓝 0, ‖(u + s • η) - u‖ < ε :=
    hc.continuousAt.eventually (gt_mem_nhds (by simpa only [hn, abs_zero, zero_mul] using hε))
  filter_upwards [hadm, hsmall] with s hs hnorm
  have hv : u + s • η ∈ fixedEndpointClass L xₐ xᵦ := by
    refine ⟨hs, ?_, ?_⟩
    · change u.state I.left + s • η.state I.left = xₐ
      rw [hη.1, smul_zero, add_zero, hu.2.1]
    · change u.state I.right + s • η.state I.right = xᵦ
      rw [hη.2, smul_zero, add_zero, hu.2.2]
  simpa using hm (u + s • η) hv hnorm

theorem stateField_continuousOn (I : Interval) (m : ℕ) (u : C1Curve I m) :
    ContinuousOn (stateField I m u) (Icc I.a I.b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert u.state.continuous using 1
  funext t
  simp [stateField, extendState, t.property]

theorem velocityField_continuousOn (I : Interval) (m : ℕ) (u : C1Curve I m) :
    ContinuousOn (velocityField I m u) (Icc I.a I.b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert u.velocity.continuous using 1
  funext t
  simp [velocityField, extendState, t.property]

/-- Restriction of a globally smooth test to a closed interval gives a C¹ jet. -/
def interiorTestCurve {I : Interval} {m : ℕ} (φ : ℝ → State m)
    (hφ : ContDiff ℝ ∞ φ) : C1Curve I m :=
  ⟨(⟨fun t => φ t, hφ.continuous.comp continuous_subtype_val⟩,
    ⟨fun t => deriv φ t, (hφ.continuous_deriv (by simp)).comp continuous_subtype_val⟩), by
    intro t
    apply ((hφ.differentiable (by simp) t).hasDerivAt.hasDerivWithinAt).congr_of_mem
      (fun x hx => ?_) t.property
    simp [extendState, hx]⟩

theorem interiorTestCurve_endpointZero {I : Interval} {m : ℕ} (φ : ℝ → State m)
    (hφ : smoothInteriorTest I φ) : interiorTestCurve φ hφ.1 ∈ endpointZero I m := by
  constructor
  · change φ I.a = 0
    exact image_eq_zero_of_notMem_tsupport (by
      intro h
      exact (lt_irrefl I.a) (hφ.2.2 h).1)
  · change φ I.b = 0
    exact image_eq_zero_of_notMem_tsupport (by
      intro h
      exact (lt_irrefl I.b) (hφ.2.2 h).2)

/-- Velocity and state insertions into time × state × velocity. -/
def stateInsertion (m : ℕ) : State m →L[ℝ] ℝ × State m × State m :=
  (ContinuousLinearMap.inr ℝ ℝ (State m × State m)).comp
    (ContinuousLinearMap.inl ℝ (State m) (State m))

def velocityInsertion (m : ℕ) : State m →L[ℝ] ℝ × State m × State m :=
  (ContinuousLinearMap.inr ℝ ℝ (State m × State m)).comp
    (ContinuousLinearMap.inr ℝ (State m) (State m))

theorem stateGradient_eq_total {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t : I.Points) (h : DifferentiableAt ℝ L.value (graphPoint u t)) :
    stateGradient L u t = (InnerProductSpace.toDual ℝ (State m)).symm
      ((fderiv ℝ L.value (graphPoint u t)).comp (stateInsertion m)) := by
  apply congrArg (InnerProductSpace.toDual ℝ (State m)).symm
  have hi : HasFDerivAt (fun z => ((t : ℝ), z, u.velocity t)) (stateInsertion m) (u.state t) := by
    convert (hasFDerivAt_const (𝕜 := ℝ) (t : ℝ) (u.state t)).prodMk
      ((hasFDerivAt_id (𝕜 := ℝ) (u.state t)).prodMk
        (hasFDerivAt_const (𝕜 := ℝ) (u.velocity t) (u.state t))) using 1 <;> ext z <;> rfl
  exact (h.hasFDerivAt.comp (u.state t) hi).fderiv

theorem momentum_eq_total {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t : I.Points) (h : DifferentiableAt ℝ L.value (graphPoint u t)) :
    momentum L u t = (InnerProductSpace.toDual ℝ (State m)).symm
      ((fderiv ℝ L.value (graphPoint u t)).comp (velocityInsertion m)) := by
  apply congrArg (InnerProductSpace.toDual ℝ (State m)).symm
  have hi : HasFDerivAt (fun v => ((t : ℝ), u.state t, v)) (velocityInsertion m) (u.velocity t) := by
    convert (hasFDerivAt_const (𝕜 := ℝ) (t : ℝ) (u.velocity t)).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) (u.state t) (u.velocity t)).prodMk
        (hasFDerivAt_id (𝕜 := ℝ) (u.velocity t))) using 1 <;> ext v <;> rfl
  exact (h.hasFDerivAt.comp (u.velocity t) hi).fderiv

theorem graphField_continuousOn (I : Interval) (m : ℕ) (u : C1Curve I m) :
    ContinuousOn (fun t => (t, stateField I m u t, velocityField I m u t)) (Icc I.a I.b) :=
  continuousOn_id.prodMk ((stateField_continuousOn I m u).prodMk
    (velocityField_continuousOn I m u))

theorem gradientFields_continuousOn {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 1) :
    ContinuousOn (momentumField L u) (Icc I.a I.b) ∧
      ContinuousOn (stateGradientField L u) (Icc I.a I.b) := by
  obtain ⟨U, hU, hu, _, hL⟩ := hreg
  have hmap : MapsTo (fun t => (t, stateField I m u t, velocityField I m u t))
      (Icc I.a I.b) U := by
    intro t ht
    simpa [graphPoint, stateField, velocityField, extendState, ht] using hu ⟨t, ht⟩
  have hd := (hL.continuousOn_fderiv_of_isOpen hU (by simp)).comp
    (graphField_continuousOn I m u) hmap
  have hdiff : ∀ t : I.Points, DifferentiableAt ℝ L.value (graphPoint u t) := fun t =>
    (hL.differentiableOn (by simp) _ (hu t)).differentiableAt (hU.mem_nhds (hu t))
  constructor
  · apply ((InnerProductSpace.toDual ℝ (State m)).symm.continuous.comp_continuousOn
      (hd.clm_comp (continuousOn_const (c := velocityInsertion m)))).congr
    intro t ht
    simp only [momentumField, dite_eq_left ht]
    rw [momentum_eq_total L u ⟨t, ht⟩ (hdiff ⟨t, ht⟩)]
    simp only [Function.comp_apply, graphPoint, stateField, velocityField, extendState, dite_eq_left ht]
  · apply ((InnerProductSpace.toDual ℝ (State m)).symm.continuous.comp_continuousOn
      (hd.clm_comp (continuousOn_const (c := stateInsertion m)))).congr
    intro t ht
    simp only [stateGradientField, dite_eq_left ht]
    rw [stateGradient_eq_total L u ⟨t, ht⟩ (hdiff ⟨t, ht⟩)]
    simp only [Function.comp_apply, graphPoint, stateField, velocityField, extendState, dite_eq_left ht]

/-- An endpoint-zero identity implies the distributional equation; no integration
by parts of the (initially only continuous) momentum is assumed. -/
theorem weakDerivative_of_endpoint_identity {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m)
    (h : ∀ η : C1Curve I m, η ∈ endpointZero I m →
      (∫ t in I.a..I.b, variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m η) (velocityField I m η) t) = 0) :
    WeakDerivativeInterval m I.a I.b (momentumField L u) (stateGradientField L u) := by
  intro φ hφ hc hs
  let η : C1Curve I m := interiorTestCurve φ hφ
  have hη : η ∈ endpointZero I m := interiorTestCurve_endpointZero φ ⟨hφ, hc, hs⟩
  have hid := h η hη
  rw [intervalIntegral.integral_of_le I.increasing.le, integral_Ioc_eq_integral_Ioo] at hid
  have heq : (∫ t in Ioo I.a I.b,
      inner ℝ (momentumField L u t) (deriv φ t) + inner ℝ (stateGradientField L u t) (φ t)) =
      ∫ t in Ioo I.a I.b, variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m η) (velocityField I m η) t := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    simp [variationDensity, stateField, velocityField, extendState, η, interiorTestCurve,
      C1Curve.state, C1Curve.velocity, Ioo_subset_Icc_self ht, add_comm]
  exact heq.trans hid

/-- Differentiation under an integral when the directional derivative is
continuous on a compact parameter strip. -/
theorem compactStrip_hasDerivAt (I : Interval) {F F' : ℝ → ℝ → ℝ}
    {r : ℝ} (hr : 0 < r)
    (hF : ContinuousOn (Function.uncurry F) (Metric.closedBall (0 : ℝ) r ×ˢ Icc I.a I.b))
    (hF' : ContinuousOn (Function.uncurry F') (Metric.closedBall (0 : ℝ) r ×ˢ Icc I.a I.b))
    (hdiff : ∀ s ∈ Metric.ball (0 : ℝ) r, ∀ t ∈ Icc I.a I.b,
      HasDerivAt (fun s => F s t) (F' s t) s) :
    HasDerivAt (fun s => ∫ t in I.a..I.b, F s t)
      (∫ t in I.a..I.b, F' 0 t) 0 := by
  have hslice : ∀ {G : ℝ → ℝ → ℝ},
      ContinuousOn (Function.uncurry G) (Metric.closedBall (0 : ℝ) r ×ˢ Icc I.a I.b) →
      ∀ s ∈ Metric.closedBall (0 : ℝ) r, ContinuousOn (G s) (Icc I.a I.b) := by
    intro G hG s hs
    exact hG.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hs, ht⟩)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) r).prod (isCompact_Icc (a := I.a) (b := I.b))).exists_bound_of_continuousOn hF'
  have hzero : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) r := Metric.mem_closedBall_self hr.le
  have hu : ∀ t ∈ Set.uIoc I.a I.b, t ∈ Icc I.a I.b := by
    rw [uIoc_of_le I.increasing.le]
    exact Ioc_subset_Icc_self
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := F') (bound := fun _ => C) (Metric.ball_mem_nhds (0 : ℝ) hr)
    ?_ ((hslice hF 0 hzero).intervalIntegrable_of_Icc I.increasing.le)
    ?_ ?_ (intervalIntegrable_const) ?_).2
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with s hs
    exact (hslice hF s (Metric.ball_subset_closedBall hs)).aestronglyMeasurable
      measurableSet_Icc |>.mono_set (fun t ht => hu t ht)
  · exact (hslice hF' 0 hzero).aestronglyMeasurable measurableSet_Icc |>.mono_set
      (fun t ht => hu t ht)
  · filter_upwards with t ht s hs
    exact hC (s, t) ⟨Metric.ball_subset_closedBall hs, hu t ht⟩
  · filter_upwards with t ht s hs
    exact hdiff s hs t (hu t ht)

/-- The affine graph and its velocity in the variation parameter. -/
def affineGraphField {I : Interval} {m : ℕ} (u η : C1Curve I m) (s t : ℝ) :
    ℝ × State m × State m :=
  (t, stateField I m u t + s • stateField I m η t,
    velocityField I m u t + s • velocityField I m η t)

def affineGraphDirection {I : Interval} {m : ℕ} (η : C1Curve I m) (t : ℝ) :
    ℝ × State m × State m := (0, stateField I m η t, velocityField I m η t)

theorem affineGraphField_hasDerivAt {I : Interval} {m : ℕ} (u η : C1Curve I m) (s t : ℝ) :
    HasDerivAt (fun s => affineGraphField u η s t) (affineGraphDirection η t) s := by
  have hz := (hasDerivAt_const s (stateField I m u t)).add
    ((hasDerivAt_id s).smul_const (stateField I m η t))
  have hv := (hasDerivAt_const s (velocityField I m u t)).add
    ((hasDerivAt_id s).smul_const (velocityField I m η t))
  simpa only [zero_add, one_smul, affineGraphDirection, affineGraphField, Pi.add_apply, id_eq] using
    (hasDerivAt_const s t).prodMk (hz.prodMk hv)

theorem affineGraphField_continuousOn {I : Interval} {m : ℕ} (u η : C1Curve I m)
    (S : Set ℝ) : ContinuousOn (Function.uncurry (affineGraphField u η)) (S ×ˢ Icc I.a I.b) := by
  have hmaps : MapsTo (Prod.snd : ℝ × ℝ → ℝ) (S ×ˢ Icc I.a I.b) (Icc I.a I.b) :=
    fun _ h => h.2
  exact continuousOn_snd.prodMk
    (((stateField_continuousOn I m u).comp continuousOn_snd hmaps |>.add
      (continuousOn_fst.smul ((stateField_continuousOn I m η).comp continuousOn_snd hmaps))).prodMk
    ((velocityField_continuousOn I m u).comp continuousOn_snd hmaps |>.add
      (continuousOn_fst.smul ((velocityField_continuousOn I m η).comp continuousOn_snd hmaps))))

theorem action_hasDerivAt_total {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u η : C1Curve I m) (hreg : regularNearGraph L u 1) :
    HasDerivAt (fun s : ℝ => action L (u + s • η))
      (∫ t in I.a..I.b, fderiv ℝ L.value (affineGraphField u η 0 t) (affineGraphDirection η t)) 0 := by
  obtain ⟨U, hU, hu, _, hL⟩ := hreg
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
  have hF := hL.continuousOn.comp hG hmaps
  have hA := (hL.continuousOn_fderiv_of_isOpen hU (by simp)).comp hG hmaps
  have hW : ContinuousOn (fun x : ℝ × ℝ => affineGraphDirection η x.2)
      (Metric.closedBall (0 : ℝ) r ×ˢ Icc I.a I.b) := by
    exact continuousOn_const.prodMk
      (((stateField_continuousOn I m η).comp continuousOn_snd (fun _ h => h.2)).prodMk
        ((velocityField_continuousOn I m η).comp continuousOn_snd (fun _ h => h.2)))
  have hD := hA.clm_apply hW
  have hd := compactStrip_hasDerivAt I
    (F := fun s t => L.value (affineGraphField u η s t))
    (F' := fun s t => fderiv ℝ L.value (affineGraphField u η s t) (affineGraphDirection η t))
    hr hF hD (by
    intro s hs t ht
    have hp := hmaps (x := (s, t)) ⟨Metric.ball_subset_closedBall hs, ht⟩
    have hl := (hL.differentiableOn (by simp) _ hp).differentiableAt (hU.mem_nhds hp)
    exact hl.hasFDerivAt.comp_hasDerivAt s (affineGraphField_hasDerivAt u η s t))
  have he : (fun s : ℝ => action L (u + s • η)) =
      (fun s => ∫ t in I.a..I.b, L.value (affineGraphField u η s t)) := by
    funext s
    unfold action
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le I.increasing.le] at ht
    simp only [affineGraphField, stateField, velocityField, extendState, dite_eq_left ht]
    rfl
  rw [he]
  exact hd

theorem variationDensity_eq_total {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t : I.Points) (z v : State m)
    (h : DifferentiableAt ℝ L.value (graphPoint u t)) :
    inner ℝ (stateGradient L u t) z + inner ℝ (momentum L u t) v =
      fderiv ℝ L.value (graphPoint u t) (0, z, v) := by
  rw [stateGradient_eq_total L u t h, momentum_eq_total L u t h]
  simp only [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply]
  rw [← map_add]
  congr 1
  ext <;> simp [stateInsertion, velocityInsertion]

theorem classicalActionDerivative : Specs.VariationalNotes.Classical.FirstVariation.classicalActionDerivative := by
  intro I m L u η hreg
  have hd := action_hasDerivAt_total L u η hreg
  have he : (∫ t in I.a..I.b,
      fderiv ℝ L.value (affineGraphField u η 0 t) (affineGraphDirection η t)) =
      ∫ t in I.a..I.b, variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m η) (velocityField I m η) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le I.increasing.le] at ht
    obtain ⟨U, hU, hu, _, hL⟩ := hreg
    have hp := hu ⟨t, ht⟩
    have hdiff := (hL.differentiableOn (by simp) _ hp).differentiableAt (hU.mem_nhds hp)
    simpa only [affineGraphField, affineGraphDirection, variationDensity, stateField,
      velocityField, momentumField, stateGradientField, extendState, dite_eq_left ht,
      zero_smul, add_zero, graphPoint] using
      (variationDensity_eq_total L u ⟨t, ht⟩ (η.state ⟨t, ht⟩) (η.velocity ⟨t, ht⟩) hdiff).symm
  exact he ▸ hd

theorem classicalFirstVariation : Specs.VariationalNotes.Classical.FirstVariation.classicalFirstVariation := by
  intro I m L xₐ xᵦ u hmin hreg η hη
  have hd := classicalActionDerivative I m L u η hreg
  exact ⟨hd, (affine_action_localMinimum L xₐ xᵦ u η hmin hη).hasDerivAt_eq_zero hd⟩

theorem classicalEulerLagrange : Specs.VariationalNotes.Classical.FirstVariation.classicalEulerLagrange := by
  intro I m L xₐ xᵦ u hmin hreg
  have hw := weakDerivative_of_endpoint_identity L u (fun η hη =>
    (classicalFirstVariation I m L xₐ xᵦ u hmin hreg η hη).2)
  obtain ⟨hp, hq⟩ := gradientFields_continuousOn L u hreg
  have hpc := hp.mono Ioo_subset_Icc_self
  have hqc := hq.mono Ioo_subset_Icc_self
  exact ⟨hw, distributionalPrimitiveContinuous m I.a I.b I.increasing
    (momentumField L u) (stateGradientField L u)
    (hpc.locallyIntegrableOn measurableSet_Ioo) (hqc.locallyIntegrableOn measurableSet_Ioo)
    hw hpc hqc⟩

end VariationalNotes.Classical
