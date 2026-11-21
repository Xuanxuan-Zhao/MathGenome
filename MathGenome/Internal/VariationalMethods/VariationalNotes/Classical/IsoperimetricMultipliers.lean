import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.IsoperimetricMultipliers
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.FirstVariation
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.EqualityMultipliers
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff
namespace VariationalNotes.Classical.IsoperimetricMultipliers

/-- Continuity of the density supplies every integrability premise used below. -/
theorem density_integrable {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u η : C1Curve I m) (hreg : regularNearGraph L u 1) :
    IntervalIntegrable (fun t => variationDensity (momentumField L u) (stateGradientField L u)
      (stateField I m η) (velocityField I m η) t) volume I.a I.b := by
  obtain ⟨hp, hq⟩ := gradientFields_continuousOn L u hreg
  exact ((hq.inner (stateField_continuousOn I m η)).add
    (hp.inner (velocityField_continuousOn I m η))).intervalIntegrable_of_Icc I.increasing.le

/-- The first variation is linear; continuity on the full curve space is not
needed for the finite-dimensional implicit-function argument. -/
def firstVariationLinear {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 1) : C1Curve I m →ₗ[ℝ] ℝ where
  toFun := firstVariation L u
  map_add' η θ := by
    have he : (fun t => variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m (η + θ)) (velocityField I m (η + θ)) t) =
      (fun t => variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m η) (velocityField I m η) t +
        variationDensity (momentumField L u) (stateGradientField L u)
          (stateField I m θ) (velocityField I m θ) t) := by
      funext t
      simp only [variationDensity, stateField, velocityField, C1Curve.state, C1Curve.velocity]
      change inner ℝ _ (extendState I m (η.val.1 + θ.val.1) t) +
        inner ℝ _ (extendState I m (η.val.2 + θ.val.2) t) = _
      simp only [extendState_add, Pi.add_apply, inner_add_right]
      ring
    unfold firstVariation
    rw [he]
    exact intervalIntegral.integral_add (density_integrable L u η hreg)
      (density_integrable L u θ hreg)
  map_smul' c η := by
    unfold firstVariation
    have he : (fun t => variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m (c • η)) (velocityField I m (c • η)) t) =
      (fun t => c * variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m η) (velocityField I m η) t) := by
      funext t
      simp only [variationDensity, stateField, velocityField, C1Curve.state, C1Curve.velocity]
      change inner ℝ _ (extendState I m (c • η.val.1) t) +
        inner ℝ _ (extendState I m (c • η.val.2) t) = _
      simp only [extendState_smul, Pi.smul_apply, real_inner_smul_right]
      ring
    rw [he, intervalIntegral.integral_const_mul]
    rfl

def constraintLinear {I : Interval} {m k : ℕ} (Ls : Fin k → Lagrangian m)
    (u : C1Curve I m) (hreg : ∀ i, regularNearGraph (Ls i) u 1) :
    endpointZero I m →ₗ[ℝ] (Fin k → ℝ) :=
  LinearMap.pi fun i => (firstVariationLinear (Ls i) u (hreg i)).comp (endpointZero I m).subtype

/-- Coordinates of a covector, including the zero-dimensional target. -/
theorem dual_coordinates {k : ℕ} (ν : (Fin k → ℝ) →ₗ[ℝ] ℝ) (y : Fin k → ℝ) :
    ν y = ∑ i, ν (Pi.single i 1) * y i := by
  classical
  have he : y = ∑ i : Fin k, y i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  simp [map_sum, mul_comm]

/-- Failure of surjectivity already supplies a nonzero abnormal covector. -/
theorem abnormal_of_not_surjective {I : Interval} {m k : ℕ}
    (L : Lagrangian m) (Ls : Fin k → Lagrangian m) (u : C1Curve I m)
    (hreg : ∀ i, regularNearGraph (Ls i) u 1)
    (hs : ¬ Function.Surjective (constraintDerivative Ls u)) :
    ∃ lam : Fin k → ℝ, lam ≠ 0 ∧ stationary L Ls u 0 lam := by
  classical
  let B := constraintLinear Ls u hreg
  have hB : LinearMap.range B < ⊤ := lt_top_iff_ne_top.mpr (by
    intro h
    exact hs (LinearMap.range_eq_top.mp h))
  obtain ⟨ν, hν, hvan⟩ := (LinearMap.range B).exists_dual_map_eq_bot_of_lt_top hB inferInstance
  let lam : Fin k → ℝ := fun i => ν (Pi.single i 1)
  have hn : lam ≠ 0 := by
    intro hz
    apply hν
    apply LinearMap.ext
    intro y
    change ν y = 0
    rw [dual_coordinates]
    change (∑ i, lam i * y i) = 0
    simp [hz]
  refine ⟨lam, hn, ?_⟩
  intro η
  have hb : ν (B η) = 0 := by
    have hm : ν (B η) ∈ (⊥ : Submodule ℝ ℝ) := by
      rw [← hvan]
      exact ⟨B η, LinearMap.mem_range_self B η, rfl⟩
    exact hm
  rw [dual_coordinates] at hb
  change (∑ i, ν (Pi.single i 1) * constraintDerivative Ls u η i) = 0 at hb
  simpa only [zero_mul, zero_add, lam] using hb


/-- A continuously differentiable integrand on a compact parameter strip gives
an actual C¹ integral on its open parameter ball. -/
theorem compactStrip_contDiffOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : Interval) {F : E → ℝ → ℝ}
    {D : E → ℝ → E →L[ℝ] ℝ} {r : ℝ} (_hr : 0 < r)
    (hF : ContinuousOn (Function.uncurry F) (Metric.closedBall (0 : E) r ×ˢ Icc I.a I.b))
    (hD : ContinuousOn (Function.uncurry D) (Metric.closedBall (0 : E) r ×ˢ Icc I.a I.b))
    (hd : ∀ x ∈ Metric.ball (0 : E) r, ∀ t ∈ Icc I.a I.b,
      HasFDerivAt (fun x => F x t) (D x t) x) :
    ContDiffOn ℝ 1 (fun x => ∫ t in I.a..I.b, F x t) (Metric.ball (0 : E) r) := by
  have hslice : ∀ {G : Type} [NormedAddCommGroup G] {f : E → ℝ → G},
      ContinuousOn (Function.uncurry f) (Metric.closedBall (0 : E) r ×ˢ Icc I.a I.b) →
      ∀ x ∈ Metric.closedBall (0 : E) r, ContinuousOn (f x) (Icc I.a I.b) := by
    intro G _ f hf x hx
    exact hf.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hx, ht⟩)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : E) r).prod
    (isCompact_Icc (a := I.a) (b := I.b))).exists_bound_of_continuousOn hD
  have hu : ∀ t ∈ Set.uIoc I.a I.b, t ∈ Icc I.a I.b := by
    rw [uIoc_of_le I.increasing.le]
    exact Ioc_subset_Icc_self
  have hder : ∀ x ∈ Metric.ball (0 : E) r,
      HasFDerivAt (fun x => ∫ t in I.a..I.b, F x t) (∫ t in I.a..I.b, D x t) x := by
    intro x hx
    apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := D) (bound := fun _ => C) (isOpen_ball.mem_nhds hx)
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hslice hF y (Metric.ball_subset_closedBall hy)).aestronglyMeasurable
        measurableSet_Icc |>.mono_set (fun t ht => hu t ht)
    · exact (hslice hF x (Metric.ball_subset_closedBall hx)).intervalIntegrable_of_Icc I.increasing.le
    · exact (hslice hD x (Metric.ball_subset_closedBall hx)).aestronglyMeasurable
        measurableSet_Icc |>.mono_set (fun t ht => hu t ht)
    · filter_upwards with t ht y hy
      exact hC (y, t) ⟨Metric.ball_subset_closedBall hy, hu t ht⟩
    · exact intervalIntegrable_const
    · filter_upwards with t ht y hy
      exact hd y hy t (hu t ht)
  have hc : ContinuousOn (fun x => ∫ t in I.a..I.b, D x t) (Metric.ball (0 : E) r) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C)
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hslice hD y (Metric.ball_subset_closedBall hy)).aestronglyMeasurable
        measurableSet_Icc |>.mono_set (fun t ht => hu t ht)
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact ae_of_all _ (fun t ht => hC (y, t) ⟨Metric.ball_subset_closedBall hy, hu t ht⟩)
    · exact intervalIntegrable_const
    · filter_upwards with t ht
      have hcx : ContinuousOn (fun y => D y t) (Metric.closedBall (0 : E) r) :=
        hD.comp (continuousOn_id.prodMk continuousOn_const) (fun _ hy => ⟨hy, hu t ht⟩)
      exact (hcx x (Metric.ball_subset_closedBall hx)).continuousAt
        (Metric.closedBall_mem_nhds_of_mem hx)
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) isOpen_ball).2
  refine ⟨fun x hx => (hder x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  apply contDiffOn_zero.mpr
  exact hc.congr (fun x hx => (hder x hx).fderiv)

/-- The linear graph direction associated with a finite-dimensional family. -/
def familyDirection {I : Interval} {m : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : E →L[ℝ] C1Curve I m) (t : ℝ) :
    E →L[ℝ] (ℝ × State m × State m) :=
  if ht : t ∈ Icc I.a I.b then
    (0 : E →L[ℝ] ℝ).prod
      (((ContinuousMap.evalCLM ℝ ⟨t, ht⟩).comp
        ((ContinuousLinearMap.fst ℝ _ _).comp ((curveJets I m).subtypeL.comp A))).prod
      ((ContinuousMap.evalCLM ℝ ⟨t, ht⟩).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp ((curveJets I m).subtypeL.comp A))))
  else 0

/-- C¹ integrands remain C¹ along every finite-dimensional affine family.
This is the analytic hypothesis needed by the source's implicit-function proof. -/
theorem action_finiteFamily_contDiffAt {I : Interval} {m : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Lagrangian m) (u : C1Curve I m) (hreg : regularNearGraph L u 1)
    (A : E →L[ℝ] C1Curve I m) :
    ContDiffAt ℝ 1 (fun x => action L (u + A x)) 0 := by
  obtain ⟨U, hU, hu, _, hL⟩ := hreg
  let G : E → ℝ → ℝ × State m × State m := fun x t =>
    (t, stateField I m (u + A x) t, velocityField I m (u + A x) t)
  have hdirection : ContinuousOn (familyDirection A) (Icc I.a I.b) := by
    apply continuousOn_clm_apply.mpr
    intro x
    exact ((continuousOn_const (c := (0 : ℝ))).prodMk ((stateField_continuousOn I m (A x)).prodMk
      (velocityField_continuousOn I m (A x)))).congr (fun t ht => by
        simp only [familyDirection, ContinuousLinearMap.prod_apply,
          zero_apply, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
          ContinuousLinearMap.fst, ContinuousLinearMap.snd, Submodule.subtypeL_apply,
          stateField, velocityField, extendState, dite_eq_left ht, C1Curve.state, C1Curve.velocity]
        rfl)
  have hcgraph : Continuous (fun z : E × I.Points => graphPoint (u + A z.1) z.2) := by
    have hs : Continuous (fun z : E × I.Points => (u + A z.1).state z.2) := by
      apply Continuous.eval
      · exact continuous_const.add (continuous_fst.comp
          (((curveJets I m).subtypeL.comp A).continuous.comp continuous_fst))
      · exact continuous_snd
    have hv : Continuous (fun z : E × I.Points => (u + A z.1).velocity z.2) := by
      apply Continuous.eval
      · exact continuous_const.add (continuous_snd.comp
          (((curveJets I m).subtypeL.comp A).continuous.comp continuous_fst))
      · exact continuous_snd
    exact (continuous_subtype_val.comp continuous_snd).prodMk (hs.prodMk hv)
  have he := (isCompact_univ : IsCompact (univ : Set I.Points)).eventually_forall_of_forall_eventually
    (x₀ := (0 : E)) (P := fun x t => graphPoint (u + A x) t ∈ U) (by
      intro t _
      have ht : graphPoint (u + A 0) t ∈ U := by simpa using hu t
      exact hcgraph.continuousAt.eventually (hU.mem_nhds ht))
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp he
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hmaps : MapsTo (Function.uncurry G) (Metric.closedBall (0 : E) r ×ˢ Icc I.a I.b) U := by
    intro z hz
    have hx : z.1 ∈ Metric.ball (0 : E) R := lt_of_le_of_lt hz.1 (half_lt_self hR)
    simpa only [G, Function.uncurry, graphPoint, stateField, velocityField, extendState, dite_eq_left hz.2] using hsub hx ⟨z.2, hz.2⟩ (mem_univ _)
  have hG : ContinuousOn (Function.uncurry G) (Metric.closedBall (0 : E) r ×ˢ Icc I.a I.b) := by
    -- Rewrite the restriction as the continuous compact-interval graph map.
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun z : ↥(Metric.closedBall (0 : E) r ×ˢ Icc I.a I.b) => G z.val.1 z.val.2)
    have heq : (fun z : ↥(Metric.closedBall (0 : E) r ×ˢ Icc I.a I.b) => G z.val.1 z.val.2) =
      (fun z => graphPoint (u + A z.val.1) ⟨z.val.2, z.property.2⟩) := by
      funext z
      simp only [G, graphPoint, stateField, velocityField, extendState, dite_eq_left z.property.2]
    rw [heq]
    exact hcgraph.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z => z.property.2)))
  let D : E → ℝ → E →L[ℝ] ℝ := fun x t => (fderiv ℝ L.value (G x t)).comp (familyDirection A t)
  have hD : ContinuousOn (Function.uncurry D) (Metric.closedBall (0 : E) r ×ˢ Icc I.a I.b) :=
    ((hL.continuousOn_fderiv_of_isOpen hU (by simp)).comp hG hmaps).clm_comp
      (hdirection.comp continuousOn_snd (fun _ hz => hz.2))
  have hder : ∀ x ∈ Metric.ball (0 : E) r, ∀ t ∈ Icc I.a I.b,
      HasFDerivAt (fun x => L.value (G x t)) (D x t) x := by
    intro x hx t ht
    have hp := hmaps (x := (x,t)) ⟨Metric.ball_subset_closedBall hx, ht⟩
    have hl := (hL.differentiableOn (by simp) _ hp).differentiableAt (hU.mem_nhds hp)
    have hg : HasFDerivAt (fun x => G x t) (familyDirection A t) x := by
      have heq : (fun x => G x t) = fun x => graphPoint u ⟨t, ht⟩ + familyDirection A t x := by
        funext y
        simp only [G, graphPoint, familyDirection, stateField, velocityField,
          extendState, C1Curve.state, C1Curve.velocity, dite_eq_left ht]
        change (t, u.state ⟨t, ht⟩ + (A y).state ⟨t, ht⟩,
          u.velocity ⟨t, ht⟩ + (A y).velocity ⟨t, ht⟩) =
          (t + 0, u.state ⟨t, ht⟩ + (A y).state ⟨t, ht⟩,
          u.velocity ⟨t, ht⟩ + (A y).velocity ⟨t, ht⟩)
        rw [add_zero]
      rw [heq]
      convert (hasFDerivAt_const (𝕜 := ℝ) (graphPoint u ⟨t, ht⟩) x).add
        (familyDirection A t).hasFDerivAt using 1 <;> simp only [zero_add]
    exact hl.hasFDerivAt.comp x hg
  have hresult := compactStrip_contDiffOn I (F := fun x t => L.value (G x t)) (D := D) hr
    (hL.continuousOn.comp hG hmaps) hD hder
  exact hresult.contDiffAt (Metric.ball_mem_nhds (0 : E) hr)


/-- The augmented integrand has precisely the original common open domain. -/
theorem augmented_regular {I : Interval} {m k : ℕ} (L : Lagrangian m)
    (Ls : Fin k → Lagrangian m) (u : C1Curve I m)
    (hL : regularNearGraph L u 1) (hLs : ∀ i, regularNearGraph (Ls i) u 1)
    (lam0 : ℝ) (lam : Fin k → ℝ) : regularNearGraph (augmented L Ls lam0 lam) u 1 := by
  classical
  obtain ⟨U, hU, hu, hsub, hc⟩ := hL
  choose Us hUs hus hsubs hcs using hLs
  let W := U ∩ ⋂ i, Us i
  have hWL : W ⊆ U := inter_subset_left
  have hWi (i : Fin k) : W ⊆ Us i := fun x hx => mem_iInter.mp hx.2 i
  refine ⟨W, hU.inter (isOpen_iInter_of_finite hUs), ?_, ?_, ?_⟩
  · intro t
    exact ⟨hu t, mem_iInter.mpr (fun i => hus i t)⟩
  · intro x hx
    exact ⟨hsub hx.1, mem_iInter.mpr (fun i => hsubs i (hWi i hx))⟩
  · exact ((hc.mono hWL).const_smul lam0).add
      (ContDiffOn.sum (fun i _ => ((hcs i).mono (hWi i)).const_smul (lam i)))

/-- Linearity in the integrands, proved at the derivative level before integrating. -/
theorem firstVariation_augmented {I : Interval} {m k : ℕ} (L : Lagrangian m)
    (Ls : Fin k → Lagrangian m) (u η : C1Curve I m)
    (hL : regularNearGraph L u 1) (hLs : ∀ i, regularNearGraph (Ls i) u 1)
    (lam0 : ℝ) (lam : Fin k → ℝ) :
    firstVariation (augmented L Ls lam0 lam) u η =
      lam0 * firstVariation L u η + ∑ i, lam i * firstVariation (Ls i) u η := by
  classical
  have hdiff {M : Lagrangian m} (hM : regularNearGraph M u 1) (t : I.Points) :
      DifferentiableAt ℝ M.value (graphPoint u t) := by
    obtain ⟨U, ho, hu, _, hc⟩ := hM
    exact (hc.differentiableOn (by simp) _ (hu t)).differentiableAt (ho.mem_nhds (hu t))
  have he : ∀ t ∈ Icc I.a I.b,
      variationDensity (momentumField (augmented L Ls lam0 lam) u)
        (stateGradientField (augmented L Ls lam0 lam) u)
        (stateField I m η) (velocityField I m η) t =
      lam0 * variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m η) (velocityField I m η) t +
      ∑ i, lam i * variationDensity (momentumField (Ls i) u) (stateGradientField (Ls i) u)
        (stateField I m η) (velocityField I m η) t := by
    intro t ht
    let x := graphPoint u ⟨t, ht⟩
    have hdA : HasFDerivAt (augmented L Ls lam0 lam).value
        (lam0 • fderiv ℝ L.value x + ∑ i, lam i • fderiv ℝ (Ls i).value x) x := by
      convert ((hdiff hL ⟨t, ht⟩).hasFDerivAt.const_mul lam0).add
        (HasFDerivAt.sum (u := Finset.univ) (fun i _ => ((hdiff (hLs i) ⟨t, ht⟩).hasFDerivAt.const_mul (lam i)))) using 1
      funext y
      simp only [augmented, Pi.add_apply, Finset.sum_apply]
    have hpoint {M : Lagrangian m} (hM : regularNearGraph M u 1) :
        variationDensity (momentumField M u) (stateGradientField M u)
          (stateField I m η) (velocityField I m η) t =
        fderiv ℝ M.value x (0, η.state ⟨t, ht⟩, η.velocity ⟨t, ht⟩) := by
      simpa only [variationDensity, momentumField, stateGradientField, stateField, velocityField,
        extendState, dite_eq_left ht, x] using
        variationDensity_eq_total M u ⟨t, ht⟩ (η.state ⟨t, ht⟩) (η.velocity ⟨t, ht⟩) (hdiff hM ⟨t, ht⟩)
    rw [hpoint (augmented_regular L Ls u hL hLs lam0 lam), hdA.fderiv]
    simp only [add_apply, sum_apply,
      smul_apply, smul_eq_mul]
    rw [hpoint hL]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hpoint (hLs i)]
  unfold firstVariation
  rw [intervalIntegral.integral_congr (fun t ht => he t (by
    simpa only [uIcc_of_le I.increasing.le] using ht))]
  have hint := IntervalIntegrable.sum Finset.univ (fun i _ =>
    (density_integrable (Ls i) u η (hLs i)).const_mul (lam i))
  have hint' : IntervalIntegrable (fun t => ∑ i, lam i *
      variationDensity (momentumField (Ls i) u) (stateGradientField (Ls i) u)
        (stateField I m η) (velocityField I m η) t) volume I.a I.b := by
    convert hint using 1
    funext t
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_add ((density_integrable L u η hL).const_mul lam0) hint']
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul]
  · intro i _
    exact (density_integrable (Ls i) u η (hLs i)).const_mul (lam i)

/-- Stationarity gives Euler–Lagrange by the accepted distributional primitive
result, so no differentiability of the original momentum is assumed. -/
theorem eulerLagrange_of_stationary {I : Interval} {m k : ℕ} (L : Lagrangian m)
    (Ls : Fin k → Lagrangian m) (u : C1Curve I m)
    (hL : regularNearGraph L u 1) (hLs : ∀ i, regularNearGraph (Ls i) u 1)
    (lam0 : ℝ) (lam : Fin k → ℝ) (hs : stationary L Ls u lam0 lam) :
    augmentedEulerLagrange L Ls u lam0 lam := by
  let A := augmented L Ls lam0 lam
  have hr : regularNearGraph A u 1 := augmented_regular L Ls u hL hLs lam0 lam
  have hz : ∀ η : C1Curve I m, η ∈ endpointZero I m → firstVariation A u η = 0 := by
    intro η hη
    rw [firstVariation_augmented L Ls u η hL hLs lam0 lam]
    exact hs ⟨η, hη⟩
  have hw := weakDerivative_of_endpoint_identity A u hz
  obtain ⟨hp, hq⟩ := gradientFields_continuousOn A u hr
  have hpc := hp.mono Ioo_subset_Icc_self
  have hqc := hq.mono Ioo_subset_Icc_self
  exact ⟨hw, distributionalPrimitiveContinuous m I.a I.b I.increasing
    (momentumField A u) (stateGradientField A u)
    (hpc.locallyIntegrableOn measurableSet_Ioo) (hqc.locallyIntegrableOn measurableSet_Ioo)
    hw hpc hqc⟩


/-- The Fréchet derivative of a finite slice agrees with the first-variation
integral in every parameter direction. -/
theorem action_family_fderiv {I : Interval} {m : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Lagrangian m) (u : C1Curve I m) (hreg : regularNearGraph L u 1)
    (A : E →L[ℝ] C1Curve I m) (d : E) :
    fderiv ℝ (fun x => action L (u + A x)) 0 d = firstVariation L u (A d) := by
  have h := (action_finiteFamily_contDiffAt L u hreg A).differentiableAt_one.hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => s • d) d 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const d
  have h' : HasFDerivAt (fun x => action L (u + A x))
      (fderiv ℝ (fun x => action L (u + A x)) 0) ((0 : ℝ) • d) := by
    simpa only [zero_smul] using h
  have hd := h'.comp_hasDerivAt 0 hline
  have hd' := classicalActionDerivative I m L u (A d) hreg
  have heq : (fun s : ℝ => action L (u + A (s • d))) =
      (fun s : ℝ => action L (u + s • A d)) := by
    funext s
    rw [map_smul]
  change HasDerivAt (fun s : ℝ => action L (u + A (s • d))) _ 0 at hd
  rw [heq] at hd
  exact hd.unique hd'

theorem action_family_hasFDerivAt {I : Interval} {m : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Lagrangian m) (u : C1Curve I m) (hreg : regularNearGraph L u 1)
    (A : E →L[ℝ] C1Curve I m) :
    HasFDerivAt (fun x => action L (u + A x))
      (LinearMap.toContinuousLinearMap ((firstVariationLinear L u hreg).comp A.toLinearMap)) 0 := by
  have he : fderiv ℝ (fun x => action L (u + A x)) 0 =
      LinearMap.toContinuousLinearMap ((firstVariationLinear L u hreg).comp A.toLinearMap) := by
    apply ContinuousLinearMap.ext
    intro d
    exact action_family_fderiv L u hreg A d
  rw [← he]
  exact (action_finiteFamily_contDiffAt L u hreg A).differentiableAt_one.hasFDerivAt

/-- Compactness of the time interval gives a common admissible neighborhood
for every finite-dimensional affine family. -/
theorem family_graph_eventually {I : Interval} {m : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Lagrangian m) (u : C1Curve I m) (hu : graphAdmissible L u)
    (A : E →L[ℝ] C1Curve I m) :
    ∀ᶠ x in 𝓝 (0 : E), graphAdmissible L (u + A x) := by
  have hs : Continuous (fun z : E × I.Points => (u + A z.1).state z.2) := by
    apply Continuous.eval
    · exact continuous_const.add (continuous_fst.comp
        (((curveJets I m).subtypeL.comp A).continuous.comp continuous_fst))
    · exact continuous_snd
  have hv : Continuous (fun z : E × I.Points => (u + A z.1).velocity z.2) := by
    apply Continuous.eval
    · exact continuous_const.add (continuous_snd.comp
        (((curveJets I m).subtypeL.comp A).continuous.comp continuous_fst))
    · exact continuous_snd
  have hc : Continuous (fun z : E × I.Points => graphPoint (u + A z.1) z.2) :=
    (continuous_subtype_val.comp continuous_snd).prodMk (hs.prodMk hv)
  have he := (isCompact_univ : IsCompact (univ : Set I.Points)).eventually_forall_of_forall_eventually
    (x₀ := (0 : E)) (P := fun x t => graphPoint (u + A x) t ∈ L.domain) (by
      intro t _
      have ht : graphPoint (u + A 0) t ∈ L.domain := by simpa using hu t
      exact hc.continuousAt.eventually (L.isOpen_domain.mem_nhds ht))
  simpa only [mem_univ, forall_const, graphAdmissible] using he

/-- Normal multiplier rule on the genuine C¹ variation space. Only the
finite-dimensional slices require completeness. -/
theorem normal_of_surjective {I : Interval} {m k : ℕ} (L : Lagrangian m)
    (Ls : Fin k → Lagrangian m) (u : C1Curve I m)
    (hL : regularNearGraph L u 1) (hLs : ∀ i, regularNearGraph (Ls i) u 1)
    (hm : constrainedLocalMinimum L Ls u)
    (hs : Function.Surjective (constraintDerivative Ls u)) :
    ∃! lam : Fin k → ℝ, stationary L Ls u 1 lam := by
  classical
  let V := endpointZero I m
  let Y := Fin k → ℝ
  let D := constraintLinear Ls u hLs
  let F := (firstVariationLinear L u hL).comp V.subtype
  have hsur : Function.Surjective D := hs
  obtain ⟨R, hR⟩ := D.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsur)
  have hright (y : Y) : D (R y) = y := congrArg (fun T : Y →ₗ[ℝ] Y => T y) hR
  let nu : Y →ₗ[ℝ] ℝ := -(F.comp R)
  let lam : Fin k → ℝ := fun i => nu (Pi.single i 1)
  have hnormal : stationary L Ls u 1 lam := by
    intro η
    let E := ℝ × Y
    let A : E →ₗ[ℝ] V := (LinearMap.fst ℝ ℝ Y).smulRight η +
      R.comp (LinearMap.snd ℝ ℝ Y)
    have hAc : Continuous (fun x : E => (A x : C1Curve I m)) := by
      apply continuous_induced_rng.mpr
      exact ((curveJets I m).subtype.comp (V.subtype.comp A)).continuous_of_finiteDimensional
    let Ac : E →L[ℝ] C1Curve I m := { toLinearMap := V.subtype.comp A, cont := hAc }
    let f : E → ℝ := fun x => action L (u + Ac x)
    let H : E → Y := fun x i => action (Ls i) (u + Ac x) - action (Ls i) u
    let B : E →L[ℝ] Y := LinearMap.toContinuousLinearMap (D.comp A)
    have hB : HasFDerivAt H B 0 := by
      apply hasFDerivAt_pi''
      intro i
      convert (action_family_hasFDerivAt (Ls i) u (hLs i) Ac).sub_const (action (Ls i) u) using 1
      apply ContinuousLinearMap.ext
      intro x
      rfl
    have hHC : ContDiffAt ℝ 1 H 0 :=
      contDiffAt_pi.mpr (fun i => (action_finiteFamily_contDiffAt (Ls i) u (hLs i) Ac).sub contDiffAt_const)
    obtain ⟨W, hW, hCW⟩ := hHC.contDiffOn (le_refl 1) (by simp)
    obtain ⟨U, hUW, hU, h0U⟩ := _root_.mem_nhds_iff.mp hW
    have h0H : H 0 = 0 := by
      apply funext
      intro i
      simp [H, Ac]
      rfl
    have hsurB : Function.Surjective B := by
      intro y
      refine ⟨(0, y), ?_⟩
      change D (A (0, y)) = y
      have he : A (0, y) = R y := by
        change (0 : ℝ) • η + R y = R y
        rw [zero_smul, zero_add]
      rw [he]
      exact hright y
    have hmin : IsLocalMinOn f (U ∩ H ⁻¹' {0}) 0 := by
      obtain ⟨hadm, hadms, ε, hε, hmin⟩ := hm
      have hnc : Continuous (fun x : E => ‖(Ac x).val‖) :=
        (((curveJets I m).subtypeL.comp Ac).continuous).norm
      have hnorm : ∀ᶠ x in 𝓝 (0 : E), ‖Ac x‖ < ε := by
        exact (hnc.continuousAt (x := (0 : E))).eventually
          (gt_mem_nhds (by simpa only [map_zero, ZeroMemClass.coe_zero, norm_zero] using hε))
      have hcomp : ∀ᶠ x in 𝓝 (0 : E), ∀ i, graphAdmissible (Ls i) (u + Ac x) :=
        Filter.eventually_all.mpr (fun i => family_graph_eventually (Ls i) u (hadms i) Ac)
      filter_upwards [hnorm.filter_mono nhdsWithin_le_nhds,
        (family_graph_eventually L u hadm Ac).filter_mono nhdsWithin_le_nhds,
        hcomp.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hax hasx hset
      have hxH : H x = 0 := hset.2
      have hcon : ∀ i, action (Ls i) (u + Ac x) = action (Ls i) u := by
        intro i
        have hi := congrFun hxH i
        exact sub_eq_zero.mp hi
      have hcancel : (u + Ac x) - u = Ac x := by
        apply Subtype.ext
        apply Prod.ext <;> ext t <;> exact add_sub_cancel_left _ _
      have hv : (u + Ac x) - u ∈ V := by
        rw [hcancel]
        exact (A x).property
      have hn : ‖(u + Ac x) - u‖ < ε := by rw [hcancel]; exact hx
      simpa only [f, map_zero, add_zero] using hmin (u + Ac x) hv hax hasx hcon hn
    obtain ⟨ν, hν, _⟩ := Ch06.EqualityMultipliers.finiteTargetEqualityMultipliers
      E Y 1 (le_refl 1) U hU H (hCW.mono hUW) 0 h0U h0H B hB hsurB f
      (action_finiteFamily_contDiffAt L u hL Ac).differentiableAt_one hmin
    have heq (x : E) : F (A x) + ν (D (A x)) = 0 := by
      have he := congrArg (fun T : E →L[ℝ] ℝ => T x) hν
      change fderiv ℝ f 0 x + ν (B x) = 0 at he
      rw [action_family_fderiv L u hL Ac] at he
      exact he
    have hnu (y : Y) : ν y = nu y := by
      have he := heq (0, y)
      have hAr : A (0, y) = R y := by
        change (0 : ℝ) • η + R y = R y
        rw [zero_smul, zero_add]
      rw [hAr, hright] at he
      exact eq_neg_of_add_eq_zero_right he
    have hAη : A (1, 0) = η := by
      change (1 : ℝ) • η + R 0 = η
      rw [one_smul, map_zero, add_zero]
    have he := heq (1, 0)
    rw [hAη, hnu, dual_coordinates] at he
    change firstVariation L u η + (∑ i, lam i * constraintDerivative Ls u η i) = 0 at he
    simpa only [one_mul] using he
  refine ⟨lam, hnormal, ?_⟩
  intro mu hmu
  have hcov : ∀ y : Y, (∑ i, mu i * y i) = ∑ i, lam i * y i := by
    intro y
    obtain ⟨η, hη⟩ := hs y
    have h1 := hmu η
    have h2 := hnormal η
    simp only [one_mul] at h1
    simp only [one_mul] at h2
    rw [hη] at h1 h2
    linarith
  ext i
  simpa [Pi.single_apply] using hcov (Pi.single i 1)


/-- Isoperimetric multipliers and the Euler–Lagrange equation of the same
augmented integrand, including normal uniqueness and the abnormal alternative. -/
theorem isoperimetricMultipliers : Specs.IsoperimetricMultipliersType := by
  intro I m k L Ls u hL hLs hm
  classical
  have hn : Function.Surjective (constraintDerivative Ls u) →
      ∃! lam : Fin k → ℝ, stationary L Ls u 1 lam ∧ augmentedEulerLagrange L Ls u 1 lam := by
    intro hs
    obtain ⟨lam, hstat, huniq⟩ := normal_of_surjective L Ls u hL hLs hm hs
    exact ⟨lam, ⟨hstat, eulerLagrange_of_stationary L Ls u hL hLs 1 lam hstat⟩,
      fun mu hmu => huniq mu hmu.1⟩
  have ha : ¬ Function.Surjective (constraintDerivative Ls u) →
      ∃ lam : Fin k → ℝ, lam ≠ 0 ∧ stationary L Ls u 0 lam ∧
        augmentedEulerLagrange L Ls u 0 lam := by
    intro hs
    obtain ⟨lam, hne, hstat⟩ := abnormal_of_not_surjective L Ls u hLs hs
    exact ⟨lam, hne, hstat, eulerLagrange_of_stationary L Ls u hL hLs 0 lam hstat⟩
  refine ⟨?_, hn, ha⟩
  by_cases hs : Function.Surjective (constraintDerivative Ls u)
  · obtain ⟨lam, hstat, _⟩ := hn hs
    exact ⟨1, lam, zero_le_one, Or.inl one_ne_zero, hstat⟩
  · obtain ⟨lam, hne, hstat⟩ := ha hs
    exact ⟨0, lam, le_refl 0, Or.inr hne, hstat⟩


/-- The empty-index convention is covered without a nonemptiness assumption. -/
theorem emptyConstraints : Specs.EmptyConstraintsType := by
  intro I m L u hL hm
  let Ls : Fin 0 → Lagrangian m := fun i => Fin.elim0 i
  have hLs : ∀ i, regularNearGraph (Ls i) u 1 := fun i => Fin.elim0 i
  have hs : Function.Surjective (constraintDerivative Ls u) := by
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨lam, hstat, _⟩ := (isoperimetricMultipliers I m 0 L Ls u hL hLs hm).2.1 hs
  have he : lam = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
  rw [he] at hstat
  exact hstat

end VariationalNotes.Classical.IsoperimetricMultipliers
