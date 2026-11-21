import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.EvenWave
import MathGenome.Internal.LinearPDE.P201.Hyperbolic.OddWave
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace P201.EvenWave

abbrev projection : P201Specs.EvenWave.ProjectionType := P201Specs.EvenWave.projection
abbrev inclusion : P201Specs.EvenWave.InclusionType := P201Specs.EvenWave.inclusion
abbrev lift : P201Specs.EvenWave.LiftType := @P201Specs.EvenWave.lift
abbrev liftedMean : P201Specs.EvenWave.LiftedMeanType := @P201Specs.EvenWave.liftedMean
abbrev weightedBallMean : P201Specs.EvenWave.WeightedBallMeanType :=
  @P201Specs.EvenWave.weightedBallMean
abbrev velocityEven : P201Specs.EvenWave.VelocityEvenType := @P201Specs.EvenWave.velocityEven
abbrev velocityTwoBall : P201Specs.EvenWave.VelocityTwoBallType :=
  @P201Specs.EvenWave.velocityTwoBall

@[simp] theorem projection_apply {n : ℕ} (y : Space (n + 1)) (i : Fin n) :
    projection n y i = y i.castSucc := rfl

@[simp] theorem inclusion_castSucc {n : ℕ} (x : Space n) (i : Fin n) :
    inclusion n x i.castSucc = x i := by
  change @Fin.snoc n (fun _ => ℝ) (fun j => x j) 0 i.castSucc = x i
  simp

@[simp] theorem inclusion_last {n : ℕ} (x : Space n) :
    inclusion n x (Fin.last n) = 0 := by
  change @Fin.snoc n (fun _ => ℝ) (fun j => x j) 0 (Fin.last n) = 0
  simp

@[simp] theorem projection_inclusion {n : ℕ} (x : Space n) :
    projection n (inclusion n x) = x := by
  ext i
  exact inclusion_castSucc x i

@[simp] theorem lift_inclusion {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (h : Space n → 𝕜) (x : Space n) : lift h (inclusion n x) = h x := by
  change h (projection n (inclusion n x)) = h x
  rw [projection_inclusion]

theorem lift_contDiff {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {h : Space n → 𝕜} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (lift h) := hh.comp (projection n).contDiff

/-- A lifted spherical mean depends on its center only through its first n coordinates. -/
theorem sphericalMean_lift {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (h : Space n → 𝕜) (y : Space (n + 1)) (r : ℝ) :
    OddWave.sphericalMean (lift h) y r = liftedMean h (projection n y) r := by
  change (P201Specs.omega (n + 1))⁻¹ •
      (∫ θ, h (projection n (y + r • θ)) ∂P201Specs.unitSurface (n + 1)) =
    (P201Specs.omega (n + 1))⁻¹ •
      (∫ θ, h (projection n (inclusion n (projection n y) + r • θ))
        ∂P201Specs.unitSurface (n + 1))
  simp only [map_add, map_smul, projection_inclusion]

/-- Independence of the discarded coordinate survives all radial differentiations. -/
theorem velocityOdd_lift {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (h : Space n → 𝕜) (t : ℝ) (y : Space (n + 1)) :
    OddWave.velocityOdd c (lift h) t y = velocityEven c h t (projection n y) := by
  have he : OddWave.sphericalMean (lift h) y =
      OddWave.sphericalMean (lift h) (inclusion n (projection n y)) := by
    funext r
    exact sphericalMean_lift h y r
  change (if t = 0 then 0 else _ • OddWave.radialIterate _
    (fun r => r ^ _ • OddWave.sphericalMean (lift h) y r) _) =
    (if t = 0 then 0 else _ • OddWave.radialIterate _
    (fun r => r ^ _ • OddWave.sphericalMean (lift h) (inclusion n (projection n y)) r) _)
  rw [he]

theorem velocity_even_formula : P201Specs.EvenWave.VelocityEvenFormulaStatement := by
  intro n hn _ 𝕜 _ c _ h t x
  constructor
  · intro ht
    change (if t = 0 then 0 else _) = _
    rw [ite_eq_right ht]
    simp only [show n + 1 - 2 = n - 1 by omega,
      show n + 1 - 3 = n - 2 by omega]
    rfl
  · exact OddWave.velocityOdd_zero c (lift h) (inclusion n x)

@[simp] theorem projection_coordinate_castSucc {n : ℕ} (i : Fin n) :
    projection n (coordinate (n + 1) i.castSucc) = coordinate n i := by
  ext j
  simp [P201.coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single]

@[simp] theorem projection_coordinate_last (n : ℕ) :
    projection n (coordinate (n + 1) (Fin.last n)) = 0 := by
  ext j
  simp [P201.coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single]

/-- The chain rule for a directional derivative of a lifted function. -/
theorem directional_lift {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {h : Space n → 𝕜} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (v y : Space (n + 1)) :
    OddWave.directional (lift h) v y =
      OddWave.directional h (projection n v) (projection n y) := by
  unfold OddWave.directional
  change fderiv ℝ (h ∘ projection n) y v = _
  rw [fderiv_comp y (hh.differentiable (by simp) _)
    (projection n).differentiableAt, (projection n).fderiv]
  rfl

/-- The last second derivative vanishes and all other second derivatives
are precisely their n-dimensional counterparts. -/
theorem laplacian_lift {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {h : Space n → 𝕜} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (y : Space (n + 1)) :
    laplacian (lift h) y = laplacian h (projection n y) := by
  rw [OddWave.laplacian_eq_sum_directional, OddWave.laplacian_eq_sum_directional]
  have he (v : Space (n + 1)) : OddWave.directional (lift h) v =
      lift (OddWave.directional h (projection n v)) :=
    funext fun z => directional_lift hh v z
  simp_rw [he]
  simp_rw [directional_lift (OddWave.directional_contDiff hh _)]
  rw [Fin.sum_univ_castSucc]
  simp only [projection_coordinate_castSucc, projection_coordinate_last,
    OddWave.directional, map_zero, add_zero]

/-- Descent preserves joint smoothness, the wave equation and the initial jets. -/
theorem velocity_even : P201Specs.EvenWave.VelocityEvenStatement := by
  intro n hn hneven 𝕜 _ c hc h hh
  have hnodd : Odd (n + 1) := by
    obtain ⟨k, hk⟩ := hneven
    exact ⟨k, by omega⟩
  obtain ⟨hs, hw, hi⟩ := OddWave.velocity_odd (by omega) hnodd c hc (lift h)
    (lift_contDiff hh)
  have hsm : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Space n => velocityEven c h p.1 p.2) := by
    exact hs.comp (contDiff_fst.prodMk ((inclusion n).contDiff.comp contDiff_snd))
  refine ⟨hsm, ?_, ?_⟩
  · intro t x
    have hsp : ContDiff ℝ (⊤ : ℕ∞) (velocityEven c h t) :=
      hsm.comp (contDiff_const.prodMk contDiff_id)
    have he : OddWave.velocityOdd c (lift h) t = lift (velocityEven c h t) :=
      funext fun y => velocityOdd_lift c h t y
    change deriv (deriv (fun s => OddWave.velocityOdd c (lift h) s (inclusion n x))) t = _
    rw [hw]
    change c ^ 2 • laplacian (OddWave.velocityOdd c (lift h) t) (inclusion n x) =
      c ^ 2 • laplacian (velocityEven c h t) x
    rw [he, laplacian_lift hsp, projection_inclusion]
  · intro x
    simpa only [velocityEven, P201Specs.EvenWave.velocityEven, lift_inclusion] using
      hi (inclusion n x)

/-- Exact Euclidean disk/ball volumes and the sphere mass appearing in descent. -/
theorem surface_ball_constants : P201Specs.EvenWave.SurfaceBallConstantsStatement := by
  have h2 : (volume : Measure (Space 2)).real (Metric.ball 0 1) = Real.pi := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_two]
    simp [Real.pi_nonneg]
  have h3 : (volume : Measure (Space 3)).real (Metric.ball 0 1) = 4 * Real.pi / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  refine ⟨?_, h2, h3⟩
  change (P201Specs.unitSurface 3).real univ = _
  rw [P201.unitSurfaceMass, h3]
  norm_num
  ring

/-- Translation and dilation of a ball, with the Euclidean Jacobian. -/
theorem integral_ball_affine {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Space n → 𝕜) (x : Space n) {R : ℝ} (hR : 0 < R) :
    (∫ y in Metric.ball x R, f y) =
      R ^ n • ∫ z in Metric.ball (0 : Space n) 1, f (x + R • z) := by
  have ht : (fun y : Space n => x + y) ⁻¹' Metric.ball x R =
      Metric.ball (0 : Space n) R := by
    ext y
    simp [Metric.mem_ball, dist_eq_norm]
  have hi := (measurePreserving_add_left (volume : Measure (Space n)) x).setIntegral_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding f (Metric.ball x R)
  rw [ht] at hi
  rw [← hi, MeasureTheory.Measure.setIntegral_comp_smul_of_pos volume
    (fun y : Space n => f (x + y)) (Metric.ball 0 1) hR,
    smul_unitBall_of_pos hR]
  simp only [Space, P201Specs.Space, finrank_euclideanSpace, Fintype.card_fin, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero n hR.ne'), one_smul]

/-- The square-root weight transforms with one inverse power of the radius. -/
theorem sqrt_ball_affine {n : ℕ} (x z : Space n) {R : ℝ} (hR : 0 < R) :
    Real.sqrt (R ^ 2 - ‖x + R • z - x‖ ^ 2) =
      R * Real.sqrt (1 - ‖z‖ ^ 2) := by
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]
  rw [show R ^ 2 - (R * ‖z‖) ^ 2 = R ^ 2 * (1 - ‖z‖ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR.le]

/-- The n=2 change of variables, including the exact power of ct. -/
theorem poisson_integral_scale {𝕜 : Type} [RCLike 𝕜]
    (h : Space 2 → 𝕜) (x : Space 2) {R : ℝ} (hR : 0 < R) :
    (∫ y in Metric.ball x R,
      (Real.sqrt (R ^ 2 - ‖y - x‖ ^ 2))⁻¹ • h y) =
      R • ∫ z in Metric.ball (0 : Space 2) 1,
        (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • h (x + R • z) := by
  rw [integral_ball_affine _ x hR]
  simp_rw [sqrt_ball_affine x _ hR, mul_inv_rev, ← smul_smul]
  have he : (fun z : Space 2 => (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ •
      R⁻¹ • h (x + R • z)) = fun z => R⁻¹ •
      (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • h (x + R • z) := by
    funext z
    exact smul_comm _ _ _
  rw [he, integral_smul, smul_smul]
  congr 1
  field_simp

/-- The endpoint singularity is integrable; this estimate also applies to
continuous data with no global bound or support assumption. -/
theorem radial_sqrt_weight_integrable :
    IntegrableOn (fun r : ℝ => (Real.sqrt (1-r))⁻¹) (Ioo 0 1) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
    (by norm_num : (-1 : ℝ) < -(1/2 : ℝ))).comp_sub_left 1
  have hi : IntegrableOn (fun r : ℝ => (1-r) ^ (-(1/2 : ℝ))) (Ioo 0 1) := by
    simpa using h.symm.1.mono_set Ioo_subset_Ioc_self
  apply hi.congr_fun _ measurableSet_Ioo
  intro r hr
  rcases hr with ⟨hr0, hr1⟩
  dsimp only
  rw [Real.rpow_neg (by linarith : 0 ≤ 1-r), ← Real.sqrt_eq_rpow]

theorem sqrt_weight_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    IntegrableOn (fun z : E => (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹) (Metric.ball 0 1) μ := by
  apply (integrableOn_fun_norm_addHaar μ (f := fun r : ℝ => (Real.sqrt (1-r^2))⁻¹)).mpr
  apply radial_sqrt_weight_integrable.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rcases hr with ⟨hr0, hr1⟩
  have hsq : r ^ 2 ≤ r := by nlinarith [sq_nonneg r]
  have hp : 0 < Real.sqrt (1-r) := Real.sqrt_pos.mpr (by linarith)
  have hp' : 0 < Real.sqrt (1-r^2) := Real.sqrt_pos.mpr (by nlinarith)
  have hinv : (Real.sqrt (1-r^2))⁻¹ ≤ (Real.sqrt (1-r))⁻¹ :=
    (inv_le_inv₀ hp' hp).mpr (Real.sqrt_le_sqrt (by linarith))
  have hpow : r ^ (Module.finrank ℝ E - 1) ≤ 1 := pow_le_one₀ hr0.le hr1.le
  rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hr0.le _), abs_of_nonneg (inv_nonneg.mpr hp'.le)]
  exact (mul_le_of_le_one_left (inv_nonneg.mpr hp'.le) hpow).trans hinv

theorem weighted_continuous_integrable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) (hf : Continuous f) :
    IntegrableOn (fun z : E => (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • f z)
      (Metric.ball 0 1) μ := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E) 1).exists_bound_of_continuousOn hf.continuousOn
  apply (sqrt_weight_integrable μ).smul_bdd C hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact hC z (Metric.ball_subset_closedBall hz)

theorem weighted_parametric_continuous {X E F : Type*}
    [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) (w : E → ℝ) (hw : IntegrableOn w (Metric.ball 0 1) μ)
    (f : X → E → F) (hf : Continuous f.uncurry) :
    Continuous (fun p => ∫ z in Metric.ball (0:E) 1, w z • f p z ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨U, hUc, hUn⟩ := exists_compact_mem_nhds p₀
  obtain ⟨C, hC⟩ := (hUc.prod (isCompact_closedBall (0:E) 1)).exists_bound_of_continuousOn hf.continuousOn
  apply continuousAt_of_dominated (bound := fun z => ‖w z‖ * C)
  · filter_upwards with p
    exact hw.aestronglyMeasurable.smul (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [hUn] with p hp
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (p,z) ⟨hp, Metric.ball_subset_closedBall hz⟩) (norm_nonneg _)
  · exact hw.norm.mul_const C
  · filter_upwards with z
    exact ContinuousAt.const_smul (by fun_prop) _

theorem weighted_ball_joint_continuous {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) (hf : Continuous f) :
    Continuous (fun p : E × ℝ => ∫ z in Metric.ball (0:E) 1,
      (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • f (p.1 + p.2 • z) ∂μ) := by
  apply weighted_parametric_continuous μ _ (sqrt_weight_integrable μ)
  fun_prop

/-- Splitting off the last coordinate preserves Euclidean Lebesgue volume. -/
def splitLast (n : ℕ) : Space (n + 1) ≃ᵐ Space n × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm |>.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).trans
      ((MeasurableEquiv.prodComm).trans
        ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).prodCongr (MeasurableEquiv.refl ℝ))))

@[simp] theorem splitLast_apply {n : ℕ} (y : Space (n + 1)) :
    splitLast n y = (projection n y, y (Fin.last n)) := by
  apply Prod.ext
  · ext i
    change y ((Fin.last n).succAbove i) = y i.castSucc
    simp
  · rfl

theorem splitLast_measurePreserving (n : ℕ) :
    MeasurePreserving (splitLast n) volume volume := by
  apply MeasurePreserving.comp
    (MeasurePreserving.comp
      ((PiLp.volume_preserving_toLp (Fin n)).prod (MeasurePreserving.id volume))
      (Measure.measurePreserving_swap))
    (MeasurePreserving.comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))
      (PiLp.volume_preserving_ofLp (Fin (n + 1))))

theorem norm_sq_projection_last {n : ℕ} (y : Space (n + 1)) :
    ‖y‖ ^ 2 = ‖projection n y‖ ^ 2 + (y (Fin.last n)) ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [Fin.sum_univ_castSucc]
  rfl

@[simp] theorem projection_splitLast_symm {n : ℕ} (p : Space n × ℝ) :
    projection n ((splitLast n).symm p) = p.1 := by
  have h := (splitLast n).apply_symm_apply p
  rw [splitLast_apply] at h
  exact congrArg Prod.fst h

@[simp] theorem last_splitLast_symm {n : ℕ} (p : Space n × ℝ) :
    (splitLast n).symm p (Fin.last n) = p.2 := by
  have h := (splitLast n).apply_symm_apply p
  rw [splitLast_apply] at h
  exact congrArg Prod.snd h

theorem norm_sq_splitLast_symm {n : ℕ} (p : Space n × ℝ) :
    ‖(splitLast n).symm p‖ ^ 2 = ‖p.1‖ ^ 2 + p.2 ^ 2 := by
  rw [norm_sq_projection_last, projection_splitLast_symm, last_splitLast_symm]

theorem splitLast_symm_mem_ball {n : ℕ} (z : Space n) (t : ℝ)
    {R : ℝ} (hR : 0 < R) :
    (splitLast n).symm (z, t) ∈ Metric.ball 0 R ↔
      z ∈ Metric.ball 0 R ∧ t ∈ Ioo (-Real.sqrt (R ^ 2 - ‖z‖ ^ 2))
        (Real.sqrt (R ^ 2 - ‖z‖ ^ 2)) := by
  simp only [Metric.mem_ball, dist_zero_right, mem_Ioo]
  rw [← sq_lt_sq₀ (norm_nonneg _) hR.le, norm_sq_splitLast_symm]
  constructor
  · intro ht
    have hz : ‖z‖ < R := (sq_lt_sq₀ (norm_nonneg _) hR.le).mp (by nlinarith [sq_nonneg t])
    have hp : 0 ≤ R ^ 2 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hs := Real.sq_sqrt hp
    have hsn := Real.sqrt_nonneg (R ^ 2 - ‖z‖ ^ 2)
    refine ⟨hz, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hz, hl, hu⟩
    have hp : 0 ≤ R ^ 2 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hs := Real.sq_sqrt hp
    have hm := mul_pos (sub_pos.mpr hu) (sub_pos.mpr hl)
    nlinarith


theorem cylindrical_ball_slicing {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Space n → 𝕜) (hf : Continuous f) {R : ℝ} (hR : 0 < R) :
    (∫ y in Metric.ball (0 : Space (n+1)) R, f (projection n y)) =
      (2 : ℝ) • ∫ z in Metric.ball (0 : Space n) R,
        Real.sqrt (R^2 - ‖z‖^2) • f z := by
  let g : Space (n+1) → 𝕜 := (Metric.ball 0 R).indicator (fun y => f (projection n y))
  have hfi : IntegrableOn (fun y : Space (n+1) => f (projection n y)) (Metric.ball 0 R) := by
    exact (ContinuousOn.integrableOn_compact (isCompact_closedBall (0:Space (n+1)) R)
      (by fun_prop)).mono_set Metric.ball_subset_closedBall
  have hgi : Integrable g volume := (integrable_indicator_iff measurableSet_ball).mpr hfi
  have hmp := (splitLast_measurePreserving n).symm
  have hpi := hmp.integrable_comp_of_integrable hgi
  change Integrable (fun p => g ((splitLast n).symm p)) (volume.prod volume) at hpi
  calc
    _ = ∫ y, g y := (integral_indicator measurableSet_ball).symm
    _ = ∫ p : Space n × ℝ, g ((splitLast n).symm p) := (hmp.integral_comp' g).symm
    _ = ∫ z : Space n, ∫ t : ℝ, g ((splitLast n).symm (z,t)) := integral_prod _ hpi
    _ = ∫ z in Metric.ball (0:Space n) R,
        (2 * Real.sqrt (R^2 - ‖z‖^2)) • f z := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ Metric.ball (0:Space n) R
      · rw [indicator_of_mem hz]
        have hinner : (fun t : ℝ => g ((splitLast n).symm (z,t))) =
            (Ioo (-Real.sqrt (R^2-‖z‖^2)) (Real.sqrt (R^2-‖z‖^2))).indicator (fun _ => f z) := by
          funext t
          simp [g, indicator, splitLast_symm_mem_ball z t hR, hz]
        rw [hinner, integral_indicator measurableSet_Ioo, integral_const]
        simp [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal,
          sub_neg_eq_add, two_mul, Real.sqrt_nonneg]
      · have hinner : (fun t : ℝ => g ((splitLast n).symm (z,t))) = 0 := by
          funext t
          simp [g, indicator, splitLast_symm_mem_ball z t hR, hz]
        simp [hinner, hz]
    _ = _ := by rw [← integral_smul]; apply setIntegral_congr_fun measurableSet_ball; intro z hz; simp [mul_smul]


lemma sqrt_kernel_primitive {a r : ℝ} (ha : 0 ≤ a) (har : a ≤ r) :
    IntegrableOn (fun s : ℝ => s * (Real.sqrt (s ^ 2 - a ^ 2))⁻¹) (Ioo a r) ∧
    (∫ s in Ioo a r, s * (Real.sqrt (s ^ 2 - a ^ 2))⁻¹) =
      Real.sqrt (r ^ 2 - a ^ 2) := by
  have hc : ContinuousOn (fun s : ℝ => Real.sqrt (s ^ 2 - a ^ 2)) (Icc a r) := by fun_prop
  have hd : ∀ s ∈ Ioo a r,
      HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 - a ^ 2))
        (s * (Real.sqrt (s ^ 2 - a ^ 2))⁻¹) s := by
    intro s hs
    have hpos : 0 < s ^ 2 - a ^ 2 := by nlinarith [hs.1]
    have hd0 : HasDerivAt (fun s : ℝ => s ^ 2 - a ^ 2) (2 * s) s := by
      convert (((hasDerivAt_id s).pow 2).sub_const (a ^ 2)) using 1 <;> simp
    convert hd0.sqrt hpos.ne' using 1 <;> field_simp <;> ring
  have hn : ∀ s ∈ Ioo a r, 0 ≤ s * (Real.sqrt (s ^ 2 - a ^ 2))⁻¹ := by
    intro s hs
    exact mul_nonneg (ha.trans hs.1.le) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hi := intervalIntegral.integrableOn_deriv_of_nonneg hc hd hn
  refine ⟨hi.mono_set Ioo_subset_Ioc_self, ?_⟩
  have hiv : IntervalIntegrable (fun s : ℝ => s * (Real.sqrt (s ^ 2 - a ^ 2))⁻¹) volume a r := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le har).mpr hi
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le har,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le har hc hd hiv]
  simp

private def sqrtKernel (a s : ℝ) : ℝ :=
  (Ioi a).indicator (fun s => s * (Real.sqrt (s ^ 2 - a ^ 2))⁻¹) s

lemma sqrt_kernel_interval {a r : ℝ} (ha : 0 ≤ a) (har : a ≤ r) :
    IntegrableOn (sqrtKernel a) (Ioo 0 r) ∧
    (∫ s in Ioo 0 r, sqrtKernel a s) = Real.sqrt (r ^ 2 - a ^ 2) := by
  obtain ⟨hi,he⟩ := sqrt_kernel_primitive ha har
  have hi' : Ioo 0 r ∩ Ioi a = Ioo a r := by
    ext s
    simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
    constructor
    · rintro ⟨⟨hs0,hsr⟩,has⟩; exact ⟨has,hsr⟩
    · rintro ⟨has,hsr⟩; exact ⟨⟨ha.trans_lt has,hsr⟩,has⟩
  constructor
  · unfold sqrtKernel
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi]
    simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_Ioi,
      inter_comm (Ioi a), hi'] using hi
  · unfold sqrtKernel
    rw [setIntegral_indicator measurableSet_Ioi, hi']
    exact he


private lemma sqrtKernel_nonneg {a s : ℝ} (hs : 0 ≤ s) : 0 ≤ sqrtKernel a s := by
  unfold sqrtKernel
  by_cases has : a < s
  · simpa [has] using
      mul_nonneg hs (inv_nonneg.mpr (Real.sqrt_nonneg (s ^ 2 - a ^ 2)))
  · simp [has]

lemma sqrt_layer_cake {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) (hf : Continuous f)
    {r : ℝ} (_hr : 0 ≤ r) :
    (∫ z in Metric.ball (0 : E) r, Real.sqrt (r ^ 2 - ‖z‖ ^ 2) • f z ∂μ) =
      ∫ s in Ioo 0 r, s • ∫ z in Metric.ball (0 : E) s,
        (Real.sqrt (s ^ 2 - ‖z‖ ^ 2))⁻¹ • f z ∂μ := by
  let K : E × ℝ → F := fun p => sqrtKernel ‖p.1‖ p.2 • f p.1
  have hmK : StronglyMeasurable K := by
    have hm : Measurable (fun p : E × ℝ => sqrtKernel ‖p.1‖ p.2) := by
      unfold sqrtKernel
      simp only [indicator_apply, mem_Ioi]
      exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
        (by fun_prop) measurable_const
    exact hm.stronglyMeasurable.smul (hf.comp continuous_fst).stronglyMeasurable
  have hin : ∀ z ∈ Metric.ball (0 : E) r,
      IntegrableOn (fun s => K (z,s)) (Ioo 0 r) := by
    intro z hz
    have hzr : ‖z‖ ≤ r := (by simpa using hz : ‖z‖ < r).le
    exact (sqrt_kernel_interval (norm_nonneg z) hzr).1.smul_const (f z)
  have hnorm : ∀ z ∈ Metric.ball (0 : E) r,
      (∫ s in Ioo 0 r, ‖K (z,s)‖) = Real.sqrt (r ^ 2 - ‖z‖ ^ 2) * ‖f z‖ := by
    intro z hz
    have hzr : ‖z‖ ≤ r := (by simpa using hz : ‖z‖ < r).le
    calc
      _ = ∫ s in Ioo 0 r, sqrtKernel ‖z‖ s * ‖f z‖ := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro s hs
        simp only [K, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (sqrtKernel_nonneg hs.1.le)]
      _ = _ := by rw [integral_mul_const, (sqrt_kernel_interval (norm_nonneg z) hzr).2]
  have hni : Integrable (fun z => ∫ s in Ioo 0 r, ‖K (z,s)‖) (μ.restrict (Metric.ball 0 r)) := by
    have hc : Continuous (fun z : E => Real.sqrt (r ^ 2 - ‖z‖ ^ 2) * ‖f z‖) := by fun_prop
    have hi : IntegrableOn (fun z : E => Real.sqrt (r ^ 2 - ‖z‖ ^ 2) * ‖f z‖)
        (Metric.ball 0 r) μ :=
      (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) r)).mono_set
        Metric.ball_subset_closedBall
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact (hnorm z hz).symm
  have hKi : Integrable K ((μ.restrict (Metric.ball 0 r)).prod (volume.restrict (Ioo 0 r))) := by
    apply (integrable_prod_iff hmK.aestronglyMeasurable).mpr
    refine ⟨?_,hni⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hin z hz
  have hleft : (∫ z in Metric.ball (0 : E) r, ∫ s in Ioo 0 r, K (z,s) ∂volume ∂μ) =
      ∫ z in Metric.ball (0 : E) r, Real.sqrt (r ^ 2 - ‖z‖ ^ 2) • f z ∂μ := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    change (∫ s in Ioo 0 r, sqrtKernel ‖z‖ s • f z) = _
    have hzr : ‖z‖ ≤ r := (by simpa using hz : ‖z‖ < r).le
    rw [integral_smul_const, (sqrt_kernel_interval (norm_nonneg z) hzr).2]
  rw [← hleft, integral_integral_swap hKi]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hs
  have hsub : Metric.ball (0 : E) r ∩ Metric.ball 0 s = Metric.ball 0 s := by
    exact inter_eq_right.mpr (Metric.ball_subset_ball hs.2.le)
  calc
    (∫ z in Metric.ball (0 : E) r, K (z,s) ∂μ) =
        ∫ z in Metric.ball (0 : E) r, (Metric.ball (0 : E) s).indicator
          (fun z => s • ((Real.sqrt (s ^ 2 - ‖z‖ ^ 2))⁻¹ • f z)) z ∂μ := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : ‖z‖ < s
      · simp [K, sqrtKernel, hz, Metric.mem_ball, dist_zero_right, mul_smul]
      · simp [K, sqrtKernel, hz, Metric.mem_ball, dist_zero_right]
    _ = _ := by rw [setIntegral_indicator measurableSet_ball, hsub, integral_smul]


lemma radial_weighted_ball_scale {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Space n → 𝕜) {s : ℝ} (hs : 0 < s) :
    s • (∫ z in Metric.ball (0 : Space n) s,
      (Real.sqrt (s ^ 2 - ‖z‖ ^ 2))⁻¹ • f z) =
    s ^ n • (∫ z in Metric.ball (0 : Space n) 1,
      (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • f (s • z)) := by
  rw [integral_ball_affine _ 0 hs]
  simp only [zero_add]
  have hsq (z : Space n) : Real.sqrt (s ^ 2 - ‖s • z‖ ^ 2) =
      s * Real.sqrt (1 - ‖z‖ ^ 2) := by
    simpa only [zero_add, sub_zero] using sqrt_ball_affine (0 : Space n) z hs
  simp_rw [hsq, mul_inv_rev, ← smul_smul]
  have he : (fun z : Space n => (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ •
      s⁻¹ • f (s • z)) = fun z => s⁻¹ •
      (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • f (s • z) := by
    funext z; exact smul_comm _ _ _
  rw [he, integral_smul, smul_smul, smul_smul]
  congr 1
  field_simp

/-- Projection of the actual Haar surface measure has the two-hemisphere
inverse-square-root density. The proof compares derivatives of cylindrical
ball integrals, using their Euclidean slices and the radial primitive. -/
theorem sphere_projection : P201Specs.EvenWave.SphereProjectionStatement := by
  intro n hn 𝕜 _ f hf
  have hslice (R : ℝ) (hR : 0 < R) := cylindrical_ball_slicing f hf hR
  letI : NeZero n := ⟨by omega⟩
  let W : ℝ → 𝕜 := fun s => ∫ z in Metric.ball (0 : Space n) 1,
    (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • f (s • z)
  have hW : Continuous W := by
    simpa only [Function.comp_def, W, zero_add] using
      (weighted_ball_joint_continuous (volume : Measure (Space n)) f hf).comp
        (show Continuous (fun s : ℝ => ((0 : Space n),s)) by fun_prop)
  let B : ℝ → 𝕜 := fun s => (2 : ℝ) • (s ^ n • W s)
  have hB : Continuous B := by exact continuous_const.smul ((continuous_id.pow n).smul hW)
  have hV (R : ℝ) (hR : 0 < R) :
      (∫ y in Metric.ball (0 : Space (n + 1)) R, f (projection n y)) =
      ∫ s in Ioo 0 R, B s := by
    rw [hslice R hR, sqrt_layer_cake volume f hf hR.le, ← integral_smul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro s hs
    change (2 : ℝ) • (s • ∫ z in Metric.ball (0 : Space n) s,
      (Real.sqrt (s ^ 2 - ‖z‖ ^ 2))⁻¹ • f z) = B s
    rw [radial_weighted_ball_scale f hs.1]
  have hVB : HasDerivAt (fun R : ℝ =>
      ∫ y in Metric.ball (0 : Space (n + 1)) R, f (projection n y)) (B 1) 1 := by
    have hd := intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ)) (b := (1 : ℝ))
      (hB.intervalIntegrable 0 1) hB.aestronglyMeasurable.stronglyMeasurableAtFilter hB.continuousAt
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with R hR
    rw [hV R hR, intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo]
  have hVS := MeanValues.ballIntegral_hasDerivAt (by omega : 1 ≤ n + 1)
    (⊤ : Domain (n + 1)) (fun y => f (projection n y))
    ((hf.comp (projection n).continuous).continuousOn)
    (0 : Space (n + 1)) 1 (by norm_num) (by simp)
  refine ⟨weighted_continuous_integrable volume f hf, ?_⟩
  have he := hVS.unique hVB
  simpa only [one_pow, one_smul, zero_add, B, W] using he

/-- Reduce the normalized mean formula to an unnormalized geometric integral. -/
theorem lifted_mean_ball_of_projection :
    P201Specs.EvenWave.LiftedMeanBallFromProjectionStatement := by
  intro hproj n hn _ 𝕜 _ h hh x r
  let f : Space n → 𝕜 := fun z => h (x + r • z)
  have hf : Continuous f :=
    hh.continuous.comp (continuous_const.add (continuous_id.const_smul r))
  obtain ⟨hi, he⟩ := hproj hn f hf
  refine ⟨hi, ?_⟩
  change (P201Specs.omega (n + 1))⁻¹ •
      (∫ θ, h (projection n (inclusion n x + r • θ)) ∂P201Specs.unitSurface (n + 1)) =
    (2 / P201Specs.omega (n + 1)) •
      ∫ z in Metric.ball (0 : Space n) 1,
        (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ • f z
  simp only [map_add, map_smul, projection_inclusion]
  change (P201Specs.omega (n + 1))⁻¹ •
      (∫ θ, f (projection n θ) ∂P201Specs.unitSurface (n + 1)) = _
  rw [he, smul_smul]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

/-- Once the geometric mean identity is known, the two-dimensional
positive-time formula follows from scaling; there is no analytic PDE premise. -/
theorem velocity_two_ball_of_liftedMean :
    P201Specs.EvenWave.VelocityTwoBallFromMeanStatement := by
  intro hmean 𝕜 _ c hc h hh
  have he (t : ℝ) (x : Space 2) (ht : 0 < t) :
      velocityEven c h t x = velocityTwoBall c h t x := by
    have hm := (hmean (by omega) (show Even 2 from ⟨1, rfl⟩) h hh x (c * t)).2
    have hv := OddWave.velocity_three c hc (lift h) t (inclusion 2 x)
    change velocityEven c h t x = t • liftedMean h x (c * t) at hv
    change liftedMean h x (c * t) = weightedBallMean h x (c * t) at hm
    rw [hv, hm]
    change t • ((2 / P201Specs.omega 3) • _) = _
    rw [surface_ball_constants.1]
    change t • ((2 / (4 * Real.pi)) • _) =
      (if t = 0 then 0 else (2 * Real.pi * c)⁻¹ • _)
    rw [ite_eq_right ht.ne']
    rw [show c ^ 2 * t ^ 2 = (c * t) ^ 2 by ring,
      poisson_integral_scale h x (mul_pos hc ht), smul_smul, smul_smul]
    congr 1
    field_simp
    ring
  refine ⟨fun t x ht => he t x ht, ?_⟩
  intro x
  have hs := (velocity_even (by omega) (show Even 2 from ⟨1, rfl⟩) c hc h hh).1
  have hcont : Continuous (fun t : ℝ => velocityEven c h t x) :=
    hs.continuous.comp (continuous_id.prodMk continuous_const)
  have heq : (fun t : ℝ => velocityTwoBall c h t x) =ᶠ[nhdsWithin 0 (Ici 0)]
      (fun t : ℝ => velocityEven c h t x) := by
    filter_upwards [self_mem_nhdsWithin] with t ht0
    by_cases ht : 0 < t
    · exact (he t x ht).symm
    · have htzero : t = 0 := le_antisymm (le_of_not_gt ht) ht0
      subst t
      simp [velocityTwoBall, P201Specs.EvenWave.velocityTwoBall, velocityEven,
        P201Specs.EvenWave.velocityEven, OddWave.velocityOdd_zero]
  refine ⟨by simp [P201Specs.EvenWave.velocityTwoBall], ?_⟩
  apply hcont.continuousWithinAt.congr_of_eventuallyEq heq
  simp [velocityTwoBall, P201Specs.EvenWave.velocityTwoBall, velocityEven,
    P201Specs.EvenWave.velocityEven, OddWave.velocityOdd_zero]

/-- The lifted normalized spherical mean equals its weighted-ball formula
at every real radius, including zero. -/
theorem lifted_mean_ball : P201Specs.EvenWave.LiftedMeanBallStatement :=
  lifted_mean_ball_of_projection sphere_projection

/-- The exact positive-time Poisson formula in dimension two, with its
continuous value at zero. -/
theorem velocity_two_ball : P201Specs.EvenWave.VelocityTwoBallStatement :=
  velocity_two_ball_of_liftedMean lifted_mean_ball

end P201.EvenWave
