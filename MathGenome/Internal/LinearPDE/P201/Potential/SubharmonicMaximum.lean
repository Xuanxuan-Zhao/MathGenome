import MathGenome.Internal.LinearPDE.P201Specs.Potential.SubharmonicMaximum
import MathGenome.Internal.LinearPDE.P201.Potential.MeanValues
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace P201.SubharmonicMaximum

abbrev extendedIntegral : P201Specs.SubharmonicMaximum.ExtendedIntegralType :=
  @P201Specs.SubharmonicMaximum.extendedIntegral
abbrev extendedAverage : P201Specs.SubharmonicMaximum.ExtendedAverageType :=
  @P201Specs.SubharmonicMaximum.extendedAverage
abbrev HasSphereSubmean : P201Specs.SubharmonicMaximum.SubmeanType :=
  @P201Specs.SubharmonicMaximum.HasSphereSubmean
abbrev HasBallSubmean : P201Specs.SubharmonicMaximum.SubmeanType :=
  @P201Specs.SubharmonicMaximum.HasBallSubmean
abbrev IsAdmissible : P201Specs.SubharmonicMaximum.SubmeanType :=
  @P201Specs.SubharmonicMaximum.IsAdmissible
abbrev IsSubharmonic : P201Specs.SubharmonicMaximum.SubmeanType :=
  @P201Specs.SubharmonicMaximum.IsSubharmonic
abbrev HasRealSphereSubmean : P201Specs.SubharmonicMaximum.RealSubmeanType :=
  @P201Specs.SubharmonicMaximum.HasRealSphereSubmean
abbrev HasRealBallSubmean : P201Specs.SubharmonicMaximum.RealSubmeanType :=
  @P201Specs.SubharmonicMaximum.HasRealBallSubmean

theorem compact_upper_bound : P201Specs.SubharmonicMaximum.CompactUpperBoundStatement := by
  intro n Ω u hu htop K hK hKΩ
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨0, by simp [h]⟩
  · obtain ⟨a, ha, hmax⟩ := (hu.mono hKΩ).exists_isMaxOn h hK
    obtain ⟨C, hC, _⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr (htop a (hKΩ ha)))
    exact ⟨C, fun x hx => (hmax hx).trans hC.le⟩

theorem real_average_bridge : P201Specs.SubharmonicMaximum.RealAverageBridgeStatement := by
  intro n μ u hu
  unfold P201Specs.SubharmonicMaximum.extendedAverage
    P201Specs.SubharmonicMaximum.extendedIntegral
  simp only [← EReal.coe_neg, EReal.real_coe_toENNReal]
  have hneg : Integrable (fun x => -u x) μ := hu.neg
  rw [← EReal.coe_ennreal_toReal hu.lintegral_lt_top.ne,
    ← EReal.coe_ennreal_toReal hneg.lintegral_lt_top.ne,
    ← EReal.coe_sub, ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hu,
    ← EReal.coe_inv, ← EReal.coe_mul]

/-- The shared surface measure is carried by its geometric sphere. -/
theorem sphereSurface_ae_mem {n : ℕ} (a : P201Specs.Space n) (r : ℝ) (hr : 0 ≤ r) :
    ∀ᵐ x ∂P201Specs.sphereSurface a r, x ∈ sphere a r := by
  unfold P201Specs.sphereSurface
  apply Measure.ae_smul_measure
  apply (MeasureTheory.ae_map_iff (by fun_prop) isClosed_sphere.measurableSet).mpr
  filter_upwards [P201.MeanValues.unitSurface_ae_mem n] with θ hθ
  have hnorm : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
  simp [dist_eq_norm, norm_smul, hnorm, abs_of_nonneg hr]

theorem positivePart_finite_of_ae_upper_bound {n : ℕ} (μ : Measure (P201Specs.Space n))
    [IsFiniteMeasure μ] (u : P201Specs.Space n → EReal) (C : ℝ)
    (hC : ∀ᵐ x ∂μ, u x ≤ (C : EReal)) :
    (∫⁻ x, (u x).toENNReal ∂μ) < ⊤ := by
  calc
    (∫⁻ x, (u x).toENNReal ∂μ) ≤ ∫⁻ _ : P201Specs.Space n, ENNReal.ofReal C ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hC] with x hx
      exact EReal.toENNReal_le_toENNReal hx
    _ < ⊤ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem positivePart_finite : P201Specs.SubharmonicMaximum.PositivePartFiniteStatement := by
  intro n _ Ω u hu htop a r hr hball
  obtain ⟨C, hC⟩ := compact_upper_bound Ω u hu htop (closedBall a r)
    (isCompact_closedBall a r) hball
  constructor
  · apply positivePart_finite_of_ae_upper_bound _ u C
    filter_upwards [sphereSurface_ae_mem a r hr.le] with x hx
    exact hC x (sphere_subset_closedBall hx)
  · let : IsFiniteMeasure (volume.restrict (ball a r)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    apply positivePart_finite_of_ae_upper_bound _ u C
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hC x (ball_subset_closedBall hx)

theorem sphere_integrable_of_continuousOn {n : ℕ} (Ω : P201Specs.Domain n)
    (u : P201Specs.Space n → ℝ) (hc : ContinuousOn u Ω)
    (a : P201Specs.Space n) (r : ℝ) (hr : 0 ≤ r)
    (hball : closedBall a r ⊆ (Ω : Set _)) : Integrable u (P201Specs.sphereSurface a r) := by
  have hi := (hc.mono (sphere_subset_closedBall.trans hball)).integrableOn_compact
    (μ := P201Specs.sphereSurface a r) (isCompact_sphere a r)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (sphereSurface_ae_mem a r hr)] at hi

theorem continuous_submean_bridge :
    P201Specs.SubharmonicMaximum.ContinuousSubmeanBridgeStatement := by
  intro n _ Ω u hc
  have hs (a : P201Specs.Space n) (r : ℝ) (hr : 0 < r)
      (hball : closedBall a r ⊆ (Ω : Set _)) :
      (u a : EReal) ≤ extendedAverage (P201Specs.sphereSurface a r) (fun x => (u x : EReal)) ↔
        u a ≤ P201Specs.sphereAverage u a r := by
    dsimp only [extendedAverage]
    rw [real_average_bridge _ _ (sphere_integrable_of_continuousOn Ω u hc a r hr.le hball)]
    exact EReal.coe_le_coe_iff
  have hb (a : P201Specs.Space n) (r : ℝ) (_hr : 0 < r)
      (hball : closedBall a r ⊆ (Ω : Set _)) :
      (u a : EReal) ≤ extendedAverage (volume.restrict (ball a r)) (fun x => (u x : EReal)) ↔
        u a ≤ P201Specs.ballAverage u a r := by
    have hi : IntegrableOn u (ball a r) :=
      ((hc.mono hball).integrableOn_compact (isCompact_closedBall a r)).mono_set
        ball_subset_closedBall
    dsimp only [extendedAverage]
    rw [real_average_bridge _ _ hi, measureReal_restrict_apply_univ]
    exact EReal.coe_le_coe_iff
  constructor
  · exact ⟨fun h a r hr hball => (hs a r hr hball).mp (h a r hr hball),
      fun h a r hr hball => (hs a r hr hball).mpr (h a r hr hball)⟩
  · exact ⟨fun h a r hr hball => (hb a r hr hball).mp (h a r hr hball),
      fun h a r hr hball => (hb a r hr hball).mpr (h a r hr hball)⟩

/-- Nonnegative Laplacian makes each spherical mean increase from its center value. -/
theorem real_sphere_submean_of_laplacian_nonneg {n : ℕ} (hn : 1 ≤ n)
    (Ω : P201Specs.Domain n) (u : P201Specs.Space n → ℝ)
    (hu : ContDiffOn ℝ 2 u Ω) (hΔ : ∀ x ∈ Ω, 0 ≤ P201Specs.laplacian u x) :
    HasRealSphereSubmean Ω u := by
  intro a r hr hball
  have hsmall {s : ℝ} (hs : s ∈ Icc (0 : ℝ) r) :
      closedBall a s ⊆ (Ω : Set _) :=
    (closedBall_subset_closedBall hs.2).trans hball
  have hc : ContinuousOn (P201.MeanValues.unitSphereMean u a) (Icc (0 : ℝ) r) := by
    intro s hs
    exact (P201.MeanValues.angular_derivative Ω u (hu.of_le (by norm_num)) a s hs.1
      (hsmall hs)).continuousAt.continuousWithinAt
  have hd (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) r) :=
    P201.MeanValues.spherical_mean_derivative hn Ω u hu a s hs.1
      (hsmall ⟨hs.1.le, hs.2.le⟩)
  have hmono : MonotoneOn (P201.MeanValues.unitSphereMean u a) (Icc (0 : ℝ) r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc
    · intro s hs
      rw [interior_Icc] at hs
      exact (hd s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s hs).deriv]
      change 0 ≤ (P201Specs.omega n * s ^ (n - 1))⁻¹ * _
      apply mul_nonneg (inv_nonneg.mpr (mul_nonneg (P201.MeanValues.omega_pos hn).le
        (pow_nonneg hs.1.le _)))
      apply setIntegral_nonneg measurableSet_ball
      intro x hx
      exact hΔ x (hsmall ⟨hs.1.le, hs.2.le⟩ (ball_subset_closedBall hx))
  have hle := hmono ⟨le_rfl, hr.le⟩ ⟨hr.le, le_rfl⟩ hr.le
  rw [P201.MeanValues.unitSphereMean_zero hn] at hle
  rwa [P201.MeanValues.sphere_mean_normalization hn u a r hr]

/-- A negative Laplacian on a neighborhood contradicts the spherical submean
inequality at its center, by strictly decreasing spherical means. -/
theorem laplacian_nonneg_of_real_sphere_submean {n : ℕ} (hn : 1 ≤ n)
    (Ω : P201Specs.Domain n) (u : P201Specs.Space n → ℝ)
    (hu : ContDiffOn ℝ 2 u Ω) (hmean : HasRealSphereSubmean Ω u) :
    ∀ a ∈ Ω, 0 ≤ P201Specs.laplacian u a := by
  intro a ha
  by_contra h
  have hneg : P201Specs.laplacian u a < 0 := lt_of_not_ge h
  let c := P201Specs.laplacian u a / 2
  have hcneg : c < 0 := by dsimp [c]; linarith
  have hcont := (P201.MeanValues.laplacian_continuousOn Ω u hu).continuousAt
    (Ω.isOpen.mem_nhds ha)
  have hnb : ∀ᶠ x in 𝓝 a, x ∈ Ω ∧ P201Specs.laplacian u x < c :=
    by
      filter_upwards [Ω.isOpen.mem_nhds ha,
        hcont.eventually_lt_const (show P201Specs.laplacian u a < c by dsimp [c]; linarith)] with x hx hxc
      exact ⟨hx, hxc⟩
  obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp hnb
  let r := ε / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hball : closedBall a r ⊆ (Ω : Set _) := by
    intro x hx
    exact (hεprop ((closedBall_subset_ball (by dsimp [r]; linarith)) hx)).1
  have hbound : ∀ x ∈ closedBall a r, P201Specs.laplacian u x ≤ c := by
    intro x hx
    exact (hεprop ((closedBall_subset_ball (by dsimp [r]; linarith)) hx)).2.le
  have hsmall {s : ℝ} (hs : s ∈ Icc (0 : ℝ) r) :
      closedBall a s ⊆ (Ω : Set _) :=
    (closedBall_subset_closedBall hs.2).trans hball
  have hc : ContinuousOn (P201.MeanValues.unitSphereMean u a) (Icc (0 : ℝ) r) := by
    intro s hs
    exact (P201.MeanValues.angular_derivative Ω u (hu.of_le (by norm_num)) a s hs.1
      (hsmall hs)).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn (P201.MeanValues.unitSphereMean u a) (Icc (0 : ℝ) r) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc
    intro s hs
    rw [interior_Icc] at hs
    have hi : IntegrableOn (P201Specs.laplacian u) (ball a s) :=
      ((P201.MeanValues.laplacian_continuousOn Ω u hu).mono
        (hsmall ⟨hs.1.le, hs.2.le⟩)).integrableOn_compact
        (isCompact_closedBall a s) |>.mono_set ball_subset_closedBall
    have hle : (∫ x in ball a s, P201Specs.laplacian u x) ≤
        volume.real (ball a s) * c := by
      simpa only [setIntegral_const, smul_eq_mul] using
        setIntegral_mono_on hi (integrableOn_const measure_ball_lt_top.ne)
          measurableSet_ball (fun x hx => hbound x
            (closedBall_subset_closedBall hs.2.le (ball_subset_closedBall hx)))
    have hv : 0 < volume.real (ball a s) :=
      ENNReal.toReal_pos (measure_ball_pos volume a hs.1).ne' measure_ball_lt_top.ne
    have hlt : (∫ x in ball a s, P201Specs.laplacian u x) < 0 :=
      hle.trans_lt (mul_neg_of_pos_of_neg hv hcneg)
    rw [(P201.MeanValues.spherical_mean_derivative hn Ω u hu a s hs.1
      (hsmall ⟨hs.1.le, hs.2.le⟩)).deriv]
    change (P201Specs.omega n * s ^ (n - 1))⁻¹ * _ < 0
    exact mul_neg_of_pos_of_neg (inv_pos.mpr
      (mul_pos (P201.MeanValues.omega_pos hn) (pow_pos hs.1 _))) hlt
  have hlt := hanti ⟨le_rfl, hr.le⟩ ⟨hr.le, le_rfl⟩ hr
  rw [P201.MeanValues.unitSphereMean_zero hn] at hlt
  have hle := hmean a r hr hball
  rw [P201.MeanValues.sphere_mean_normalization hn u a r hr] at hle
  exact (not_lt_of_ge hle) hlt

theorem smooth_sphere_criterion : P201Specs.SubharmonicMaximum.SmoothSphereCriterionStatement := by
  intro n hn Ω u hu
  have hn' : 1 ≤ n := by omega
  exact ⟨laplacian_nonneg_of_real_sphere_submean hn' Ω u hu,
    real_sphere_submean_of_laplacian_nonneg hn' Ω u hu⟩

/-- Continuous spherical submeans imply ball submeans by polar integration.
The shifted integrand is used so only nonnegativity is integrated. -/
theorem real_sphere_implies_ball {n : ℕ} (hn : 1 ≤ n)
    (Ω : P201Specs.Domain n) (u : P201Specs.Space n → ℝ)
    (hc : ContinuousOn u Ω) (hs : HasRealSphereSubmean Ω u) :
    HasRealBallSubmean Ω u := by
  intro a r hr hball
  have hi : IntegrableOn u (ball a r) :=
    ((hc.mono hball).integrableOn_compact (isCompact_closedBall a r)).mono_set
      ball_subset_closedBall
  have hshift : 0 ≤ ∫ x in ball a r, u x - u a := by
    have hvi : IntegrableOn (fun x => u x - u a) (ball a r) :=
      hi.sub (integrableOn_const measure_ball_lt_top.ne)
    rw [P201.MeanValues.integral_ball_polar hn a r hvi]
    apply setIntegral_nonneg measurableSet_Ioo
    intro s hs'
    apply mul_nonneg (pow_nonneg hs'.1.le _)
    have hsmall : closedBall a s ⊆ (Ω : Set _) :=
      (closedBall_subset_closedBall hs'.2.le).trans hball
    have hθ : Integrable (fun θ => u (a + s • θ)) (P201Specs.unitSurface n) := by
      apply P201.MeanValues.unitSurface_integrable_of_continuousOn
      apply hc.comp (by fun_prop)
      intro θ hθ
      apply hsmall
      have hnθ : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hnθ,
        mul_one, Real.norm_eq_abs, abs_of_pos hs'.1]
      exact le_rfl
    rw [integral_sub hθ (integrable_const _), integral_const]
    change 0 ≤ (∫ θ, u (a + s • θ) ∂P201Specs.unitSurface n) - P201Specs.omega n * u a
    apply sub_nonneg.mpr
    have hm := hs a s hs'.1 hsmall
    rw [P201.MeanValues.sphere_mean_normalization hn u a s hs'.1] at hm
    change u a ≤ (P201Specs.omega n)⁻¹ * _ at hm
    calc
      P201Specs.omega n * u a ≤ P201Specs.omega n *
          ((P201Specs.omega n)⁻¹ * ∫ θ, u (a + s • θ) ∂P201Specs.unitSurface n) :=
        mul_le_mul_of_nonneg_left hm (P201.MeanValues.omega_pos hn).le
      _ = _ := by
        rw [← mul_assoc, mul_inv_cancel₀ (P201.MeanValues.omega_pos hn).ne', one_mul]
  have hv : 0 < volume.real (ball a r) :=
    ENNReal.toReal_pos (measure_ball_pos volume a hr).ne' measure_ball_lt_top.ne
  have he : P201Specs.ballAverage u a r - u a = (volume.real (ball a r))⁻¹ *
      ∫ x in ball a r, u x - u a := by
    change (volume.real (ball a r))⁻¹ * (∫ x in ball a r, u x) - u a = _
    rw [integral_sub hi (integrableOn_const measure_ball_lt_top.ne), setIntegral_const,
      smul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hv.ne', one_mul]
  exact sub_nonneg.mp (he ▸ mul_nonneg (inv_nonneg.mpr hv.le) hshift)

/-- The ball converse can be reduced to the harmonic converse locally: on a
region where Δu < 0, -u has positive Laplacian. Both ball inequalities would
then be equalities, contradicting harmonicity. -/
theorem smooth_ball_criterion : P201Specs.SubharmonicMaximum.SmoothBallCriterionStatement := by
  intro n hn Ω u hu
  have hn' : 1 ≤ n := by omega
  constructor
  · intro hm a ha
    by_contra h
    have hneg : P201Specs.laplacian u a < 0 := lt_of_not_ge h
    have hcont := (P201.MeanValues.laplacian_continuousOn Ω u hu).continuousAt
      (Ω.isOpen.mem_nhds ha)
    have hnb : ∀ᶠ x in 𝓝 a, x ∈ Ω ∧ P201Specs.laplacian u x < 0 := by
      filter_upwards [Ω.isOpen.mem_nhds ha, hcont.eventually_lt_const hneg] with x hx hΔ
      exact ⟨hx, hΔ⟩
    obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp hnb
    let V : P201Specs.Domain n := ⟨ball a ε, isOpen_ball⟩
    have hVΩ : (V : Set (P201Specs.Space n)) ⊆ (Ω : Set (P201Specs.Space n)) := fun x hx => (hεprop hx).1
    have hcu : ContDiffOn ℝ 2 u V := hu.mono hVΩ
    have hminus : HasRealBallSubmean V (fun x => -u x) := by
      apply real_sphere_implies_ball hn' V _ hcu.neg.continuousOn
      apply real_sphere_submean_of_laplacian_nonneg hn' V _ hcu.neg
      intro x hx
      rw [P201.MeanValues.laplacian_bridge _ x
        (hcu.neg.contDiffAt (V.isOpen.mem_nhds hx))]
      change 0 ≤ Laplacian.laplacian (-u) x
      rw [InnerProductSpace.laplacian_neg]
      change 0 ≤ -Laplacian.laplacian u x
      rw [← P201.MeanValues.laplacian_bridge u x (hcu.contDiffAt (V.isOpen.mem_nhds hx))]
      exact neg_nonneg.mpr (hεprop hx).2.le
    have hmean : P201.MeanValues.HasBallMeanValue V u := by
      intro b r hr hball
      apply le_antisymm (hm b r hr (hball.trans hVΩ))
      have h := hminus b r hr hball
      change -u b ≤ (volume.real (ball b r))⁻¹ * (∫ x in ball b r, -u x) at h
      rw [integral_neg, mul_neg] at h
      exact neg_le_neg_iff.mp h
    have hh := P201.MeanValues.ball_converse hn' V u hcu.continuousOn hmean
    have hz := hh.2.2 a (show a ∈ V from mem_ball_self hε)
    exact hneg.ne hz
  · intro hΔ
    exact real_sphere_implies_ball hn' Ω u hu.continuousOn
      (real_sphere_submean_of_laplacian_nonneg hn' Ω u hu hΔ)

theorem real_admissible {n : ℕ} (Ω : P201Specs.Domain n)
    (u : P201Specs.Space n → ℝ) (hc : ContinuousOn u Ω) :
    IsAdmissible Ω (fun x => (u x : EReal)) := by
  refine ⟨(continuous_coe_real_ereal.comp_continuousOn hc).upperSemicontinuousOn,
    fun x _ => EReal.coe_ne_top (u x), ?_⟩
  intro a ha
  exact ⟨a, mem_connectedComponentIn ha, EReal.coe_ne_bot (u a)⟩

theorem smooth_subharmonic_criterion :
    P201Specs.SubharmonicMaximum.SmoothSubharmonicCriterionStatement := by
  intro n hn Ω u hu
  constructor
  · intro h
    exact (smooth_sphere_criterion hn Ω u hu).mp
      ((continuous_submean_bridge hn Ω u hu.continuousOn).1.mp h.2)
  · intro hΔ
    exact ⟨real_admissible Ω u hu.continuousOn,
      (continuous_submean_bridge hn Ω u hu.continuousOn).1.mpr
        ((smooth_sphere_criterion hn Ω u hu).mpr hΔ)⟩

theorem smooth_extended_ball_criterion :
    P201Specs.SubharmonicMaximum.SmoothExtendedBallCriterionStatement := by
  intro n hn Ω u hu
  exact (continuous_submean_bridge hn Ω u hu.continuousOn).2.trans
    (smooth_ball_criterion hn Ω u hu)

/-- Monotonicity also holds when the lower integral is negatively infinite. -/
theorem extendedAverage_mono {n : ℕ} (μ : Measure (P201Specs.Space n))
    (u v : P201Specs.Space n → EReal) (h : u ≤ᵐ[μ] v) :
    extendedAverage μ u ≤ extendedAverage μ v := by
  apply mul_le_mul_of_nonneg_left _ (EReal.coe_nonneg.mpr (inv_nonneg.mpr ENNReal.toReal_nonneg))
  apply EReal.sub_le_sub
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono_ae (h.mono fun x hx => EReal.toENNReal_le_toENNReal hx))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono_ae (h.mono fun x hx => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hx)))

/-- A strict upper bound on a set of positive measure makes the average strictly
smaller than a finite common upper bound. No integrability of `u` is assumed. -/
theorem extendedAverage_lt_of_upper_bound {n : ℕ} (μ : Measure (P201Specs.Space n))
    [IsFiniteMeasure μ] (hμ : 0 < μ.real univ)
    (u : P201Specs.Space n → EReal) (m c : ℝ) (hcm : c < m)
    (T : Set (P201Specs.Space n)) (hT : MeasurableSet T) (hpos : 0 < μ.real T)
    (hm : ∀ᵐ x ∂μ, u x ≤ (m : EReal))
    (hc : ∀ᵐ x ∂μ, x ∈ T → u x ≤ (c : EReal)) :
    extendedAverage μ u < (m : EReal) := by
  let v : P201Specs.Space n → ℝ := fun x => m - T.indicator (fun _ => m - c) x
  have hi : Integrable v μ := (integrable_const m).sub
    ((integrable_const (m - c)).indicator hT)
  have huv : u ≤ᵐ[μ] (fun x => (v x : EReal)) := by
    filter_upwards [hm, hc] with x hx hxT
    by_cases hx' : x ∈ T
    · simpa [v, indicator_of_mem hx'] using hxT hx'
    · simpa [v, indicator_of_notMem hx'] using hx
  apply (extendedAverage_mono μ u _ huv).trans_lt
  dsimp only [extendedAverage]
  rw [real_average_bridge μ v hi]
  apply EReal.coe_lt_coe_iff.mpr
  have he : (∫ x, v x ∂μ) = μ.real univ * m - μ.real T * (m - c) := by
    rw [integral_sub (integrable_const m) ((integrable_const (m - c)).indicator hT)]
    simp [integral_indicator hT, integral_const, smul_eq_mul]
  rw [he, mul_sub, ← mul_assoc, inv_mul_cancel₀ hμ.ne', one_mul]
  exact sub_lt_self _ (mul_pos (inv_pos.mpr hμ) (mul_pos hpos (sub_pos.mpr hcm)))

/-- At a finite maximum, the ball inequality forces equality throughout every
ball on which that maximum bounds the function. -/
theorem ball_constant_of_max {n : ℕ} (Ω : P201Specs.Domain n)
    (u : P201Specs.Space n → EReal) (hu : UpperSemicontinuousOn u (Ω : Set _))
    (hmean : HasBallSubmean Ω u) (a : P201Specs.Space n) (r : ℝ) (hr : 0 < r)
    (hball : closedBall a r ⊆ (Ω : Set _)) (m : ℝ) (ha : u a = (m : EReal))
    (hm : ∀ x ∈ ball a r, u x ≤ (m : EReal)) :
    ∀ x ∈ ball a r, u x = (m : EReal) := by
  intro b hb
  by_contra hne
  obtain ⟨c, hbc, hcm⟩ := EReal.exists_between_coe_real (lt_of_le_of_ne (hm b hb) hne)
  have hnb : ∀ᶠ x in 𝓝 b, x ∈ ball a r ∧ u x < (c : EReal) := by
    have huc := hu b (hball (ball_subset_closedBall hb)) (c : EReal) hbc
    rw [nhdsWithin_eq_nhds.mpr (Ω.isOpen.mem_nhds (hball (ball_subset_closedBall hb)))] at huc
    filter_upwards [isOpen_ball.mem_nhds hb, huc] with x hx hux
    exact ⟨hx, hux⟩
  obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp hnb
  let μ : Measure (P201Specs.Space n) := volume.restrict (ball a r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hμ : 0 < μ.real univ := by
    rw [measureReal_restrict_apply_univ]
    exact ENNReal.toReal_pos (measure_ball_pos volume a hr).ne' measure_ball_lt_top.ne
  have hT : 0 < μ.real (ball b ε) := by
    have hsub : ball b ε ⊆ ball a r := fun x hx => (hεprop hx).1
    rw [measureReal_restrict_apply measurableSet_ball, inter_eq_left.mpr hsub]
    exact ENNReal.toReal_pos (measure_ball_pos volume b hε).ne' measure_ball_lt_top.ne
  have hav := extendedAverage_lt_of_upper_bound μ hμ u m c
    (EReal.coe_lt_coe_iff.mp hcm) (ball b ε) measurableSet_ball hT
    (by filter_upwards [ae_restrict_mem measurableSet_ball] with x hx; exact hm x hx)
    (by filter_upwards [] with x hx; exact (hεprop hx).2.le)
  exact (not_lt_of_ge (ha ▸ hmean a r hr hball)) hav

/-- The maximum set and its complement are relatively open in the component. -/
theorem strong_maximum : P201Specs.SubharmonicMaximum.StrongMaximumStatement := by
  intro n _ Ω u hu _ hmean a ha m ham hm
  let S := connectedComponentIn (Ω : Set _) a
  have hS : IsOpen S := Ω.isOpen.connectedComponentIn
  have hSΩ : S ⊆ (Ω : Set _) := connectedComponentIn_subset _ _
  let A := {x | x ∈ S ∧ u x = (m : EReal)}
  let B := {x | x ∈ S ∧ u x < (m : EReal)}
  have hA : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro b hb
    obtain ⟨r, hr, hbr⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hb.1)
    have hclosed : closedBall b (r / 2) ⊆ (Ω : Set _) :=
      (closedBall_subset_ball (by linarith)).trans (hbr.trans hSΩ)
    have hconst := ball_constant_of_max Ω u hu hmean b (r / 2) (by linarith)
      hclosed m hb.2 (fun x hx => hm x (hbr (ball_subset_ball (by linarith) hx)))
    apply Filter.mem_of_superset (ball_mem_nhds b (show 0 < r / 2 by linarith))
    intro x hx
    exact ⟨hbr (ball_subset_ball (by linarith) hx), hconst x hx⟩
  have hB : IsOpen B := by
    rw [isOpen_iff_mem_nhds]
    intro b hb
    have huc := hu b (hSΩ hb.1) (m : EReal) hb.2
    rw [nhdsWithin_eq_nhds.mpr (Ω.isOpen.mem_nhds (hSΩ hb.1))] at huc
    filter_upwards [hS.mem_nhds hb.1, huc] with x hx hux
    exact ⟨hx, hux⟩
  have hsub : S ⊆ A := by
    apply isPreconnected_connectedComponentIn.subset_left_of_subset_union hA hB
    · exact disjoint_left.mpr (fun x hxA hxB => hxB.2.ne hxA.2)
    · intro x hx
      rcases (hm x hx).lt_or_eq with h | h
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl ⟨hx, h⟩
    · exact ⟨a, mem_connectedComponentIn ha, mem_connectedComponentIn ha, ham⟩
  exact fun x hx => (hsub hx).2

/-- Boundary upper limits give an upper semicontinuous extension to the compact
closure. A maximum above the boundary bound would have a compact open maximum set. -/
theorem boundary_maximum : P201Specs.SubharmonicMaximum.BoundaryMaximumStatement := by
  classical
  intro n hn Ω u M hbounded hu htop hmean hboundary x hx
  by_contra hle
  have hMx : (M : EReal) < u x := lt_of_not_ge hle
  let v : P201Specs.Space n → EReal := fun y => if y ∈ Ω then u y else (M : EReal)
  have hv_in (y : P201Specs.Space n) (hy : y ∈ Ω) : v y = u y := ite_eq_left hy
  have hv_out (y : P201Specs.Space n) (hy : y ∉ Ω) : v y = (M : EReal) := ite_eq_right hy
  have hv : UpperSemicontinuousOn v (closure (Ω : Set _)) := by
    intro y hy c hc
    rw [eventually_nhdsWithin_iff]
    by_cases hyΩ : y ∈ Ω
    · have he := hu y hyΩ c (by rwa [hv_in y hyΩ] at hc)
      rw [eventually_nhdsWithin_iff] at he
      filter_upwards [he, Ω.isOpen.mem_nhds hyΩ] with z hz hzΩ _
      rw [hv_in z hzΩ]
      exact hz hzΩ
    · have hyfr : y ∈ frontier (Ω : Set _) := by
        rw [Ω.isOpen.frontier_eq]
        exact ⟨hy, hyΩ⟩
      have hMc : (M : EReal) < c := by rwa [hv_out y hyΩ] at hc
      have he := eventually_lt_of_limsup_lt ((hboundary y hyfr).trans_lt hMc)
      rw [eventually_nhdsWithin_iff] at he
      filter_upwards [he] with z hz _
      by_cases hzΩ : z ∈ Ω
      · rw [hv_in z hzΩ]; exact hz hzΩ
      · rw [hv_out z hzΩ]; exact hMc
  obtain ⟨b, hb, hmax⟩ := hv.exists_isMaxOn ⟨x, subset_closure hx⟩ hbounded.isCompact_closure
  have hMb : (M : EReal) < v b := hMx.trans_le (by simpa [v, hx] using hmax (subset_closure hx))
  have hbΩ : b ∈ Ω := by
    by_contra h
    rw [hv_out b h] at hMb
    exact hMb.false
  have hbtop : v b ≠ ⊤ := by simpa [v, hbΩ] using htop b hbΩ
  have hbbot : v b ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot M) hMb.le
  let m : ℝ := (v b).toReal
  have hbm : v b = (m : EReal) := (EReal.coe_toReal hbtop hbbot).symm
  have hMm : (M : EReal) < (m : EReal) := hbm ▸ hMb
  have hum : ∀ y ∈ Ω, u y ≤ (m : EReal) := by
    intro y hy
    have h := hmax (subset_closure hy)
    rw [hbm] at h
    simpa [v, hy] using h
  let K := closure (Ω : Set _) ∩ v ⁻¹' Ici (m : EReal)
  have hK : IsCompact K := hv.isCompact_inter_preimage_Ici hbounded.isCompact_closure _
  have hKΩ : K ⊆ (Ω : Set _) := by
    intro y hy
    by_contra h
    have hmM : (m : EReal) ≤ (M : EReal) := by
      have hh : (m : EReal) ≤ v y := hy.2
      rwa [hv_out y h] at hh
    exact hMm.not_ge hmM
  have hKeq : ∀ y ∈ K, u y = (m : EReal) := by
    intro y hy
    apply le_antisymm (hum y (hKΩ hy))
    have hh : (m : EReal) ≤ v y := hy.2
    rwa [hv_in y (hKΩ hy)] at hh
  have hKopen : IsOpen K := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨r, hr, hbr⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds (hKΩ hy))
    have hclosed : closedBall y (r / 2) ⊆ (Ω : Set _) :=
      (closedBall_subset_ball (by linarith)).trans hbr
    have hconst := ball_constant_of_max Ω u hu hmean y (r / 2) (by linarith)
      hclosed m (hKeq y hy) (fun z hz => hum z (hclosed (ball_subset_closedBall hz)))
    apply Filter.mem_of_superset (ball_mem_nhds y (show 0 < r / 2 by linarith))
    intro z hz
    have hzΩ := hclosed (ball_subset_closedBall hz)
    refine ⟨subset_closure hzΩ, ?_⟩
    change (m : EReal) ≤ v z
    rw [hv_in z hzΩ, hconst z hz]
  have hbK : b ∈ K := ⟨hb, hbm.ge⟩
  have hKuniv := (show IsClopen K from ⟨hK.isClosed, hKopen⟩).eq_univ ⟨b, hbK⟩
  have : NeZero n := ⟨by omega⟩
  have hbu : Bornology.IsBounded (univ : Set (P201Specs.Space n)) := by
    rw [← hKuniv]
    exact hbounded.subset hKΩ
  exact NormedSpace.unbounded_univ ℝ (P201Specs.Space n) hbu

/-- The positive and negative parts balance against any nonnegative upper bound. -/
theorem deficit_parts (C : ℝ) (hC : 0 ≤ C) (z : EReal) (hz : z ≤ (C : EReal)) :
    ((C : EReal) - z).toENNReal + z.toENNReal =
      ENNReal.ofReal C + (-z).toENNReal := by
  induction z with
  | bot => simp
  | top => exact False.elim ((EReal.coe_ne_top C) (top_le_iff.mp hz))
  | coe t =>
    have ht : t ≤ C := EReal.coe_le_coe_iff.mp hz
    simp only [← EReal.coe_sub, ← EReal.coe_neg, EReal.real_coe_toENNReal]
    by_cases h : 0 ≤ t
    · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr h), add_zero,
        ← ENNReal.ofReal_add (sub_nonneg.mpr ht) h, sub_add_cancel]
    · have ht0 : t ≤ 0 := le_of_not_ge h
      rw [ENNReal.ofReal_of_nonpos ht0, add_zero,
        ← ENNReal.ofReal_add hC (neg_nonneg.mpr ht0)]
      rfl

/-- Signed integration of an upper bounded extended function equals the upper
bound times the mass minus the nonnegative integral of its deficit. -/
theorem extendedIntegral_deficit {n : ℕ} (μ : Measure (P201Specs.Space n))
    [IsFiniteMeasure μ] (u : P201Specs.Space n → EReal) (hu : AEMeasurable u μ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂μ, u x ≤ (C : EReal)) :
    extendedIntegral μ u = ((C * μ.real univ : ℝ) : EReal) -
      ((∫⁻ x, ((C : EReal) - u x).toENNReal ∂μ) : EReal) := by
  let P := ∫⁻ x, (u x).toENNReal ∂μ
  let N := ∫⁻ x, (-u x).toENNReal ∂μ
  let D := ∫⁻ x, ((C : EReal) - u x).toENNReal ∂μ
  let A := ENNReal.ofReal C * μ univ
  have hP : P ≠ ⊤ := (positivePart_finite_of_ae_upper_bound μ u C hbound).ne
  have hA : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have he : D + P = A + N := by
    dsimp only [D, P, A, N]
    rw [← lintegral_add_right' _ hu.ereal_toENNReal,
      ← lintegral_const (μ := μ) (ENNReal.ofReal C),
      ← lintegral_add_left measurable_const]
    apply lintegral_congr_ae
    exact hbound.mono fun x hx => deficit_parts C hC (u x) hx
  change (P : EReal) - (N : EReal) = _ - (D : EReal)
  have hAr : A.toReal = C * μ.real univ := by simp [A, hC, Measure.real]
  by_cases hN : N = ⊤
  · have hD : D = ⊤ := by
      have : D + P = ⊤ := by simpa [hN] using he
      exact (ENNReal.add_eq_top.mp this).resolve_right hP
    simp [hN, hD]
  · have hD : D ≠ ⊤ := by
      intro hD
      have : A + N = ⊤ := by simpa [hD] using he.symm
      exact (ENNReal.add_ne_top.mpr ⟨hA, hN⟩) this
    have her := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_add hD hP, ENNReal.toReal_add hA hN, hAr] at her
    rw [← EReal.coe_ennreal_toReal hP, ← EReal.coe_ennreal_toReal hN,
      ← EReal.coe_ennreal_toReal hD, ← EReal.coe_sub, ← EReal.coe_sub]
    congr 1
    linarith

/-- A finite lower bound on an average is equivalently an upper bound on its
nonnegative deficit. -/
theorem le_extendedAverage_iff_deficit {n : ℕ} (μ : Measure (P201Specs.Space n))
    [IsFiniteMeasure μ] (hμ : 0 < μ.real univ)
    (u : P201Specs.Space n → EReal) (hu : AEMeasurable u μ)
    (C m : ℝ) (hC : 0 ≤ C) (hm : m ≤ C)
    (hbound : ∀ᵐ x ∂μ, u x ≤ (C : EReal)) :
    (m : EReal) ≤ extendedAverage μ u ↔
      (∫⁻ x, ((C : EReal) - u x).toENNReal ∂μ) ≤ ENNReal.ofReal ((C - m) * μ.real univ) := by
  change (m : EReal) ≤ (μ.real univ)⁻¹ * extendedIntegral μ u ↔ _
  rw [extendedIntegral_deficit μ u hu C hC hbound]
  let D := ∫⁻ x, ((C : EReal) - u x).toENNReal ∂μ
  change (m : EReal) ≤ (μ.real univ)⁻¹ * ((C * μ.real univ : ℝ) - (D : EReal)) ↔ D ≤ ENNReal.ofReal ((C - m) * μ.real univ)
  by_cases hD : D = ⊤
  · simp [hD, EReal.mul_bot_of_pos (EReal.coe_pos.mpr (inv_pos.mpr hμ))]
  · rw [← EReal.coe_ennreal_toReal hD, ← EReal.coe_sub, ← EReal.coe_mul,
      EReal.coe_le_coe_iff, ← ENNReal.ofReal_toReal hD,
      ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sub_nonneg.mpr hm) hμ.le),
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    constructor <;> intro h
    · have := (le_inv_mul_iff₀ hμ).mp h
      linarith
    · apply (le_inv_mul_iff₀ hμ).mpr
      linarith

/-- Tonelli polar integration, for nonnegative measurable functions. -/
theorem lintegral_polar {n : ℕ} (hn : 1 ≤ n)
    (f : P201Specs.Space n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x) = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (n - 1)) *
      ∫⁻ θ, f (s • θ) ∂P201Specs.unitSurface n := by
  let : NeZero n := ⟨by omega⟩
  have hp : (∫⁻ x, f x) = ∫⁻ p : sphere (0 : P201Specs.Space n) 1 × Ioi (0 : ℝ),
      f (p.2.1 • p.1.1)
      ∂(volume : Measure (P201Specs.Space n)).toSphere.prod (Measure.volumeIoiPow (n - 1)) := by
    calc
      (∫⁻ x, f x) = ∫⁻ x : ({0}ᶜ : Set (P201Specs.Space n)), f x.1
          ∂volume.comap Subtype.val := by
        rw [lintegral_subtype_comap (measurableSet_singleton _).compl,
          restrict_compl_singleton]
      _ = _ := by
        have h := (volume : Measure (P201Specs.Space n)).measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
          (Homeomorph.measurableEmbedding _)
          (fun p => f (((homeomorphUnitSphereProd (P201Specs.Space n)).symm p).1))
        simpa only [Function.comp_def, Homeomorph.symm_apply_apply,
          homeomorphUnitSphereProd_symm_apply_coe, finrank_euclideanSpace_fin] using h
  rw [hp, lintegral_prod_symm'
    (fun p : sphere (0 : P201Specs.Space n) 1 × Ioi (0 : ℝ) => f (p.2.1 • p.1.1))
    (hf.comp (by fun_prop))]
  have he := (isClosed_sphere (x := (0 : P201Specs.Space n)) (ε := 1)).isClosedEmbedding_subtypeVal.measurableEmbedding
  simp_rw [P201.MeanValues.unitSurface_eq_map_toSphere, he.lintegral_map]
  rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (((measurable_subtype_coe : Measurable (Subtype.val : Ioi (0 : ℝ) → ℝ)).pow_const (n - 1)).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  exact lintegral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Ioi
    (fun s : ℝ => ENNReal.ofReal (s ^ (n - 1)) *
      ∫⁻ θ : sphere (0 : P201Specs.Space n) 1, f (s • θ.1)
        ∂(volume : Measure (P201Specs.Space n)).toSphere)

/-- The radial weight is incorporated in the actual sphere surface measure. -/
theorem lintegral_ball_polar {n : ℕ} (hn : 1 ≤ n)
    (f : P201Specs.Space n → ℝ≥0∞) (hf : Measurable f) (a : P201Specs.Space n) (r : ℝ) :
    (∫⁻ x in ball a r, f x) =
      ∫⁻ s in Ioo (0 : ℝ) r, ∫⁻ x, f x ∂P201Specs.sphereSurface a s := by
  rw [← lintegral_indicator measurableSet_ball,
    ← lintegral_add_left_eq_self ((ball a r).indicator f) a,
    lintegral_polar hn (fun x => (ball a r).indicator f (a + x))
      ((hf.indicator measurableSet_ball).comp (by fun_prop))]
  have hsphere (s : ℝ) : (∫⁻ x, f x ∂P201Specs.sphereSurface a s) =
      ENNReal.ofReal (s ^ (n - 1)) * ∫⁻ θ, f (a + s • θ) ∂P201Specs.unitSurface n := by
    rw [P201Specs.sphereSurface, lintegral_smul_measure, lintegral_map hf (by fun_prop)]
    rfl
  have hh (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      ENNReal.ofReal (s ^ (n - 1)) *
        (∫⁻ θ, (ball a r).indicator f (a + s • θ) ∂P201Specs.unitSurface n) =
      (Iio r).indicator (fun s => ∫⁻ x, f x ∂P201Specs.sphereSurface a s) s := by
    have he : (∫⁻ θ, (ball a r).indicator f (a + s • θ) ∂P201Specs.unitSurface n) =
        if s < r then ∫⁻ θ, f (a + s • θ) ∂P201Specs.unitSurface n else 0 := by
      split_ifs with h
      · apply lintegral_congr_ae
        filter_upwards [P201.MeanValues.unitSurface_ae_mem n] with θ hθ
        have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
        apply indicator_of_mem
        simpa [mem_ball, dist_eq_norm, norm_smul, hθn, abs_of_pos hs.out] using h
      · rw [← lintegral_zero (μ := P201Specs.unitSurface n)]
        apply lintegral_congr_ae
        filter_upwards [P201.MeanValues.unitSurface_ae_mem n] with θ hθ
        have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
        apply indicator_of_notMem
        simpa [mem_ball, dist_eq_norm, norm_smul, hθn, abs_of_pos hs.out] using h
    rw [he]
    by_cases h : s < r <;> simp [h, Set.indicator, hsphere]
  rw [setLIntegral_congr_fun measurableSet_Ioi hh, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  have he : Iio r ∩ Ioi (0 : ℝ) = Ioo 0 r := by
    ext s
    exact and_comm
  rw [he]


theorem extendedAverage_congr_ae {n : ℕ} (μ : Measure (P201Specs.Space n))
    (u v : P201Specs.Space n → EReal) (h : u =ᵐ[μ] v) :
    extendedAverage μ u = extendedAverage μ v :=
  le_antisymm (extendedAverage_mono μ u v (h.mono fun _ hx => hx.le))
    (extendedAverage_mono μ v u (h.symm.mono fun _ hx => hx.le))

theorem sphere_implies_ball : P201Specs.SubharmonicMaximum.SphereImpliesBallStatement := by
  classical
  intro n hn Ω u hu htop hs a r hr hball
  have haΩ : a ∈ Ω := hball (mem_closedBall_self hr.le)
  by_cases hbot : u a = ⊥
  · simp [hbot]
  let v : P201Specs.Space n → EReal := fun x => if x ∈ Ω then u x else 0
  have hv_eq (x : P201Specs.Space n) (hx : x ∈ Ω) : v x = u x := ite_eq_left hx
  have hv : Measurable v := by
    apply measurable_of_restrict_of_restrict_compl Ω.isOpen.measurableSet
    · have h := (upperSemicontinuousOn_iff_restrict.mpr hu).measurable
      have he : (Ω : Set _).domRestrict v = (Ω : Set _).domRestrict u := by
        funext x
        exact hv_eq x x.property
      rw [he]
      exact h
    · have h : ((Ω : Set _)ᶜ).domRestrict v = fun _ => (0 : EReal) := by
        funext x
        exact ite_eq_right x.property
      rw [h]
      exact measurable_const
  let m : ℝ := (u a).toReal
  have ham : u a = (m : EReal) := (EReal.coe_toReal (htop a haΩ) hbot).symm
  obtain ⟨C₀, hC₀⟩ := compact_upper_bound Ω u hu htop (closedBall a r)
    (isCompact_closedBall a r) hball
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (x : P201Specs.Space n) (hx : x ∈ closedBall a r) : v x ≤ (C : EReal) := by
    rw [hv_eq x (hball hx)]
    exact (hC₀ x hx).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  have hmC : m ≤ C := by
    apply EReal.coe_le_coe_iff.mp
    rw [← ham, ← hv_eq a haΩ]
    exact hbound a (mem_closedBall_self hr.le)
  let μ : Measure (P201Specs.Space n) := volume.restrict (ball a r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hμ : 0 < μ.real univ := by
    rw [measureReal_restrict_apply_univ]
    exact ENNReal.toReal_pos (measure_ball_pos volume a hr).ne' measure_ball_lt_top.ne
  have hμbound : ∀ᵐ x ∂μ, v x ≤ (C : EReal) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hbound x (ball_subset_closedBall hx)
  have hμeq : u =ᵐ[μ] v := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hv_eq x (hball (ball_subset_closedBall hx))).symm
  change u a ≤ extendedAverage μ u
  rw [extendedAverage_congr_ae μ u v hμeq, ham]
  apply (le_extendedAverage_iff_deficit μ hμ v hv.aemeasurable C m hC hmC hμbound).mpr
  let f : P201Specs.Space n → ℝ≥0∞ := fun x => ((C : EReal) - v x).toENNReal
  have hf : Measurable f := (measurable_const.sub hv).ereal_toENNReal
  have hrad (s : ℝ) (hsr : s ∈ Ioo (0 : ℝ) r) :
      (∫⁻ x, f x ∂P201Specs.sphereSurface a s) ≤
        ∫⁻ _ : P201Specs.Space n, ENNReal.ofReal (C - m) ∂P201Specs.sphereSurface a s := by
    have hsmall : closedBall a s ⊆ (Ω : Set _) :=
      (closedBall_subset_closedBall hsr.2.le).trans hball
    have hseq : u =ᵐ[P201Specs.sphereSurface a s] v := by
      filter_upwards [sphereSurface_ae_mem a s hsr.1.le] with x hx
      exact (hv_eq x (hsmall (sphere_subset_closedBall hx))).symm
    have hsbound : ∀ᵐ x ∂P201Specs.sphereSurface a s, v x ≤ (C : EReal) := by
      filter_upwards [sphereSurface_ae_mem a s hsr.1.le] with x hx
      exact hbound x ((closedBall_subset_closedBall hsr.2.le) (sphere_subset_closedBall hx))
    have hsmass : 0 < (P201Specs.sphereSurface a s).real univ := by
      rw [P201.sphereSurfaceMass a s hsr.1.le]
      exact mul_pos (P201.MeanValues.omega_pos (by omega)) (pow_pos hsr.1 _)
    have hsmean := hs a s hsr.1 hsmall
    change u a ≤ extendedAverage (P201Specs.sphereSurface a s) u at hsmean
    rw [ham, extendedAverage_congr_ae _ u v hseq] at hsmean
    have hdef := (le_extendedAverage_iff_deficit (P201Specs.sphereSurface a s) hsmass
      v hv.aemeasurable C m hC hmC hsbound).mp hsmean
    dsimp only [f]
    convert hdef using 1
    rw [lintegral_const, ENNReal.ofReal_mul (sub_nonneg.mpr hmC), Measure.real,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change (∫⁻ x in ball a r, f x) ≤ _
  rw [lintegral_ball_polar (by omega) f hf a r]
  calc
    (∫⁻ s in Ioo (0 : ℝ) r, ∫⁻ x, f x ∂P201Specs.sphereSurface a s) ≤
      ∫⁻ s in Ioo (0 : ℝ) r, ∫⁻ _ : P201Specs.Space n,
        ENNReal.ofReal (C - m) ∂P201Specs.sphereSurface a s := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hsr
          exact hrad s hsr
    _ = ∫⁻ _ : P201Specs.Space n in ball a r, ENNReal.ofReal (C - m) :=
      (lintegral_ball_polar (by omega) (fun _ => ENNReal.ofReal (C - m)) measurable_const a r).symm
    _ = ENNReal.ofReal ((C - m) * μ.real univ) := by
      rw [lintegral_const, ENNReal.ofReal_mul (sub_nonneg.mpr hmC), Measure.real,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]

end P201.SubharmonicMaximum
