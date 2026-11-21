import MathGenome.Internal.FourierSobolev.P102.Periodic.Localization
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Dini
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter Set
open scoped Topology Real ComplexConjugate

namespace P102.Periodic
open Expected.Dini (offset residual)

/-- Normalized Haar measure has no point masses. -/
instance haar_nullSingletonClass (T : ℝ) [hT : Fact (0 < T)] :
    NullSingletonClass (haar T) := by
  constructor
  intro x
  have hz : ENNReal.ofReal T * (haar T) {x} = 0 := by
    change (ENNReal.ofReal T • haar T) {x} = 0
    rw [← AddCircle.volume_eq_smul_haarAddCircle, ← Metric.closedBall_zero,
      AddCircle.volume_closedBall]
    simp [hT.out.le]
  exact (mul_eq_zero.mp hz).resolve_left (by simpa using hT.out)

/-- Pullback to a fundamental interval, with its unnormalized Lebesgue measure. -/
theorem integrableOn_circle_interval (T : ℝ) [hT : Fact (0 < T)]
    (h : Circle T → ℂ) (hh : Integrable h (haar T)) (a : ℝ) :
    IntegrableOn (fun v : ℝ => h (v : Circle T)) (Icc a (a + T)) := by
  have hs := (interval_measure T a).integrable_comp_of_integrable hh
  have hioc : IntegrableOn (fun v : ℝ => h (v : Circle T)) (Ioc a (a + T)) :=
    (integrable_smul_measure (by simp [hT.out]) ENNReal.ofReal_ne_top).mp hs
  exact (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).mpr hioc

/-- The symmetric kernel is even, including at zero. -/
theorem dirichletKernel_neg (T : ℝ) (N : ℕ) (y : Circle T) :
    dirichletKernel T N (-y) = dirichletKernel T N y := by
  unfold dirichletKernel
  apply Finset.sum_bij (fun k _ => -k)
  · intro k hk
    simp only [frequencies, Finset.mem_Icc] at hk ⊢
    constructor <;> omega
  · intro a ha b hb hab
    exact neg_injective hab
  · intro k hk
    refine ⟨-k, ?_, neg_neg k⟩
    simp only [frequencies, Finset.mem_Icc] at hk ⊢
    constructor <;> omega
  · intro k hk
    simp [mode, fourier_apply, neg_smul, smul_neg]

/-- The zeroth coefficient of the Dirichlet kernel is one. -/
theorem integral_dirichletKernel (T : ℝ) [Fact (0 < T)] (N : ℕ) :
    (∫ y, dirichletKernel T N y ∂haar T) = 1 := by
  have hm (k : ℤ) : (∫ y, mode T k y ∂haar T) = if k = 0 then 1 else 0 := by
    have h := congrFun (fourierCoeff_fourier (T := T) 0) (-k)
    rw [← coefficient_eq_fourierCoeff] at h
    simpa [coefficient, mode, Pi.single_apply, eq_comm] using h
  simp_rw [dirichletKernel]
  rw [integral_finsetSum]
  · simp only [hm]
    rw [Finset.sum_ite_eq']
    simp [frequencies]
  · intro k hk
    exact (mode T k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Size of the first-character difference in angular coordinates. -/
theorem angular_mode_sub_one_norm (v : ℝ) (hv : 0 < v) (hπ : v ≤ Real.pi) :
    ‖mode (2 * Real.pi) 1 (v : Circle (2 * Real.pi)) - 1‖ =
      2 * Real.sin (v / 2) := by
  rw [angular_mode]
  simp only [Int.cast_one, mul_one]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_of_pos]
  exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

/-- Only the upper comparison with the Dini weight is needed. -/
theorem angular_quotient_norm_le (z : ℂ) (v : ℝ) (hv : 0 < v) (hπ : v ≤ Real.pi) :
    ‖z / (mode (2 * Real.pi) 1 (v : Circle (2 * Real.pi)) - 1)‖ ≤
      Real.pi * (‖z‖ / v) := by
  have hs : 0 < Real.sin (v / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hb := Real.mul_le_sin (x := v / 2) (by positivity) (by linarith)
  have hb' : v ≤ Real.pi * (2 * Real.sin (v / 2)) := by
    have hh : v / Real.pi ≤ Real.sin (v / 2) := by convert hb using 1 <;> ring
    have hh' := (div_le_iff₀ Real.pi_pos).mp hh
    nlinarith [mul_nonneg Real.pi_pos.le hs.le]
  rw [norm_div, angular_mode_sub_one_norm v hv hπ, ← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hs) hv).mpr
  nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hb')]

/-- For an even circle function, the Dini weight on just the positive side
makes division by the first-character difference integrable on the circle. -/
theorem integrable_angular_quotient_of_dini
    (h : Circle (2 * Real.pi) → ℂ) (hh : Integrable h (haar (2 * Real.pi)))
    (he : ∀ y, h (-y) = h y) (δ : ℝ) (hδ : 0 < δ)
    (hd : IntegrableOn (fun v : ℝ => ‖h (v : Circle (2 * Real.pi))‖ / v) (Ioo 0 δ)) :
    Integrable (fun y => h y / (mode (2 * Real.pi) 1 y - 1)) (haar (2 * Real.pi)) := by
  let P := 2 * Real.pi
  let q : Circle P → ℂ := fun y => h y / (mode P 1 y - 1)
  have hfull : IntegrableOn (fun v : ℝ => h (v : Circle P)) (Icc (-Real.pi) Real.pi) := by
    convert integrableOn_circle_interval P h hh (-Real.pi) using 1 <;> dsimp [P] <;> congr 1 <;> ring
  have hhalf : IntegrableOn (fun v : ℝ => h (v : Circle P)) (Icc 0 Real.pi) :=
    hfull.mono_set (Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl)
  let η := min δ Real.pi
  have hη : 0 < η := lt_min hδ Real.pi_pos
  have hηπ : η ≤ Real.pi := min_le_right _ _
  have hsmall : IntegrableOn (fun v : ℝ => q (v : Circle P)) (Ioo 0 η) := by
    have hd' := (hd.mono_set (Ioo_subset_Ioo le_rfl (min_le_left δ Real.pi))).const_mul Real.pi
    apply hd'.mono'
    · exact (hhalf.aestronglyMeasurable.mono_set
        (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl hηπ))).div₀
        (((mode P 1).continuous.comp continuous_quotient_mk').sub continuous_const).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      exact angular_quotient_norm_le _ v hv.1 (hv.2.le.trans hηπ)
  have hlarge : IntegrableOn (fun v : ℝ => q (v : Circle P)) (Icc η Real.pi) := by
    have hi := hhalf.mono_set (Icc_subset_Icc hη.le le_rfl)
    have hc : ContinuousOn (fun v : ℝ =>
        (mode P 1 (v : Circle P) - 1)⁻¹) (Icc η Real.pi) := by
      apply ContinuousOn.inv₀
      · exact (((mode P 1).continuous.comp continuous_quotient_mk').sub continuous_const).continuousOn
      · intro v hv
        apply norm_ne_zero_iff.mp
        rw [angular_mode_sub_one_norm v (hη.trans_le hv.1) hv.2]
        exact (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi
          (by linarith [hv.1]) (by linarith [hv.2, Real.pi_pos]))).ne'
    simpa only [q, div_eq_mul_inv] using hi.mul_continuousOn hc isCompact_Icc
  have hp : IntegrableOn (fun v : ℝ => q (v : Circle P)) (Icc 0 Real.pi) := by
    apply (integrableOn_Icc_iff_integrableOn_Ioo (by finiteness) (by finiteness)).mpr
    apply (hsmall.union hlarge).mono_set
    intro v hv
    by_cases hvη : v < η
    · exact Or.inl ⟨hv.1, hvη⟩
    · exact Or.inr ⟨le_of_not_gt hvη, hv.2.le⟩
  have hnormeven (v : ℝ) : ‖q ((-v : ℝ) : Circle P)‖ = ‖q (v : Circle P)‖ := by
    have hc (y : Circle P) : mode P 1 (-y) - 1 = conj (mode P 1 y - 1) := by
      have hm : mode P 1 (-y) = conj (mode P 1 y) := by
        simpa only [zero_sub, mode, fourier_eval_zero, one_mul] using mode_sub P 1 0 y
      rw [hm, map_sub, map_one]
    simp only [q, AddCircle.coe_neg, norm_div, he, hc, Complex.norm_conj]
  have hn : IntegrableOn (fun v : ℝ => ‖q (v : Circle P)‖) (Icc (-Real.pi) 0) := by
    have hp' : IntervalIntegrable (fun v : ℝ => ‖q (v : Circle P)‖) volume 0 Real.pi :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mpr hp.norm
    have hn' := (IntervalIntegrable.iff_comp_neg).mp hp'
    simp only [neg_zero, hnormeven] at hn'
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).mp hn'.symm
  have hnfull : IntegrableOn (fun v : ℝ => ‖q (v : Circle P)‖) (Icc (-Real.pi) Real.pi) := by
    apply (hn.union hp.norm).mono_set
    intro v hv
    by_cases hv0 : v ≤ 0
    · exact Or.inl ⟨hv.1, hv0⟩
    · exact Or.inr ⟨(le_of_not_ge hv0), hv.2⟩
  have hqm : AEStronglyMeasurable q (haar P) := hh.aestronglyMeasurable.div₀
    ((mode P 1).continuous.sub continuous_const).aestronglyMeasurable
  have hqfull : IntegrableOn (fun v : ℝ => q (v : Circle P)) (Icc (-Real.pi) Real.pi) := by
    apply (integrable_norm_iff ?_).mp hnfull
    exact hfull.aestronglyMeasurable.div₀
      (((mode P 1).continuous.comp continuous_quotient_mk').sub continuous_const).aestronglyMeasurable
  apply ((interval_measure P (-Real.pi)).integrable_comp hqm).mp
  apply (integrable_smul_measure (by simp [P, Real.pi_pos]) ENNReal.ofReal_ne_top).mpr
  have hioc := hqfull.mono_set Ioc_subset_Icc_self
  change IntegrableOn (fun v : ℝ => q (v : Circle P)) (Ioc (-Real.pi) (-Real.pi + P))
  convert hioc using 1
  dsimp [P]
  congr 1
  ring

/-- The geometric-series identity turns an integrable quotient into two
Fourier coefficients escaping to infinity. -/
theorem integral_mul_dirichlet_tendsto_zero (T : ℝ) [Fact (0 < T)]
    (h : Circle T → ℂ)
    (hq : Integrable (fun y => h y / (mode T 1 y - 1)) (haar T)) :
    Tendsto (fun N : ℕ => ∫ y, h y * dirichletKernel T N y ∂haar T)
      atTop (𝓝 0) := by
  let q : Circle T → ℂ := fun y => h y / (mode T 1 y - 1)
  have heq (N : ℕ) : (∫ y, h y * dirichletKernel T N y ∂haar T) =
      coefficient T q (-(↑N + 1)) - coefficient T q (N : ℤ) := by
    calc
      _ = ∫ y, q y * (mode T (↑N + 1) y - mode T (-↑N) y) ∂haar T := by
        apply integral_congr_ae
        have hz : ∀ᵐ y ∂haar T, y ≠ 0 := by simp [ae_iff]
        filter_upwards [hz] with y hy
        have hd : mode T 1 y - 1 ≠ 0 := by
          intro hd
          exact hy ((mode_one_eq_one_iff T y).mp (sub_eq_zero.mp hd))
        calc
          _ = (q y * (mode T 1 y - 1)) * dirichletKernel T N y := by
            rw [show q y * (mode T 1 y - 1) = h y from div_mul_cancel₀ _ hd]
          _ = _ := by
            rw [mul_assoc, mul_comm (mode T 1 y - 1), dirichletKernel_mul_mode_sub_one]
      _ = _ := by
        simp_rw [mul_sub]
        rw [integral_sub (integrable_mul_mode T q hq _) (integrable_mul_mode T q hq _),
          integral_mul_mode_eq_coefficient, integral_mul_mode_eq_coefficient, neg_neg]
  have hp : Tendsto (fun N : ℕ => -((N : ℤ) + 1)) atTop cofinite := by
    rw [← Nat.cofinite_eq_atTop]
    exact (show Function.Injective (fun N : ℕ => -((N : ℤ) + 1)) from by
      intro a b hab
      simpa only [neg_inj, add_left_inj, Nat.cast_inj] using hab).tendsto_cofinite
  have hn : Tendsto (fun N : ℕ => (N : ℤ)) atTop cofinite := by
    rw [← Nat.cofinite_eq_atTop]
    exact (Nat.cast_injective : Function.Injective (fun N : ℕ => (N : ℤ))).tendsto_cofinite
  have H := ((coefficient_decay T q hq).comp hp).sub ((coefficient_decay T q hq).comp hn)
  simpa only [sub_self] using H.congr' (Eventually.of_forall fun N => (heq N).symm)

/-- A sufficient condition expressed intrinsically on the circle. Pairing the
two sides allows cancellation; neither side need satisfy a separate Dini test. -/
theorem partialSum_tendsto_of_integrable_symmetric_quotient (T : ℝ) [Fact (0 < T)]
    (f : Circle T → ℂ) (hf : Integrable f (haar T)) (x : Circle T) (L : ℂ)
    (hq : Integrable (fun y =>
      (f (x + y) + f (x - y) - 2 * L) / (mode T 1 y - 1)) (haar T)) :
    Tendsto (fun N : ℕ => partialSum T N f x) atTop (𝓝 L) := by
  have heq (N : ℕ) : (∫ y, (f (x + y) + f (x - y) - 2 * L) *
      dirichletKernel T N y ∂haar T) = 2 * (partialSum T N f x - L) := by
    have hi := dirichlet_convolution_exists T f hf N x
    have hp : Integrable (fun y => f (x + y) * dirichletKernel T N y) (haar T) := by
      convert hi.comp_neg using 1
      ext y
      simp [sub_neg_eq_add, dirichletKernel_neg]
    have hk : Integrable (dirichletKernel T N) (haar T) :=
      (continuous_dirichletKernel T N).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hrefl : (∫ y, f (x + y) * dirichletKernel T N y ∂haar T) =
        ∫ y, f (x - y) * dirichletKernel T N y ∂haar T := by
      simpa only [sub_neg_eq_add, dirichletKernel_neg] using
        integral_neg_eq_self (fun y => f (x - y) * dirichletKernel T N y) (haar T)
    have hs : Integrable (fun y => f (x + y) * dirichletKernel T N y +
        f (x - y) * dirichletKernel T N y) (haar T) := hp.add hi
    simp_rw [sub_mul, add_mul]
    rw [integral_sub hs (hk.const_mul (2 * L)), integral_add hp hi,
      integral_const_mul, integral_dirichletKernel, mul_one, hrefl,
      ← show partialSum T N f x = ∫ y, f (x - y) * dirichletKernel T N y ∂haar T from
        partialSum_eq_convolution T f hf N x]
    ring
  have H := integral_mul_dirichlet_tendsto_zero T
    (fun y => f (x + y) + f (x - y) - 2 * L) hq
  have Hz : Tendsto (fun N : ℕ => partialSum T N f x - L) atTop (𝓝 0) := by
    have H' := H.const_mul (1 / 2 : ℂ)
    simp only [mul_zero] at H'
    convert H' using 1
    ext N
    rw [heq]
    ring
  simpa only [sub_add_cancel, zero_add] using Hz.add_const L

@[simp] theorem offset_angular (v : ℝ) :
    offset (2 * Real.pi) v = (v : Circle (2 * Real.pi)) := by
  unfold offset
  congr 1
  field_simp

/-- Dini's symmetric criterion in angular coordinates. -/
theorem dini_symmetric_angular (f : Circle (2 * Real.pi) → ℂ)
    (hf : Integrable f (haar (2 * Real.pi))) (x : Circle (2 * Real.pi)) (L : ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hd : IntegrableOn (fun v => ‖residual (2 * Real.pi) f x L v‖ / v) (Ioo 0 δ)) :
    Tendsto (fun N : ℕ => partialSum (2 * Real.pi) N f x) atTop (𝓝 L) := by
  apply partialSum_tendsto_of_integrable_symmetric_quotient _ f hf x L
  apply integrable_angular_quotient_of_dini
    (fun y => f (x + y) + f (x - y) - 2 * L)
    (((hf.comp_add_left x).add (hf.comp_sub_left x)).sub (integrable_const _))
    (fun y => by simp only [sub_eq_add_neg, neg_neg]; ring) δ hδ
  simpa only [Expected.Dini.residual, offset_angular] using hd

/-- Dini's criterion for every positive period and every integrable
representative. The symmetric residual may cancel even if neither one-sided
limit exists. -/
theorem dini_symmetric (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ)
    (hf : Integrable f (haar T)) (x : Circle T) (L : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hd : IntegrableOn (fun v => ‖residual T f x L v‖ / v) (Ioo 0 δ)) :
    Tendsto (fun N : ℕ => partialSum T N f x) atTop (𝓝 L) := by
  let R := rescale (2 * Real.pi) T
  let F : Circle (2 * Real.pi) → ℂ := fun y => f (R y)
  let X := R.symm x
  have hF : Integrable F (haar (2 * Real.pi)) :=
    (rescale_measure (2 * Real.pi) T).integrable_comp_of_integrable hf
  have hres (v : ℝ) : residual (2 * Real.pi) F X L v = residual T f x L v := by
    simp only [Expected.Dini.residual, offset_angular, F, map_add, map_sub, X, AddEquiv.apply_symm_apply]
    rw [show R (v : Circle (2 * Real.pi)) = offset T v from
      rescale_formula (2 * Real.pi) T v]
  have hdF : IntegrableOn (fun v => ‖residual (2 * Real.pi) F X L v‖ / v) (Ioo 0 δ) := by
    simpa only [hres] using hd
  have H := dini_symmetric_angular F hF X L δ hδ hdF
  simpa only [F, R, rescale_partialSum, X, AddEquiv.apply_symm_apply] using H

/-- Pull back an integrable circle function along angular displacement. -/
theorem integrableOn_offset_interval (T : ℝ) [Fact (0 < T)]
    (h : Circle T → ℂ) (hh : Integrable h (haar T)) (a : ℝ) :
    IntegrableOn (fun v => h (offset T v)) (Icc a (a + 2 * Real.pi)) := by
  have hF : Integrable (fun y => h (rescale (2 * Real.pi) T y))
      (haar (2 * Real.pi)) :=
    (rescale_measure (2 * Real.pi) T).integrable_comp_of_integrable hh
  simpa only [rescale_formula, Expected.Dini.offset] using
    integrableOn_circle_interval (2 * Real.pi) _ hF a

/-- Separate one-sided Dini conditions imply the symmetric condition on a
common interval, hence convergence to the average of the two constants. -/
theorem dini_separate (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ)
    (hf : Integrable f (haar T)) (x : Circle T) (aPlus aMinus : ℂ)
    (δPlus δMinus : ℝ) (hδPlus : 0 < δPlus) (hδMinus : 0 < δMinus)
    (hp : IntegrableOn (fun v => ‖f (x + offset T v) - aPlus‖ / v) (Ioo 0 δPlus))
    (hm : IntegrableOn (fun v => ‖f (x - offset T v) - aMinus‖ / v) (Ioo 0 δMinus)) :
    Tendsto (fun N : ℕ => partialSum T N f x) atTop (𝓝 ((aPlus + aMinus) / 2)) := by
  let η := min (min δPlus δMinus) (2 * Real.pi)
  have hη : 0 < η := lt_min (lt_min hδPlus hδMinus) (by positivity)
  have hηp : η ≤ δPlus := (min_le_left _ _).trans (min_le_left _ _)
  have hηm : η ≤ δMinus := (min_le_left _ _).trans (min_le_right _ _)
  have hηπ : η ≤ 2 * Real.pi := min_le_right _ _
  apply dini_symmetric T f hf x ((aPlus + aMinus) / 2) η hη
  have hp' := hp.mono_set (Ioo_subset_Ioo le_rfl hηp)
  have hm' := hm.mono_set (Ioo_subset_Ioo le_rfl hηm)
  have hr : IntegrableOn (fun v => residual T f x ((aPlus + aMinus) / 2) v)
      (Icc 0 (2 * Real.pi)) := by
    have hi := integrableOn_offset_interval T
      (fun y => f (x + y) + f (x - y) - 2 * ((aPlus + aMinus) / 2))
      (((hf.comp_add_left x).add (hf.comp_sub_left x)).sub (integrable_const _)) 0
    simpa only [zero_add, Expected.Dini.residual] using hi
  apply (hp'.add hm').mono'
  · exact ((hr.aestronglyMeasurable.mono_set
      (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl hηπ))).norm).div₀
      measurable_id.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hv.1.le),
      ← add_div]
    apply (div_le_div_iff_of_pos_right hv.1).mpr
    have heq : residual T f x ((aPlus + aMinus) / 2) v =
        (f (x + offset T v) - aPlus) + (f (x - offset T v) - aMinus) := by
      unfold Expected.Dini.residual
      ring
    rw [heq]
    exact norm_add_le _ _

/-- The canonical L¹ class interface, using its chosen representative only in
the local integral hypothesis. -/
theorem dini_symmetricL1 (T : ℝ) [Fact (0 < T)] (f : L1 T) (x : Circle T)
    (L : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hd : IntegrableOn (fun v => ‖residual T f x L v‖ / v) (Ioo 0 δ)) :
    Tendsto (fun N : ℕ => partialSum T N f x) atTop (𝓝 L) :=
  dini_symmetric T f (MeasureTheory.L1.integrable_coeFn f) x L δ hδ hd

/-- A finite Dini integral forces any existing right limit of its numerator
at the singular endpoint to be zero. -/
theorem dini_integrable_limit_zero {h : ℝ → ℂ} {c : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hi : IntegrableOn (fun v => ‖h v‖ / v) (Ioo 0 δ))
    (hc : Tendsto h (𝓝[>] 0) (𝓝 c)) : c = 0 := by
  by_contra hne
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hne
  have he : ∀ᶠ v in 𝓝[>] (0 : ℝ), ‖c‖ / 2 < ‖h v‖ :=
    (hc.norm).eventually (eventually_gt_nhds (by linarith : ‖c‖ / 2 < ‖c‖))
  obtain ⟨ε, hε, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  let η := min δ ε
  have hη : 0 < η := lt_min hδ hε
  have hi' : IntegrableOn (fun v => ‖h v‖ / v) (Ioo 0 η) :=
    hi.mono_set (Ioo_subset_Ioo le_rfl (min_le_left _ _))
  have hi'' := hi'.const_mul (2 / ‖c‖)
  have hinv : IntegrableOn (fun v : ℝ => v⁻¹) (Ioo 0 η) := by
    apply hi''.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have hb' : ‖c‖ / 2 < ‖h v‖ := hb ⟨hv.1, hv.2.trans_le (min_le_right _ _)⟩
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos hv.1]
    calc
      v⁻¹ = (2 / ‖c‖) * ((‖c‖ / 2) / v) := by field_simp
      _ ≤ (2 / ‖c‖) * (‖h v‖ / v) :=
        mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hv.1).mpr hb'.le)
          (by positivity)
  have hrpow : IntegrableOn (fun v : ℝ => v ^ (-1 : ℝ)) (Ioo 0 η) := by
    simpa only [Real.rpow_neg_one] using hinv
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hη).mp hrpow
  linarith

/-- Identification of the midpoint is a consequence of the Dini hypothesis,
without any assumption about convergence of the Fourier sums. -/
theorem dini_midpoint (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ)
    (_hf : Integrable f (haar T)) (x : Circle T) (L aPlus aMinus : ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hd : IntegrableOn (fun v => ‖residual T f x L v‖ / v) (Ioo 0 δ))
    (hp : Tendsto (fun v => f (x + offset T v)) (𝓝[>] 0) (𝓝 aPlus))
    (hm : Tendsto (fun v => f (x - offset T v)) (𝓝[>] 0) (𝓝 aMinus)) :
    (aPlus + aMinus) / 2 = L := by
  have hc : Tendsto (residual T f x L) (𝓝[>] 0) (𝓝 (aPlus + aMinus - 2 * L)) :=
    (hp.add hm).sub_const (2 * L)
  have hz := dini_integrable_limit_zero hδ hd hc
  apply (div_eq_iff (two_ne_zero : (2 : ℂ) ≠ 0)).mpr
  linear_combination hz

end P102.Periodic
