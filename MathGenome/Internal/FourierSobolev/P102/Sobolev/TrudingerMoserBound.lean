import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.TrudingerMoserBound
import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.PolyaSzego
import MathGenome.Internal.FourierSobolev.P102.U4.ZeroExtension
import MathGenome.Internal.FourierSobolev.P102.U4.ChainProduct
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Order.LeftRightNhds
import MathGenome.Internal.FourierSobolev.P102.Sobolev.MoserOneDimensional
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

import MathGenome.Internal.FourierSobolev.P102.Sobolev.PolyaSzego
/-! Conditional proof of the upper bound in the sharp Trudinger–Moser inequality.
The Pólya–Szegő implementation is deliberately not imported: it is pending.
No closed original target is declared in this conditional draft. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace P102.Sobolev.TrudingerMoser
open P102.U4

lemma sphereArea_eq_ball (d : ℕ) :
    sphereArea d = (d : ℝ) * volume.real (Metric.ball (0 : Space d) 1) := by
  simp [sphereArea, Measure.toSphere_real_apply_univ, Space]

lemma sphereArea_pos {d : ℕ} (hd : 0 < d) : 0 < sphereArea d := by
  rw [sphereArea_eq_ball]
  apply mul_pos (by exact_mod_cast hd)
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : Space d) (by norm_num : (0 : ℝ) < 1)).ne'
    (measure_ball_lt_top.ne)

lemma criticalPower_pos {d : ℕ} (hd : 2 ≤ d) : 0 < criticalPower d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_pos (by linarith) (by linarith)

lemma sharpCoefficient_pos {d : ℕ} (hd : 2 ≤ d) : 0 < sharpCoefficient d := by
  exact mul_pos (by exact_mod_cast (by omega : 0 < d))
    (Real.rpow_pos_of_pos (sphereArea_pos (by omega)) _)

/-- Coordinatewise zero extension also preserves the Euclidean gradient,
which is a different norm from the sum norm on the Sobolev tuple. -/
lemma zeroExtension_gradient_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : SobolevZero 𝕜 Ω 1 p) :
    weakGradient (sobolevZeroExtensionLI Ω 1 p u) =ᵐ[volume]
      (Ω : Set (Space d)).indicator (weakGradient u.val) := by
  have hj (j : Fin d) :
      firstWeakDerivative (sobolevZeroExtensionLI Ω 1 p u) j =ᵐ[volume]
        (Ω : Set (Space d)).indicator (firstWeakDerivative u.val j) :=
    lpZeroExtension_ae Ω p _
  filter_upwards [ae_all_iff.mpr hj] with x hx
  apply PiLp.ext
  intro j
  by_cases hΩ : x ∈ Ω
  · simpa [weakGradient, hΩ] using hx j
  · simpa [weakGradient, hΩ] using hx j

lemma zeroExtension_gradient_eLpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : SobolevZero 𝕜 Ω 1 p) :
    eLpNorm (weakGradient (sobolevZeroExtensionLI Ω 1 p u)) p volume =
      eLpNorm (weakGradient u.val) p (volume.restrict (Ω : Set (Space d))) := by
  rw [eLpNorm_congr_ae (zeroExtension_gradient_ae Ω p u)]
  exact eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet.nullMeasurableSet

/-- The zero extension vanishes off the original open set, for its a.e. class. -/
lemma zeroExtension_zero_off {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : SobolevZero 𝕜 Ω 1 p) :
    ∀ᵐ x ∂volume, x ∉ Ω →
      sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x = 0 := by
  have h := lpZeroExtension_ae Ω p (sobolevUnderlying u.val)
  filter_upwards [h] with x hx hΩ
  exact hx.trans (Set.indicator_of_notMem hΩ _)

lemma zeroExtension_supported_nonnegative {d : ℕ}
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : SobolevZero ℝ Ω 1 p) {R : ℝ}
    (hΩR : (Ω : Set (Space d)) ⊆ Metric.closedBall 0 R)
    (hu : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)), 0 ≤ sobolevUnderlying u.val x) :
    Polarization.SupportedNonnegative R (sobolevZeroExtensionLI Ω 1 p u) := by
  have hrep := lpZeroExtension_ae Ω p (sobolevUnderlying u.val)
  have hu' := (ae_restrict_iff' Ω.isOpen.measurableSet).mp hu
  constructor
  · filter_upwards [hrep, hu'] with x hx hux
    change 0 ≤ lpZeroExtension Ω p (sobolevUnderlying u.val) x
    rw [hx]
    by_cases hΩ : x ∈ Ω
    · simpa [hΩ] using hux hΩ
    · simp [hΩ]
  · filter_upwards [zeroExtension_zero_off Ω p u] with x hx hxR
    exact hx (fun hxΩ => hxR (hΩR hxΩ))

/-- Application of the three frozen rearrangement interfaces to a real,
nonnegative zero extension. All pending interfaces remain explicit parameters. -/
lemma rearrange_zeroExtension_conditional
    (hExists : PolyaSzegoExpected.Existence)
    (hRadial : PolyaSzegoExpected.RadialCharacterization)
    (hUnique : PolyaSzegoExpected.Uniqueness)
    {d : ℕ} (hd : 0 < d) (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpfin : p ≠ ∞)
    {R : ℝ} (hR : 0 < R) (u : SobolevZero ℝ Ω 1 p)
    (hΩR : (Ω : Set (Space d)) ⊆ Metric.closedBall 0 R)
    (hu : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)), 0 ≤ sobolevUnderlying u.val x) :
    ∃ g : Polarization.WholeSobolev d p,
      Polarization.SupportedNonnegative R g ∧
      Rearrangement.IsRearrangement
        (sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u)) (sobolevUnderlying g) ∧
      Rearrangement.IsRadiallyNonincreasing (sobolevUnderlying g) ∧
      eLpNorm (Polarization.gradient g) p volume ≤
        eLpNorm (weakGradient u.val) p (volume.restrict (Ω : Set (Space d))) ∧
      ∀ h : Space d → ℝ, Rearrangement.IsRearrangement
        (sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u)) h →
        sobolevUnderlying g =ᵐ[volume] h := by
  have hs := zeroExtension_supported_nonnegative Ω p u hΩR hu
  obtain ⟨g, hg, hre, _, hgrad⟩ := hExists d hd p hp hpfin R hR _ hs
  refine ⟨g, hg, hre, (hRadial d hd p hp hpfin R hR g hg).mp hre.2.1, ?_, ?_⟩
  · exact hgrad.trans_eq (zeroExtension_gradient_eLpNorm Ω p u)
  · exact fun h hh => hUnique d hd _ _ _ hre hh

/-- The exact normalization used by the logarithmic change of variables. -/
def profileScale (d : ℕ) : ℝ :=
  (sphereArea d * (d : ℝ) ^ (d - 1)) ^ (1 / (d : ℝ))

lemma profileScale_pos {d : ℕ} (hd : 2 ≤ d) : 0 < profileScale d := by
  exact Real.rpow_pos_of_pos
    (mul_pos (sphereArea_pos (by omega)) (pow_pos (by positivity) _)) _

lemma profileScale_pow {d : ℕ} (hd : 2 ≤ d) :
    profileScale d ^ d = sphereArea d * (d : ℝ) ^ (d - 1) := by
  unfold profileScale
  simpa only [one_div] using Real.rpow_inv_natCast_pow
    (mul_nonneg (sphereArea_pos (by omega)).le (by positivity)) (by omega : d ≠ 0)

lemma criticalPower_eq_inverse_exponent (d : ℕ) :
    criticalPower d = 1 / Moser.exponent d :=
  (Moser.inverse_exponent (d := d)).symm

/-- The normalized power is precisely α_d, with no loss in the coefficient. -/
lemma profileScale_criticalPower {d : ℕ} (hd : 2 ≤ d) :
    profileScale d ^ criticalPower d = sharpCoefficient d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hs : 0 ≤ sphereArea d := (sphereArea_pos (by omega)).le
  unfold profileScale criticalPower sharpCoefficient
  rw [← Real.rpow_mul (mul_nonneg hs (by positivity))]
  have he : (1 / (d : ℝ)) * ((d : ℝ) / ((d : ℝ) - 1)) =
      1 / ((d : ℝ) - 1) := by field_simp
  rw [he, Real.mul_rpow hs (pow_nonneg hd0.le _)]
  have he' : ((d - 1 : ℕ) : ℝ) * (1 / ((d : ℝ) - 1)) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    exact mul_one_div_cancel hd1
  rw [← Real.rpow_natCast (d : ℝ) (d - 1), ← Real.rpow_mul hd0.le, he', Real.rpow_one]
  exact mul_comm _ _

lemma scaled_profile_power {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 ≤ a) :
    (profileScale d * a) ^ criticalPower d =
      sharpCoefficient d * a ^ criticalPower d := by
  rw [Real.mul_rpow (profileScale_pos hd).le ha, profileScale_criticalPower hd]

/-- The final normalized estimate, independent of any spatial change of
variables. Its constant is uniform in the volume factor. -/
lemma normalized_moser_bound {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ℝ≥0∞) (w : ℝ → ℝ), Moser.Admissible d w →
      V * (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp ((w t) ^ criticalPower d - t))) ≤
          ENNReal.ofReal C * V := by
  obtain ⟨C, hC, hbound⟩ := Moser.oneDimensionalEstimate d hd
  refine ⟨C, hC, fun V w hw => ?_⟩
  rw [criticalPower_eq_inverse_exponent]
  simpa only [mul_comm] using mul_le_mul_left (hbound w hw) V

/-- Equimeasurability preserves the exponential excess even on ambient
spaces of infinite measure. Only strictly positive levels are needed. -/
lemma exponential_excess_equimeasurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {f : X → ℝ} {g : Y → ℝ}
    (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[ν] g)
    (hmf : AEMeasurable f μ) (hmg : AEMeasurable g ν)
    (hlevels : ∀ s : ℝ, 0 < s → μ {x | s < f x} = ν {y | s < g y})
    {A q : ℝ} (hA : 0 ≤ A) (hq : 1 < q) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (A * f x ^ q) - 1) ∂μ) =
      ∫⁻ y, ENNReal.ofReal (Real.exp (A * g y ^ q) - 1) ∂ν := by
  let k : ℝ → ℝ := fun t => (A * q * t ^ (q - 1)) * Real.exp (A * t ^ q)
  have hk : Continuous k := by
    dsimp [k]
    apply Continuous.mul
    · exact continuous_const.mul (Real.continuous_rpow_const (by linarith : 0 ≤ q - 1))
    · exact Real.continuous_exp.comp
        (continuous_const.mul (Real.continuous_rpow_const (by linarith : 0 ≤ q)))
  have hprim (s : ℝ) : (∫ t in 0..s, k t) = Real.exp (A * s ^ q) - 1 := by
    have hder (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (A * t ^ q) - 1) (k t) t := by
      have h := (((Real.hasDerivAt_rpow_const (x := t) (p := q) (Or.inr hq.le)).const_mul A).exp).sub_const 1
      convert h using 1
      dsimp [k]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
      (hk.intervalIntegrable 0 s)]
    simp [Real.zero_rpow (by linarith : q ≠ 0)]
  have hknn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ k t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (mul_nonneg (mul_nonneg hA (by linarith))
      (Real.rpow_nonneg ht.le _)) (Real.exp_pos _).le
  simp_rw [← hprim]
  rw [lintegral_comp_eq_lintegral_meas_lt_mul μ hf hmf (fun t _ => hk.intervalIntegrable 0 t) hknn,
    lintegral_comp_eq_lintegral_meas_lt_mul ν hg hmg (fun t _ => hk.intervalIntegrable 0 t) hknn]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [hlevels s hs]

/-- Polar coordinates for nonnegative radial integrands; the extended integral
retains the possibility of infinity on both sides. -/
lemma radial_lintegral {d : ℕ} (hd : 0 < d) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x : Space d, F ‖x‖) = ENNReal.ofReal (sphereArea d) *
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) * F r := by
  let : NeZero d := ⟨by omega⟩
  let μ := (volume : Measure (Space d))
  have hpol := μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
    (Homeomorph.measurableEmbedding _) (fun z => F z.2.val)
  simp only [homeomorphUnitSphereProd_apply_snd_coe] at hpol
  calc
    _ = ∫⁻ x : ({(0 : Space d)}ᶜ : Set (Space d)), F ‖x.val‖ ∂(μ.comap (↑)) := by
      symm
      calc
        _ = ∫⁻ x in {(0 : Space d)}ᶜ, F ‖x‖ ∂μ :=
          lintegral_subtype_comap (measurableSet_singleton _).compl (fun x => F ‖x‖)
        _ = _ := by rw [restrict_compl_singleton]
    _ = ∫⁻ z, F z.2.val ∂μ.toSphere.prod (Measure.volumeIoiPow (d - 1)) := by
      simpa [Space, μ] using hpol
    _ = μ.toSphere Set.univ * ∫⁻ r : Ioi (0 : ℝ), F r ∂Measure.volumeIoiPow (d - 1) := by
      rw [lintegral_prod _ (by fun_prop)]
      simp [lintegral_const, mul_comm]
    _ = _ := by
      rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul
        (g := fun r : Ioi (0 : ℝ) => F r) _ (by fun_prop) (by fun_prop)]
      change μ.toSphere Set.univ *
        (∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (r.val ^ (d - 1)) * F r ∂volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) = _
      rw [lintegral_subtype_comap measurableSet_Ioi
        (fun r => ENNReal.ofReal (r ^ (d - 1)) * F r)]
      rw [sphereArea, ofReal_measureReal]

/-- Radius corresponding to logarithmic time t = d log(R/r). -/
def logarithmicRadius (d : ℕ) (R t : ℝ) : ℝ := R * Real.exp (-t / d)

lemma logarithmicRadius_pos {d : ℕ} {R : ℝ} (hR : 0 < R) (t : ℝ) :
    0 < logarithmicRadius d R t := mul_pos hR (Real.exp_pos _)

lemma logarithmicRadius_lt {d : ℕ} (hd : 0 < d) {R t : ℝ}
    (hR : 0 < R) (ht : 0 < t) : logarithmicRadius d R t < R := by
  unfold logarithmicRadius
  exact mul_lt_of_lt_one_right hR (Real.exp_lt_one_iff.mpr
    (div_neg_of_neg_of_pos (neg_neg_of_pos ht) (by exact_mod_cast hd)))

lemma logarithmicRadius_injective {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) :
    Function.Injective (logarithmicRadius d R) := by
  intro s t h
  have he : Real.exp (-s / d) = Real.exp (-t / d) := mul_left_cancel₀ hR.ne' h
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  exact neg_injective ((div_left_inj' hd0).mp (Real.exp_injective he))

lemma logarithmicRadius_image {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) :
    logarithmicRadius d R '' Ioi 0 = Ioo 0 R := by
  ext r
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨logarithmicRadius_pos hR t, logarithmicRadius_lt hd hR ht⟩
  · intro hr
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    refine ⟨-(d : ℝ) * Real.log (r / R), ?_, ?_⟩
    · exact mul_pos_of_neg_of_neg (neg_neg_of_pos hd0)
        (Real.log_neg (div_pos hr.1 hR) ((div_lt_one hR).mpr hr.2))
    · unfold logarithmicRadius
      have he : -(-(d : ℝ) * Real.log (r / R)) / d = Real.log (r / R) := by
        field_simp
      rw [he, Real.exp_log (div_pos hr.1 hR)]
      exact mul_div_cancel₀ r hR.ne'

lemma logarithmicRadius_hasDerivAt (d : ℕ) (R t : ℝ) :
    HasDerivAt (logarithmicRadius d R) (-(logarithmicRadius d R t / d)) t := by
  change HasDerivAt (fun t : ℝ => R * Real.exp (-t / d)) _ t
  have h := ((((hasDerivAt_id t).neg).div_const (d : ℝ)).exp).const_mul R
  convert h using 1 <;> simp [logarithmicRadius, div_eq_mul_inv, mul_assoc]

/-- The exact Jacobian identity σ r^(d-1)|dr| = (σ R^d/d)e^(-t)dt. -/
lemma logarithmicRadius_density {d : ℕ} (hd : 0 < d) (R t σ : ℝ) :
    (logarithmicRadius d R t / d) * (σ * logarithmicRadius d R t ^ (d - 1)) =
      (σ * R ^ d / d) * Real.exp (-t) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hpow : logarithmicRadius d R t ^ d = R ^ d * Real.exp (-t) := by
    unfold logarithmicRadius
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    field_simp
  calc
    _ = (σ / d) * (logarithmicRadius d R t * logarithmicRadius d R t ^ (d - 1)) := by ring
    _ = (σ / d) * logarithmicRadius d R t ^ d := by
      rw [← pow_succ', Nat.sub_add_cancel hd]
    _ = _ := by rw [hpow]; ring

/-- Logarithmic substitution for nonnegative integrals, valid without an
advance integrability assumption on F. -/
lemma logarithmic_lintegral {d : ℕ} (hd : 0 < d) {R σ : ℝ}
    (hR : 0 < R) (hσ : 0 ≤ σ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ r in Ioo 0 R, ENNReal.ofReal (σ * r ^ (d - 1)) * F r) =
      ENNReal.ofReal (σ * R ^ d / d) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) * F (logarithmicRadius d R t) := by
  rw [← logarithmicRadius_image hd hR]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun t _ => (logarithmicRadius_hasDerivAt d R t).hasDerivWithinAt)
    (logarithmicRadius_injective hd hR).injOn]
  rw [← lintegral_const_mul' _ _ (by finiteness)]
  apply lintegral_congr_ae
  filter_upwards with t
  have hp := (logarithmicRadius_pos (d := d) hR t).le
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [abs_neg, abs_of_nonneg (div_nonneg hp hd0.le), ← mul_assoc,
    ← ENNReal.ofReal_mul (div_nonneg hp hd0.le), logarithmicRadius_density hd,
    ENNReal.ofReal_mul (by positivity)]
  exact mul_assoc _ _ _

lemma criticalPower_gt_one {d : ℕ} (hd : 2 ≤ d) : 1 < criticalPower d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold criticalPower
  apply (lt_div_iff₀ (by linarith : 0 < (d : ℝ) - 1)).mpr
  linarith

/-- The geometric volume factor in the radial substitution. -/
lemma logarithmic_volume_factor {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (sphereArea d * R ^ d / d) = volume (Metric.ball (0 : Space d) R) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hv : volume (Metric.ball (0 : Space d) R) =
      ENNReal.ofReal (R ^ d) * volume (Metric.ball (0 : Space d) 1) := by
    simpa [Space] using Measure.addHaar_ball_of_pos volume (0 : Space d) hR
  rw [sphereArea_eq_ball]
  have he : (d * volume.real (Metric.ball (0 : Space d) 1)) * R ^ d / d =
      R ^ d * volume.real (Metric.ball (0 : Space d) 1) := by field_simp
  rw [he, ENNReal.ofReal_mul (pow_nonneg hR.le _), ofReal_measureReal]
  exact hv.symm

lemma radial_ball_lintegral {d : ℕ} (hd : 0 < d) (R : ℝ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x in Metric.ball (0 : Space d) R, F ‖x‖) =
      ENNReal.ofReal (sphereArea d) *
        ∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal (r ^ (d - 1)) * F r := by
  have hb : (fun x : Space d => (Metric.ball (0 : Space d) R).indicator
      (fun x => F ‖x‖) x) = (fun x => (Iio R).indicator F ‖x‖) := by
    ext x
    by_cases hx : ‖x‖ < R <;> simp [Metric.mem_ball, dist_zero_right, hx]
  rw [← lintegral_indicator measurableSet_ball, hb,
    radial_lintegral hd ((Iio R).indicator F) (hF.indicator measurableSet_Iio)]
  congr 1
  have hi : (fun r : ℝ => ENNReal.ofReal (r ^ (d - 1)) * (Iio R).indicator F r) =
      (Iio R).indicator (fun r => ENNReal.ofReal (r ^ (d - 1)) * F r) := by
    ext r
    by_cases hr : r < R <;> simp [hr]
  rw [hi, setLIntegral_indicator measurableSet_Iio]
  congr 1
  congr 1
  exact Set.ext fun r => and_comm

/-- The exact radial exponential integral identity. The only hypotheses here
are on the measurable radial profile, not on its derivatives. -/
lemma radial_exponential_change {d : ℕ} (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hφnn : ∀ r > 0, 0 ≤ φ r) :
    (∫⁻ x in Metric.ball (0 : Space d) R,
      ENNReal.ofReal (Real.exp (sharpCoefficient d * (φ ‖x‖) ^ criticalPower d))) =
      volume (Metric.ball (0 : Space d) R) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp
          ((profileScale d * φ (logarithmicRadius d R t)) ^ criticalPower d - t)) := by
  let F : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (sharpCoefficient d * φ r ^ criticalPower d))
  have hF : Measurable F := by dsimp [F]; fun_prop
  rw [radial_ball_lintegral (by omega) R F hF]
  rw [← lintegral_const_mul' _ _ (by finiteness)]
  have he : (∫⁻ r in Ioo (0 : ℝ) R,
      ENNReal.ofReal (sphereArea d) * (ENNReal.ofReal (r ^ (d - 1)) * F r)) =
      ∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal (sphereArea d * r ^ (d - 1)) * F r := by
    apply lintegral_congr_ae
    filter_upwards with r
    rw [ENNReal.ofReal_mul (sphereArea_pos (by omega)).le, mul_assoc]
  rw [he, logarithmic_lintegral (by omega) hR (sphereArea_pos (by omega)).le F,
    logarithmic_volume_factor (by omega) hR]
  congr 1
  apply lintegral_congr_ae
  filter_upwards with t
  dsimp [F]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    scaled_profile_power hd (hφnn _ (logarithmicRadius_pos hR t))]
  congr 2
  ring

/-- On an arbitrary fixed scalar level, almost every existing line derivative
vanishes. The scalar may be real or complex. -/
lemma ae_line_derivative_zero {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (c : 𝕜) :
    ∀ᵐ t ∂volume, f t = c → ∀ v, HasDerivAt f v t → v = 0 := by
  let s := {t | f t = c}
  have hc : {t ∈ s | 𝓝[s ∩ Ioi t] t = ⊥}.Countable :=
    countable_setOfPred_isolated_right_within
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hc.measure_zero (μ := volume))]
    with t ht htc v hv
  have hn : (𝓝[s ∩ Ioi t] t).NeBot := ⟨fun h => ht ⟨htc, h⟩⟩
  have hn' : (𝓝[s \ {t}] t).NeBot := hn.mono
    (nhdsWithin_mono t (fun z hz => ⟨hz.1, by simpa using ne_of_gt hz.2⟩))
  have hud : UniqueDiffWithinAt ℝ s t :=
    uniqueDiffWithinAt_iff_accPt.mpr (accPt_principal_iff_nhdsWithin.mpr hn')
  have hz : HasDerivWithinAt f 0 s t :=
    (hasDerivWithinAt_const t s c).congr (fun z hz => hz) htc
  exact (hv.hasDerivWithinAt.derivWithin hud).symm.trans (hz.derivWithin hud)

lemma hasDerivAt_norm_of_zero {𝕜 : Type} [RCLike 𝕜] {f : ℝ → 𝕜} {t : ℝ}
    (hf : HasDerivAt f 0 t) : HasDerivAt (fun s => ‖f s‖) 0 t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hf ⊢
  simp only [smul_zero, sub_zero] at hf ⊢
  exact (Asymptotics.isBigO_of_le' (c := (1 : ℝ)) (𝓝 0)
    (fun s => by simpa only [Real.norm_eq_abs, one_mul] using abs_norm_sub_norm_le (f (t + s)) (f t))).trans_isLittleO hf

/-- The differential of the norm, assigned zero at its only singular point. -/
def normDifferential {𝕜 : Type} [RCLike 𝕜] (z : 𝕜) : 𝕜 →L[ℝ] ℝ :=
  fderiv ℝ (norm : 𝕜 → ℝ) z

lemma normDifferential_bound {𝕜 : Type} [RCLike 𝕜] (z v : 𝕜) :
    ‖normDifferential z v‖ ≤ ‖v‖ := by
  have hb : ‖normDifferential z‖ ≤ 1 := by
    exact norm_fderiv_le_of_lipschitz ℝ (f := norm) (x₀ := z)
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : 𝕜 → ℝ))
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg v))

lemma normDifferential_zero {𝕜 : Type} [RCLike 𝕜] :
    normDifferential (0 : 𝕜) = 0 :=
  fderiv_zero_of_not_differentiableAt (not_differentiableAt_norm_zero 𝕜)

/-- Absolute value belongs to the actual real Sobolev space, with its weak
derivatives represented by the real differential of the scalar norm. -/
lemma absoluteValue_sobolev {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω 1 p) :
    ∃ v : Sobolev ℝ Ω 1 p,
      sobolevUnderlying v =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => ‖sobolevUnderlying u x‖) ∧
      ∀ j : Fin d, firstWeakDerivative v j =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => normDifferential (sobolevUnderlying u x) (firstWeakDerivative u j x)) := by
  let μ := volume.restrict (Ω : Set (Space d))
  have hm : MemLp (fun x => ‖sobolevUnderlying u x‖) p μ := (Lp.memLp _).norm
  have hk (j : Fin d) : MemLp
      (fun x => normDifferential (sobolevUnderlying u x) (firstWeakDerivative u j x)) p μ := by
    apply (Lp.memLp (firstWeakDerivative u j)).of_le
    · have heval : Continuous (fun z : (𝕜 →L[ℝ] ℝ) × 𝕜 => z.1 z.2) :=
        continuous_fst.clm_apply continuous_snd
      have hfield := (measurable_fderiv ℝ (norm : 𝕜 → ℝ)).comp_aemeasurable
        (Lp.aestronglyMeasurable (sobolevUnderlying u)).aemeasurable
      exact (heval.measurable.comp_aemeasurable
        (hfield.prodMk (Lp.aestronglyMeasurable (firstWeakDerivative u j)).aemeasurable)).aestronglyMeasurable
    · exact Eventually.of_forall fun x => normDifferential_bound _ _
  let v := hm.toLp (fun x => ‖sobolevUnderlying u x‖)
  let k := fun j => (hk j).toLp
    (fun x => normDifferential (sobolevUnderlying u x) (firstWeakDerivative u j x))
  have hv : v =ᵐ[μ] (fun x => ‖sobolevUnderlying u x‖) := hm.coeFn_toLp
  have hke (j : Fin d) : k j =ᵐ[μ]
      (fun x => normDifferential (sobolevUnderlying u x) (firstWeakDerivative u j x)) :=
    (hk j).coeFn_toLp
  have heq (j : Fin d) : distributionPartial {j} (regularDistribution Ω v) =
      regularDistribution Ω (k j) := by
    have hd : 0 < d := Nat.zero_lt_of_lt j.isLt
    obtain ⟨f, huf, hf⟩ := (acl_characterization d hd 𝕜 Ω j (sobolevUnderlying u)
      (firstWeakDerivative u j) (domainLp_locallyIntegrable Ω p _)
      (domainLp_locallyIntegrable Ω p _)).mp
        (sobolev_derivative_distribution Ω 1 p u (firstSobolevIndex j))
    apply acl_converse d hd ℝ Ω j v (k j) (domainLp_locallyIntegrable Ω p _)
      (domainLp_locallyIntegrable Ω p _)
    refine ⟨fun x => ‖f x‖, hv.trans (huf.fun_comp norm), ?_⟩
    filter_upwards [hf, acl_ae_on_fibers Ω j huf, acl_ae_on_fibers Ω j (hke j)]
      with z hfz huz hkz
    refine ⟨fun a b hab => lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval
      (hfz.1 a b hab), ?_⟩
    have hz := (ae_line_derivative_zero (fun t => f (ACL.line j z t)) 0).filter_mono
      (ae_restrict_le (s := ACL.fiber Ω j z))
    filter_upwards [hfz.2, huz, hkz, hz] with t hft hut hkt hzt
    rw [hkt, hut]
    by_cases hzero : f (ACL.line j z t) = 0
    · have hd0 := hzt hzero _ hft
      rw [hzero, normDifferential_zero, zero_apply]
      exact hasDerivAt_norm_of_zero (hd0 ▸ hft)
    · have hnorm : DifferentiableAt ℝ (norm : 𝕜 → ℝ) (f (ACL.line j z t)) :=
        (contDiffAt_norm ℝ (n := 1) hzero).differentiableAt (by decide)
      exact hnorm.hasFDerivAt.comp_hasDerivAt t hft
  obtain ⟨V, hV, hD⟩ := firstOrder_graph Ω p v k heq
  exact ⟨V, hV ▸ hv, fun j => hD j ▸ hke j⟩

/-- The scalar norm contracts the Euclidean weak gradient for both real and
complex functions. The estimate holds pointwise a.e. and in every Lp norm. -/
lemma absoluteValue_gradient_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω 1 p) :
    ∃ v : Sobolev ℝ Ω 1 p,
      sobolevUnderlying v =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => ‖sobolevUnderlying u x‖) ∧
      (∀ᵐ x ∂volume.restrict (Ω : Set (Space d)), ‖weakGradient v x‖ ≤ ‖weakGradient u x‖) ∧
      eLpNorm (weakGradient v) p (volume.restrict (Ω : Set (Space d))) ≤
        eLpNorm (weakGradient u) p (volume.restrict (Ω : Set (Space d))) := by
  obtain ⟨v, hv, hD⟩ := absoluteValue_sobolev Ω p u
  have hbound : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)),
      ‖weakGradient v x‖ ≤ ‖weakGradient u x‖ := by
    filter_upwards [ae_all_iff.mpr hD] with x hx
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
      EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    change ‖firstWeakDerivative v j x‖ ^ 2 ≤ ‖firstWeakDerivative u j x‖ ^ 2
    rw [hx j]
    exact pow_le_pow_left₀ (norm_nonneg _) (normDifferential_bound _ _) 2
  refine ⟨v, hv, hbound, eLpNorm_mono_ae ?_ hbound⟩
  have hpi : AEMeasurable (fun x => fun j : Fin d => firstWeakDerivative v j x)
      (volume.restrict (Ω : Set (Space d))) :=
    aemeasurable_pi_iff.mpr fun j => (Lp.aestronglyMeasurable (firstWeakDerivative v j)).aemeasurable
  exact ((PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable hpi).aestronglyMeasurable

/-- The first reduction on arbitrary open sets: zero extension and absolute
value give a nonnegative whole-space Sobolev function without increasing its
Euclidean gradient norm. -/
lemma absoluteValue_zeroExtension {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : SobolevZero 𝕜 Ω 1 p) {R : ℝ}
    (hΩR : (Ω : Set (Space d)) ⊆ Metric.closedBall 0 R) :
    ∃ f : Polarization.WholeSobolev d p,
      sobolevUnderlying f =ᵐ[volume]
        (fun x => ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖) ∧
      Polarization.SupportedNonnegative R f ∧
      eLpNorm (Polarization.gradient f) p volume ≤
        eLpNorm (weakGradient u.val) p (volume.restrict (Ω : Set (Space d))) := by
  obtain ⟨f, hf, _, hgrad⟩ := absoluteValue_gradient_bound (⊤ : Opens (Space d)) p
    (sobolevZeroExtensionLI Ω 1 p u)
  simp only [Opens.coe_top, Measure.restrict_univ] at hf hgrad
  refine ⟨f, hf, ⟨?_, ?_⟩, hgrad.trans_eq (zeroExtension_gradient_eLpNorm Ω p u)⟩
  · filter_upwards [hf] with x hx
    rw [hx]
    exact norm_nonneg _
  · filter_upwards [hf, zeroExtension_zero_off Ω p u] with x hx hzero hxR
    rw [hx, hzero (fun hxΩ => hxR (hΩR hxΩ)), norm_zero]

/-- Complete initial reduction for arbitrary real or complex inputs and
bounded open sets. The pending rearrangement theorems occur only as explicit
parameters, in the prescribed order. -/
lemma rearrangement_reduction_conditional
    (hExists : PolyaSzegoExpected.Existence)
    (hRadial : PolyaSzegoExpected.RadialCharacterization)
    (hUnique : PolyaSzegoExpected.Uniqueness)
    {d : ℕ} (hd : 0 < d) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (hΩ : Bornology.IsBounded (Ω : Set (Space d)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpfin : p ≠ ∞)
    (u : SobolevZero 𝕜 Ω 1 p) :
    ∃ R : ℝ, 0 < R ∧ ∃ g : Polarization.WholeSobolev d p,
      Polarization.SupportedNonnegative R g ∧
      Rearrangement.IsRearrangement
        (fun x => ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖) (sobolevUnderlying g) ∧
      Rearrangement.IsRadiallyNonincreasing (sobolevUnderlying g) ∧
      eLpNorm (Polarization.gradient g) p volume ≤
        eLpNorm (weakGradient u.val) p (volume.restrict (Ω : Set (Space d))) ∧
      ∀ h : Space d → ℝ, Rearrangement.IsRearrangement
        (fun x => ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖) h →
        sobolevUnderlying g =ᵐ[volume] h := by
  obtain ⟨R, hR, hΩR⟩ := hΩ.subset_ball_lt 0 (0 : Space d)
  obtain ⟨f, hf, hs, hgrad⟩ := absoluteValue_zeroExtension Ω p u
    (hΩR.trans Metric.ball_subset_closedBall)
  obtain ⟨g, hg, hre, _, hgg⟩ := hExists d hd p hp hpfin R hR f hs
  have hre' : Rearrangement.IsRearrangement
      (fun x => ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖) (sobolevUnderlying g) := by
    refine ⟨hre.1, hre.2.1, fun s hs => (hre.2.2 s hs).trans ?_⟩
    apply measure_congr
    filter_upwards [hf] with x hx
    simp only [hx]
  refine ⟨R, hR, g, hg, hre', (hRadial d hd p hp hpfin R hR g hg).mp hre'.2.1,
    hgg.trans hgrad, ?_⟩
  exact fun h hh => hUnique d hd _ _ _ hre' hh

/-- In positive dimension, the volume order of centered balls is exactly
that of their nonnegative radii. -/
lemma ball_volume_le_iff {d : ℕ} (hd : 0 < d) {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    volume (Metric.ball (0 : Space d) r) ≤ volume (Metric.ball (0 : Space d) R) ↔
      r ≤ R := by
  let : NeZero d := ⟨by omega⟩
  have hv (a : ℝ) (ha : 0 ≤ a) :
      volume (Metric.ball (0 : Space d) a) =
        ENNReal.ofReal (a ^ d) * volume (Metric.ball (0 : Space d) 1) := by
    simpa [Space] using Measure.addHaar_ball volume (0 : Space d) ha
  rw [hv r hr, hv R hR]
  have hb0 : volume (Metric.ball (0 : Space d) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ (by norm_num : (0 : ℝ) < 1)).ne'
  rw [ENNReal.mul_le_mul_iff_left hb0 measure_ball_lt_top.ne,
    ENNReal.ofReal_le_ofReal_iff (pow_nonneg hR _)]
  exact pow_le_pow_iff_left₀ hr hR (by omega)

/-- A nonempty bounded open set has the volume of a centered ball of
strictly positive finite radius, with no boundary regularity hypothesis. -/
lemma exists_equivolume_ball {d : ℕ} (hd : 0 < d) (Ω : Opens (Space d))
    (hne : (Ω : Set (Space d)).Nonempty)
    (hb : Bornology.IsBounded (Ω : Set (Space d))) :
    ∃ R : ℝ, 0 < R ∧ volume (Metric.ball (0 : Space d) R) = volume (Ω : Set (Space d)) := by
  have hv0 : 0 < volume.real (Ω : Set (Space d)) :=
    ENNReal.toReal_pos (Ω.isOpen.measure_pos volume hne).ne' hb.measure_lt_top.ne
  have hunit : 0 < volume.real (Metric.ball (0 : Space d) 1) :=
    ENNReal.toReal_pos
      (Metric.measure_ball_pos volume _ (by norm_num : (0 : ℝ) < 1)).ne'
      measure_ball_lt_top.ne
  let R : ℝ := (volume.real (Ω : Set (Space d)) /
    volume.real (Metric.ball (0 : Space d) 1)) ^ (1 / (d : ℝ))
  have hR : 0 < R := Real.rpow_pos_of_pos (div_pos hv0 hunit) _
  refine ⟨R, hR, ?_⟩
  have hpow : R ^ d = volume.real (Ω : Set (Space d)) /
      volume.real (Metric.ball (0 : Space d) 1) := by
    simpa only [R, one_div] using Real.rpow_inv_natCast_pow (div_pos hv0 hunit).le (by omega : d ≠ 0)
  have he : volume (Metric.ball (0 : Space d) R) =
      ENNReal.ofReal (R ^ d) * volume (Metric.ball (0 : Space d) 1) := by
    simpa [Space] using Measure.addHaar_ball_of_pos volume (0 : Space d) hR
  rw [he, hpow, ← ofReal_measureReal (μ := volume) (s := Metric.ball (0 : Space d) 1),
    ← ENNReal.ofReal_mul (div_pos hv0 hunit).le,
    div_mul_cancel₀ _ hunit.ne', ofReal_measureReal hb.measure_lt_top.ne]

/-- Equimeasurability and centered superlevels place the rearrangement inside
the ball whose volume bounds the original support. Countably many rational
levels suffice, so exceptional sets need not be uniform over real levels. -/
lemma rearrangement_supported_in_equivolume_ball {d : ℕ} (hd : 0 < d)
    {f g : Space d → ℝ} {Ω : Set (Space d)} {R : ℝ} (hR : 0 ≤ R)
    (hvol : volume Ω ≤ volume (Metric.ball (0 : Space d) R))
    (hf : ∀ᵐ x ∂volume, x ∉ Ω → f x = 0)
    (hre : Rearrangement.IsRearrangement f g) :
    ∀ᵐ x ∂volume, x ∉ Metric.ball (0 : Space d) R → g x = 0 := by
  have hlevel (s : ℝ) (hs : 0 < s) :
      ∀ᵐ x ∂volume, s < g x → x ∈ Metric.ball (0 : Space d) R := by
    obtain ⟨r, hr, heq⟩ := hre.2.1 s hs
    have hle : volume (Metric.ball (0 : Space d) r) ≤
        volume (Metric.ball (0 : Space d) R) := by
      rw [← measure_congr heq, hre.2.2 s hs]
      apply le_trans _ hvol
      apply measure_mono_ae
      filter_upwards [hf] with x hx hxs
      by_contra hxΩ
      have hz := hx hxΩ
      simp only [hz] at hxs
      linarith
    have hrR := (ball_volume_le_iff hd hr hR).mp hle
    filter_upwards [heq] with x hx hxs
    exact Metric.ball_subset_ball hrR (hx.mp hxs)
  have hrat (q : ℚ) : ∀ᵐ x ∂volume,
      0 < (q : ℝ) → (q : ℝ) < g x → x ∈ Metric.ball (0 : Space d) R := by
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [hlevel q hq] with x hx _ hqx
      exact hx hqx
    · exact Eventually.of_forall fun _ h => (hq h).elim
  filter_upwards [hre.1, ae_all_iff.mpr hrat] with x hxnn hx hxR
  apply le_antisymm _ hxnn
  by_contra hxpos
  obtain ⟨q, hq0, hqx⟩ := exists_rat_btwn (lt_of_not_ge hxpos)
  exact hxR (hx q hq0 hqx)


/-- If the function vanishes off a measurable set, its exponential integral
is the ambient exponential excess plus the measure of that set. -/
lemma exponential_integral_eq_excess_add_volume
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {s : Set X}
    (hs : MeasurableSet s) {f : X → ℝ}
    (hf : 0 ≤ᵐ[μ] f) (hzero : ∀ᵐ x ∂μ, x ∉ s → f x = 0)
    {A q : ℝ} (hA : 0 ≤ A) (hq : 0 < q) :
    (∫⁻ x in s, ENNReal.ofReal (Real.exp (A * f x ^ q)) ∂μ) =
      (∫⁻ x, ENNReal.ofReal (Real.exp (A * f x ^ q) - 1) ∂μ) + μ s := by
  have heq : (fun x => ENNReal.ofReal (Real.exp (A * f x ^ q))) =ᵐ[μ.restrict s]
      (fun x => ENNReal.ofReal (Real.exp (A * f x ^ q) - 1) + 1) := by
    filter_upwards [hf.filter_mono (ae_restrict_le (s := s))] with x hx
    have hxexp : 1 ≤ Real.exp (A * f x ^ q) :=
      Real.one_le_exp (mul_nonneg hA (Real.rpow_nonneg hx _))
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (sub_nonneg.mpr hxexp) zero_le_one,
      sub_add_cancel]
  rw [lintegral_congr_ae heq, lintegral_add_right _ measurable_const]
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]
  congr 1
  rw [← lintegral_indicator hs]
  apply lintegral_congr_ae
  filter_upwards [hzero] with x hx
  by_cases hxs : x ∈ s
  · simp [hxs]
  · simp [hxs, hx hxs, Real.zero_rpow hq.ne']

lemma exponential_integral_eq_of_equimeasurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {s : Set X} {t : Set Y}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    {f : X → ℝ} {g : Y → ℝ} (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[ν] g)
    (hmf : AEMeasurable f μ) (hmg : AEMeasurable g ν)
    (hfzero : ∀ᵐ x ∂μ, x ∉ s → f x = 0)
    (hgzero : ∀ᵐ y ∂ν, y ∉ t → g y = 0)
    (hlevels : ∀ a : ℝ, 0 < a → μ {x | a < f x} = ν {y | a < g y})
    (hvol : μ s = ν t) {A q : ℝ} (hA : 0 ≤ A) (hq : 1 < q) :
    (∫⁻ x in s, ENNReal.ofReal (Real.exp (A * f x ^ q)) ∂μ) =
      ∫⁻ y in t, ENNReal.ofReal (Real.exp (A * g y ^ q)) ∂ν := by
  rw [exponential_integral_eq_excess_add_volume μ hs hf hfzero hA (by linarith),
    exponential_integral_eq_excess_add_volume ν ht hg hgzero hA (by linarith),
    exponential_excess_equimeasurable μ ν hf hg hmf hmg hlevels hA hq, hvol]

/-- Monotone Lipschitz changes of the independent variable preserve absolute continuity. -/
lemma ac_comp_monotone_lipschitz {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {g : ℝ → ℝ} {a b c d : ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f c d)
    (hg : MonotoneOn g (uIcc a b))
    (hK : LipschitzOnWith K g (uIcc a b))
    (hmap : MapsTo g (uIcc a b) (uIcc c d)) :
    AbsolutelyContinuousOnInterval (f ∘ g) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := hf ε hε
  refine ⟨δ / (K + 1), by positivity, ?_⟩
  intro E hE hlen
  let G : ℕ × (ℕ → ℝ × ℝ) := (E.1, fun i => (g (E.2 i).1, g (E.2 i).2))
  apply hδprop G
  · constructor
    · intro i hi
      exact ⟨hmap (hE.1 i hi).1, hmap (hE.1 i hi).2⟩
    · intro i hi j hj hij
      have hdij := hE.2 hi hj hij
      change Disjoint (uIoc (g (E.2 i).1) (g (E.2 i).2))
        (uIoc (g (E.2 j).1) (g (E.2 j).2))
      dsimp only [Function.onFun] at hdij
      unfold uIoc at hdij ⊢
      rw [Ioc_disjoint_Ioc] at hdij ⊢
      have hmin (x y : ℝ) (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
          min x y ∈ uIcc a b := by rcases min_choice x y with h | h <;> simpa [h]
      have hmax (x y : ℝ) (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
          max x y ∈ uIcc a b := by rcases max_choice x y with h | h <;> simpa [h]
      have hii := hE.1 i hi
      have hjj := hE.1 j hj
      have hip := hmin _ _ hii.1 hii.2
      have hjp := hmin _ _ hjj.1 hjj.2
      have hiq := hmax _ _ hii.1 hii.2
      have hjq := hmax _ _ hjj.1 hjj.2
      have h := hg (hmin _ _ hiq hjq) (hmax _ _ hip hjp) hdij
      simpa only [hg.map_min hii.1 hii.2, hg.map_min hjj.1 hjj.2,
        hg.map_max hii.1 hii.2, hg.map_max hjj.1 hjj.2,
        hg.map_min hiq hjq, hg.map_max hip hjp] using h
  · calc
      _ ≤ (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        exact hK.dist_le_mul _ (hE.1 i hi).1 _ (hE.1 i hi).2
      _ ≤ K * (δ / (K + 1)) := by gcongr
      _ < (K + 1) * (δ / (K + 1)) := by gcongr; linarith
      _ = δ := by field_simp

/-- Antitone Lipschitz changes of the independent variable preserve absolute continuity. -/
lemma ac_comp_antitone_lipschitz {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {g : ℝ → ℝ} {a b c d : ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f c d)
    (hg : AntitoneOn g (uIcc a b))
    (hK : LipschitzOnWith K g (uIcc a b))
    (hmap : MapsTo g (uIcc a b) (uIcc c d)) :
    AbsolutelyContinuousOnInterval (f ∘ g) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := hf ε hε
  refine ⟨δ / (K + 1), by positivity, ?_⟩
  intro E hE hlen
  let G : ℕ × (ℕ → ℝ × ℝ) := (E.1, fun i => (g (E.2 i).1, g (E.2 i).2))
  apply hδprop G
  · constructor
    · intro i hi
      exact ⟨hmap (hE.1 i hi).1, hmap (hE.1 i hi).2⟩
    · intro i hi j hj hij
      have hdij := hE.2 hi hj hij
      change Disjoint (uIoc (g (E.2 i).1) (g (E.2 i).2))
        (uIoc (g (E.2 j).1) (g (E.2 j).2))
      dsimp only [Function.onFun] at hdij
      unfold uIoc at hdij ⊢
      rw [Ioc_disjoint_Ioc] at hdij ⊢
      have hmin (x y : ℝ) (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
          min x y ∈ uIcc a b := by rcases min_choice x y with h | h <;> simpa [h]
      have hmax (x y : ℝ) (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
          max x y ∈ uIcc a b := by rcases max_choice x y with h | h <;> simpa [h]
      have hii := hE.1 i hi
      have hjj := hE.1 j hj
      have hip := hmin _ _ hii.1 hii.2
      have hjp := hmin _ _ hjj.1 hjj.2
      have hiq := hmax _ _ hii.1 hii.2
      have hjq := hmax _ _ hjj.1 hjj.2
      have h := hg (hmin _ _ hiq hjq) (hmax _ _ hip hjp) hdij
      simpa only [hg.map_min hii.1 hii.2, hg.map_min hjj.1 hjj.2,
        hg.map_max hii.1 hii.2, hg.map_max hjj.1 hjj.2,
        hg.map_min hiq hjq, hg.map_max hip hjp] using h
  · calc
      _ ≤ (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        exact hK.dist_le_mul _ (hE.1 i hi).1 _ (hE.1 i hi).2
      _ ≤ K * (δ / (K + 1)) := by gcongr
      _ < (K + 1) * (δ / (K + 1)) := by gcongr; linarith
      _ = δ := by field_simp

/-- Rearrangement of the modulus of the zero extension, supported inside the
open ball with the same volume as the original domain. -/
lemma rearrangement_reduction_equivolume_conditional
    (hExists : PolyaSzegoExpected.Existence)
    (hRadial : PolyaSzegoExpected.RadialCharacterization)
    (hUnique : PolyaSzegoExpected.Uniqueness)
    {d : ℕ} (hd : 0 < d) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (hne : (Ω : Set (Space d)).Nonempty)
    (hΩ : Bornology.IsBounded (Ω : Set (Space d)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hpfin : p ≠ ∞)
    (u : SobolevZero 𝕜 Ω 1 p) :
    ∃ R : ℝ, 0 < R ∧
      volume (Metric.ball (0 : Space d) R) = volume (Ω : Set (Space d)) ∧
      ∃ g : Polarization.WholeSobolev d p,
        Polarization.SupportedNonnegative R g ∧
        Rearrangement.IsRearrangement
          (fun x => ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖)
          (sobolevUnderlying g) ∧
        Rearrangement.IsRadiallyNonincreasing (sobolevUnderlying g) ∧
        (∀ᵐ x ∂volume, x ∉ Metric.ball (0 : Space d) R →
          sobolevUnderlying g x = 0) ∧
        eLpNorm (Polarization.gradient g) p volume ≤
          eLpNorm (weakGradient u.val) p (volume.restrict (Ω : Set (Space d))) ∧
        ∀ h : Space d → ℝ, Rearrangement.IsRearrangement
          (fun x => ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖) h →
          sobolevUnderlying g =ᵐ[volume] h := by
  obtain ⟨R, hR, hvol⟩ := exists_equivolume_ball hd Ω hne hΩ
  obtain ⟨S, hS, g, hg, hre, hrad, hgrad, huniq⟩ :=
    rearrangement_reduction_conditional hExists hRadial hUnique hd Ω hΩ p hp hpfin u
  have hzero : ∀ᵐ x ∂volume, x ∉ Ω →
      ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖ = 0 := by
    filter_upwards [zeroExtension_zero_off Ω p u] with x hx hxΩ
    rw [hx hxΩ, norm_zero]
  have hsupp := rearrangement_supported_in_equivolume_ball hd hR.le
    (le_of_eq hvol.symm) hzero hre
  refine ⟨R, hR, hvol, g, ⟨hre.1, ?_⟩, hre, hrad, hsupp, hgrad, huniq⟩
  filter_upwards [hsupp] with x hx hxR
  exact hx (fun hxb => hxR (Metric.ball_subset_closedBall hxb))
lemma logarithmicRadius_antitone {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) :
    Antitone (logarithmicRadius d R) := by
  intro s t hst
  unfold logarithmicRadius
  apply mul_le_mul_of_nonneg_left _ hR.le
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (neg_le_neg hst) (by positivity)

lemma logarithmicRadius_zero (d : ℕ) (R : ℝ) : logarithmicRadius d R 0 = R := by
  simp [logarithmicRadius]

lemma logarithmicRadius_lipschitzOn {d : ℕ} (hd : 0 < d) {R T : ℝ} (hR : 0 < R) :
    LipschitzOnWith ⟨R / d, by positivity⟩ (logarithmicRadius d R) (Icc 0 T) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc (0 : ℝ) T)
    (fun t _ => (logarithmicRadius_hasDerivAt d R t).hasDerivWithinAt)
  intro t ht
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  change ‖-(logarithmicRadius d R t / d)‖ ≤ R / d
  simp only [norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (logarithmicRadius_pos (d := d) hR t).le hd0.le)]
  exact div_le_div_of_nonneg_right
    (by simpa only [logarithmicRadius_zero] using logarithmicRadius_antitone hd hR ht.1) hd0.le

/-- A locally absolutely continuous radial profile stays locally absolutely
continuous after the precise logarithmic normalization, including time zero. -/
lemma logarithmic_profile_locallyAC {d : ℕ} (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R)
    {φ : ℝ → ℝ}
    (hφ : ACL.LocallyAC φ (Ioi 0)) :
    ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval
      (fun t => profileScale d * φ (logarithmicRadius d R t)) 0 T := by
  intro T hT
  have hradle : logarithmicRadius d R T ≤ R := by
    simpa only [logarithmicRadius_zero] using logarithmicRadius_antitone (by omega : 0 < d) hR hT
  have houter := hφ (logarithmicRadius d R T) R
    (by
      rw [uIcc_of_le hradle]
      intro r hr
      exact lt_of_lt_of_le (logarithmicRadius_pos hR T) hr.1)
  have hcomp : AbsolutelyContinuousOnInterval (φ ∘ logarithmicRadius d R) 0 T :=
    ac_comp_antitone_lipschitz houter
      ((logarithmicRadius_antitone (d := d) (by omega) hR).antitoneOn _)
      (by simpa [uIcc_of_le hT] using (logarithmicRadius_lipschitzOn
        (T := T) (by omega : 0 < d) hR))
      (by
        rw [uIcc_of_le hT, uIcc_of_le hradle]
        intro t ht
        exact ⟨logarithmicRadius_antitone (by omega) hR ht.2,
          by simpa only [logarithmicRadius_zero] using logarithmicRadius_antitone (by omega : 0 < d) hR ht.1⟩)
  simpa only [Function.comp_apply] using AbsolutelyContinuousOnInterval.const_mul (profileScale d) hcomp

lemma radial_exponential_bound_of_admissible {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), 0 < R → ∀ (φ : ℝ → ℝ),
      Measurable φ → (∀ r > 0, 0 ≤ φ r) →
      Moser.Admissible d (fun t => profileScale d * φ (logarithmicRadius d R t)) →
      (∫⁻ x in Metric.ball (0 : Space d) R,
        ENNReal.ofReal (Real.exp (sharpCoefficient d * φ ‖x‖ ^ criticalPower d))) ≤
          ENNReal.ofReal C * volume (Metric.ball (0 : Space d) R) := by
  obtain ⟨C, hC, hbound⟩ := normalized_moser_bound hd
  refine ⟨C, hC, fun R hR φ hφ hφnn hw => ?_⟩
  rw [radial_exponential_change hd hR φ hφ hφnn]
  exact hbound _ _ hw

lemma logarithmic_energy_density {d : ℕ} (hd : 2 ≤ d) (r : ℝ) :
    (profileScale d / d * r) ^ d =
      (r / d) * (sphereArea d * r ^ (d - 1)) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hpd : (d : ℝ) ^ d = (d : ℝ) ^ (d - 1) * d := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
  have hpr : r ^ d = r ^ (d - 1) * r := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
  rw [mul_pow, div_pow, profileScale_pow hd, hpd, hpr]
  field_simp

/-- The logarithmic derivative substitution preserves the full radial
Dirichlet energy under the exact Moser normalization. No measurability or
integrability assumption on the nonnegative integrand is required. -/
lemma logarithmic_energy_lintegral {d : ℕ} (hd : 2 ≤ d) {R : ℝ}
    (hR : 0 < R) (H : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal ((profileScale d / d * logarithmicRadius d R t) ^ d) *
        H (logarithmicRadius d R t)) =
      ENNReal.ofReal (sphereArea d) *
        ∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal (r ^ (d - 1)) * H r := by
  have hd' : 0 < d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd'
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (logarithmicRadius d R t / d) *
          (ENNReal.ofReal (sphereArea d * logarithmicRadius d R t ^ (d - 1)) *
            H (logarithmicRadius d R t)) := by
      apply lintegral_congr_ae
      filter_upwards with t
      rw [logarithmic_energy_density hd,
        ENNReal.ofReal_mul (div_nonneg (logarithmicRadius_pos hR t).le hd0.le), mul_assoc]
    _ = ∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal (sphereArea d * r ^ (d - 1)) * H r := by
      rw [← logarithmicRadius_image hd' hR,
        lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
          (fun t _ => (logarithmicRadius_hasDerivAt d R t).hasDerivWithinAt)
          (logarithmicRadius_injective hd' hR).injOn]
      apply lintegral_congr_ae
      filter_upwards with t
      rw [abs_neg, abs_of_nonneg (div_nonneg (logarithmicRadius_pos hR t).le hd0.le)]
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (sphereArea_pos hd').le, mul_assoc]
      exact lintegral_const_mul' _ _ (by finiteness)


/-- The logarithmic radius map pulls back the null set of nondifferentiability
of a real profile on the punctured ball interval to a null set of positive times. -/
lemma logarithmicRadius_ae_differentiableAt {d : ℕ} (hd : 0 < d) {R : ℝ}
    (hR : 0 < R) (φ : ℝ → ℝ)
    (hφ : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), DifferentiableAt ℝ φ r) :
    ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      DifferentiableAt ℝ φ (logarithmicRadius d R t) := by
  let bad : ℝ → ℝ≥0∞ := {r | ¬ DifferentiableAt ℝ φ r}.indicator (fun _ => 1)
  have hbad : Measurable bad := by
    exact measurable_const.indicator (measurableSet_of_differentiableAt ℝ φ).compl
  have hzero : (∫⁻ r in Ioo (0 : ℝ) R, bad r) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hφ] with r hr
    simp [bad, hr]
  rw [← logarithmicRadius_image hd hR,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
      (fun t _ => (logarithmicRadius_hasDerivAt d R t).hasDerivWithinAt)
      (logarithmicRadius_injective hd hR).injOn] at hzero
  have hm : Measurable (fun t => ENNReal.ofReal |-(logarithmicRadius d R t / d)| *
      bad (logarithmicRadius d R t)) := by
    have hrad : Measurable (logarithmicRadius d R) := by
      unfold logarithmicRadius
      fun_prop
    exact (by fun_prop : Measurable (fun t => ENNReal.ofReal |-(logarithmicRadius d R t / d)|)).mul
      (hbad.comp hrad)
  have hz := (lintegral_eq_zero_iff hm).mp hzero
  filter_upwards [hz] with t ht
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hj : ENNReal.ofReal |-(logarithmicRadius d R t / d)| ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr (abs_pos.mpr (neg_ne_zero.mpr
      (div_pos (logarithmicRadius_pos hR t) hd0).ne'))
  by_contra hn
  have hb : bad (logarithmicRadius d R t) = 1 := by simp [bad, hn]
  rw [hb, mul_one] at ht
  exact hj ht

/-- Chain rule for the normalized logarithmic profile, with the derivative
written in the form used by the exact energy identity. -/
lemma logarithmic_profile_hasDerivAt_ae {d : ℕ} (hd : 2 ≤ d) {R : ℝ}
    (hR : 0 < R) (φ : ℝ → ℝ)
    (hφ : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), DifferentiableAt ℝ φ r) :
    ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      HasDerivAt (fun t => profileScale d * φ (logarithmicRadius d R t))
        (-(profileScale d / d * logarithmicRadius d R t) *
          deriv φ (logarithmicRadius d R t)) t := by
  filter_upwards [logarithmicRadius_ae_differentiableAt (d := d) (by omega) hR φ hφ] with t ht
  convert (ht.hasDerivAt.comp t (logarithmicRadius_hasDerivAt d R t)).const_mul
    (profileScale d) using 1
  · rfl
  · ring


lemma zeroExtension_norm_ae_on {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : SobolevZero 𝕜 Ω 1 p) :
    (fun x => ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖) =ᵐ[volume.restrict (Ω : Set (Space d))]
      (fun x => ‖sobolevUnderlying u.val x‖) := by
  have hrep := (lpZeroExtension_ae Ω p (sobolevUnderlying u.val)).filter_mono
    (ae_restrict_le (s := (Ω : Set (Space d))))
  filter_upwards [hrep, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  change ‖lpZeroExtension Ω p (sobolevUnderlying u.val) x‖ = _
  rw [hx]
  simp only [Set.indicator_of_mem hxΩ]

set_option maxHeartbeats 800000 in
/-- The original exponential integral is exactly the integral on the
rearranged equal-volume ball, before any finiteness is known. -/
lemma exponential_integral_eq_rearranged_ball {d : ℕ} (hd : 2 ≤ d)
    {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SobolevZero 𝕜 Ω 1 p)
    {R : ℝ} (g : Polarization.WholeSobolev d p)
    (hre : Rearrangement.IsRearrangement
      (fun x => ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖)
      (sobolevUnderlying g))
    (hgzero : ∀ᵐ x ∂volume, x ∉ Metric.ball (0 : Space d) R → sobolevUnderlying g x = 0)
    (hvol : volume (Metric.ball (0 : Space d) R) = volume (Ω : Set (Space d))) :
    (∫⁻ x in (Ω : Set (Space d)), ENNReal.ofReal (Real.exp
      (sharpCoefficient d * ‖sobolevUnderlying u.val x‖ ^ criticalPower d))) =
      ∫⁻ x in Metric.ball (0 : Space d) R, ENNReal.ofReal (Real.exp
        (sharpCoefficient d * sobolevUnderlying g x ^ criticalPower d)) := by
  have hnorm := zeroExtension_norm_ae_on Ω p u
  have hnormzero : ∀ᵐ x ∂volume, x ∉ Ω →
      ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖ = 0 := by
    filter_upwards [zeroExtension_zero_off Ω p u] with x hx hxΩ
    rw [hx hxΩ, norm_zero]
  have hmf : AEMeasurable (fun x => ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖) volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (Lp.aestronglyMeasurable (sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u))).norm.aemeasurable
  have hmg : AEMeasurable (sobolevUnderlying g) volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (Lp.aestronglyMeasurable (sobolevUnderlying g)).aemeasurable
  calc
    _ = ∫⁻ x in (Ω : Set (Space d)), ENNReal.ofReal (Real.exp
        (sharpCoefficient d * ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖ ^ criticalPower d)) := by
      apply lintegral_congr_ae
      filter_upwards [hnorm] with x hx
      rw [hx]
    _ = _ := exponential_integral_eq_of_equimeasurable volume volume
      Ω.isOpen.measurableSet measurableSet_ball
      (Eventually.of_forall fun _ => norm_nonneg _) hre.1
      hmf hmg
      hnormzero hgzero (fun a ha => (hre.2.2 a ha).symm) hvol.symm
      (sharpCoefficient_pos hd).le (criticalPower_gt_one hd)

/-- The rearranged representative can be replaced by any a.e. radial profile. -/
lemma exponential_integral_eq_radial_profile {d : ℕ} (hd : 2 ≤ d)
    {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SobolevZero 𝕜 Ω 1 p)
    {R : ℝ} (g : Polarization.WholeSobolev d p) (φ : ℝ → ℝ)
    (hre : Rearrangement.IsRearrangement
      (fun x => ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) x‖)
      (sobolevUnderlying g))
    (hgzero : ∀ᵐ x ∂volume, x ∉ Metric.ball (0 : Space d) R → sobolevUnderlying g x = 0)
    (hvol : volume (Metric.ball (0 : Space d) R) = volume (Ω : Set (Space d)))
    (hφ : sobolevUnderlying g =ᵐ[volume] (fun x => φ ‖x‖)) :
    (∫⁻ x in (Ω : Set (Space d)), ENNReal.ofReal (Real.exp
      (sharpCoefficient d * ‖sobolevUnderlying u.val x‖ ^ criticalPower d))) =
      ∫⁻ x in Metric.ball (0 : Space d) R, ENNReal.ofReal (Real.exp
        (sharpCoefficient d * φ ‖x‖ ^ criticalPower d)) := by
  rw [exponential_integral_eq_rearranged_ball hd Ω p u g hre hgzero hvol]
  apply lintegral_congr_ae
  filter_upwards [hφ.filter_mono (ae_restrict_le (s := Metric.ball (0 : Space d) R))] with x hx
  rw [hx]

/-- Local absolute continuity on positive compact intervals gives ordinary
one-dimensional differentiability almost everywhere on the positive half-line. -/
lemma locallyAC_ae_differentiableAt_Ioi (φ : ℝ → ℝ)
    (hφ : ∀ a b : ℝ, 0 < a → a < b → AbsolutelyContinuousOnInterval φ a b) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), DifferentiableAt ℝ φ r := by
  apply ae_restrict_of_ae_restrict_inter_Ioo
  intro a b ha hb hab
  rw [ae_restrict_iff' (measurableSet_Ioi.inter measurableSet_Ioo)]
  filter_upwards [(hφ a b ha hab).ae_differentiableAt] with r hr hmem
  apply hr
  rw [uIcc_of_le hab.le]
  exact ⟨hmem.2.1.le, hmem.2.2.le⟩

lemma locallyAC_ae_differentiableAt_Ioo (φ : ℝ → ℝ)
    (hφ : ∀ a b : ℝ, 0 < a → a < b → AbsolutelyContinuousOnInterval φ a b)
    (R : ℝ) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), DifferentiableAt ℝ φ r := by
  exact ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self
    (locallyAC_ae_differentiableAt_Ioi φ hφ)


lemma naturalEnergy_eq_eLpNorm_pow {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f : X → E} {d : ℕ}
    (hd : 0 < d) (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ d) ∂μ) = (eLpNorm f (d : ℝ≥0∞) μ) ^ d := by
  have h := (eLpNorm_nnreal_pow_eq_lintegral (p := (d : ℝ≥0))
    (by exact_mod_cast hd.ne') hf).symm
  simpa only [ENNReal.coe_natCast, NNReal.coe_natCast, ENNReal.rpow_natCast,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h

lemma naturalEnergy_le_one {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f : X → E} {d : ℕ}
    (hd : 0 < d) (hf : AEStronglyMeasurable f μ)
    (hbound : eLpNorm f (d : ℝ≥0∞) μ ≤ 1) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ d) ∂μ) ≤ 1 := by
  rw [naturalEnergy_eq_eLpNorm_pow hd hf]
  exact (pow_le_pow_left' hbound d).trans_eq (one_pow d)
/-- A monotone profile equal a.e. to a continuous profile has no pointwise jumps. -/
lemma antitoneOn_eqOn_continuous_of_ae_eq {f h : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hf : AntitoneOn f U) (hh : ContinuousOn h U)
    (he : f =ᵐ[volume.restrict U] h) : EqOn f h U := by
  have he' : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ U → f y = h y :=
    (ae_restrict_iff' hU.measurableSet).mp he
  have hdense := (volume : Measure ℝ).dense_of_ae he'
  intro x hx
  have hhc : ContinuousAt h x := (hh x hx).continuousAt (hU.mem_nhds hx)
  apply le_antisymm
  · by_contra hbad
    have hlt : h x < f x := lt_of_not_ge hbad
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ h y < f x :=
      (show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hx).and (hhc.eventually (gt_mem_nhds hlt))
    obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp hnear
    obtain ⟨y, hyint, hye⟩ := hdense.inter_open_nonempty (Ioo (x - ε) x)
      isOpen_Ioo (nonempty_Ioo.mpr (by linarith))
    have hyclose : dist y x < ε := by rw [Real.dist_eq, abs_of_neg (by linarith [hyint.2] : y - x < 0)]; linarith [hyint.1]
    obtain ⟨hyU, hylt⟩ := hεprop hyclose
    have hmono := hf hyU hx hyint.2.le
    rw [hye hyU] at hmono
    linarith
  · by_contra hbad
    have hlt : f x < h x := lt_of_not_ge hbad
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ f x < h y :=
      (show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hx).and (hhc.eventually (lt_mem_nhds hlt))
    obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp hnear
    obtain ⟨y, hyint, hye⟩ := hdense.inter_open_nonempty (Ioo x (x + ε))
      isOpen_Ioo (nonempty_Ioo.mpr (by linarith))
    have hyclose : dist y x < ε := by rw [Real.dist_eq, abs_of_pos (by linarith [hyint.1] : 0 < y - x)]; linarith [hyint.2]
    obtain ⟨hyU, hylt⟩ := hεprop hyclose
    have hmono := hf hx hyU hyint.1.le
    rw [hye hyU] at hmono
    linarith

lemma line_add {d : ℕ} (j : Fin d) (z : ACL.Transverse j) (t : ℝ) :
    ACL.line j z t = ACL.line j z 0 + t • coordinateVector d j := by
  ext k
  simp only [ACL.line, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    coordinateVector, EuclideanSpace.basisFun_apply,
    ExpandedFA.Sobolev.Lines.coordinateLine]
  by_cases h : k = j
  · subst k; simp
  · simp [h]

lemma line_norm_sq {d : ℕ} (j : Fin d) (z : ACL.Transverse j) (t : ℝ) :
    ‖ACL.line j z t‖ ^ 2 = t ^ 2 + ‖ACL.line j z 0‖ ^ 2 := by
  rw [line_add, norm_add_sq_real]
  have hinner : inner ℝ (ACL.line j z 0) (coordinateVector d j) = 0 := by
    simp [coordinateVector, EuclideanSpace.inner_single_right, ACL.line,
      ExpandedFA.Sobolev.Lines.coordinateLine]
  have hnorm : ‖coordinateVector d j‖ = 1 := by
    simp [coordinateVector]
  simp [inner_smul_right, hinner, norm_smul, hnorm, Real.norm_eq_abs, sq_abs]
  ring

lemma line_norm_pos {d : ℕ} (j : Fin d) (z : ACL.Transverse j)
    {t : ℝ} (ht : 0 < t) : 0 < ‖ACL.line j z t‖ := by
  have h := line_norm_sq j z t
  nlinarith [sq_nonneg ‖ACL.line j z 0‖, norm_nonneg (ACL.line j z t)]

lemma line_norm_monotoneOn {d : ℕ} (j : Fin d) (z : ACL.Transverse j) :
    MonotoneOn (fun t => ‖ACL.line j z t‖) (Ioi 0) := by
  intro s hs t ht hst
  have hs' := line_norm_sq j z s
  have ht' := line_norm_sq j z t
  change ‖ACL.line j z s‖ ≤ ‖ACL.line j z t‖
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hsq : s ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hs.le ht.le).mpr hst
  linarith

/-- One generic ACL line already determines a radial antitone profile on all radii
strictly larger than the distance of that line from the origin. -/
lemma radial_profile_AC_of_line {d : ℕ} (j : Fin d) (z : ACL.Transverse j)
    {φ F : ℝ → ℝ} (hφ : AntitoneOn φ (Ioi 0))
    (hF : ACL.LocallyAC F univ)
    (he : (fun t => φ ‖ACL.line j z t‖) =ᵐ[volume] F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hz : ‖ACL.line j z 0‖ < a) :
    AbsolutelyContinuousOnInterval φ a b := by
  let c := ‖ACL.line j z 0‖ ^ 2
  let q : ℝ → ℝ := fun r => Real.sqrt (r ^ 2 - c)
  have hc : 0 ≤ c := sq_nonneg _
  have hrad (r : ℝ) (hr : a ≤ r) : 0 < r ^ 2 - c := by
    dsimp [c]
    nlinarith [norm_nonneg (ACL.line j z 0)]
  have hqpos (r : ℝ) (hr : a ≤ r) : 0 < q r := Real.sqrt_pos.mpr (hrad r hr)
  have hqnorm (r : ℝ) (hr : a ≤ r) : ‖ACL.line j z (q r)‖ = r := by
    have hnorm := line_norm_sq j z (q r)
    have hqsq : q r ^ 2 = r ^ 2 - c := Real.sq_sqrt (hrad r hr).le
    have hrpos : 0 < r := ha.trans_le hr
    dsimp [c] at hqsq
    nlinarith [norm_nonneg (ACL.line j z (q r))]
  have hqmono : MonotoneOn q (Icc a b) := by
    intro r hr s hs hrs
    apply Real.sqrt_le_sqrt
    nlinarith [ha.trans_le hr.1, ha.trans_le hs.1]
  have hqdiff : ContDiffOn ℝ 1 q (Icc a b) := by
    apply ContDiffOn.sqrt (contDiff_id.pow 2 |>.sub contDiff_const).contDiffOn
    intro r hr
    exact (hrad r hr.1).ne'
  obtain ⟨K, hK⟩ := hqdiff.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  have heq : EqOn (fun t => φ ‖ACL.line j z t‖) F (Ioi 0) :=
    antitoneOn_eqOn_continuous_of_ae_eq isOpen_Ioi
      (fun s hs t ht hst => hφ (line_norm_pos j z hs) (line_norm_pos j z ht)
        (line_norm_monotoneOn j z hs ht hst))
      ((ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn.continuousOn hF isOpen_univ).mono
        (subset_univ _)) (ae_restrict_of_ae he)
  have hmap : MapsTo q (Icc a b) (Icc (q a) (q b)) := by
    intro r hr
    exact ⟨hqmono ⟨le_rfl, hab⟩ hr hr.1, hqmono hr ⟨hab, le_rfl⟩ hr.2⟩
  have hcomp := ac_comp_monotone_lipschitz (a := a) (b := b) (g := q) (hF (q a) (q b) (subset_univ _))
    (by simpa [uIcc_of_le hab] using hqmono)
    (by simpa [uIcc_of_le hab] using hK)
    (by simpa [uIcc_of_le hab, uIcc_of_le (hqmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)] using hmap)
  apply hcomp.congr
  intro r hr
  have hrr : a ≤ r := (uIcc_of_le hab ▸ hr).1
  exact (heq (hqpos r hrr)).symm.trans (congrArg φ (hqnorm r hrr))


lemma line_transverse_continuous {d : ℕ} (j : Fin d) :
    Continuous (fun z : ACL.Transverse j => ACL.line j z 0) := by
  exact (PiLp.continuous_toLp 2 _).comp
    ((ExpandedFA.Sobolev.Lines.coordinateLines_continuous j).comp
      (continuous_id.prodMk continuous_const))

set_option maxHeartbeats 1000000 in
/-- The antitone radial representative of a whole-space Sobolev function is
locally absolutely continuous at every positive radius. -/
lemma radial_profile_locallyAC {d : ℕ} (hd : 0 < d) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : Polarization.WholeSobolev d p) {φ : ℝ → ℝ}
    (hφ : AntitoneOn φ (Ioi 0))
    (he : sobolevUnderlying g =ᵐ[volume] (fun x => φ ‖x‖)) :
    ACL.LocallyAC φ (Ioi 0) := by
  let j : Fin d := ⟨0, hd⟩
  obtain ⟨F, huF, hF⟩ := (acl_characterization d hd ℝ (⊤ : Opens (Space d)) j
    (sobolevUnderlying g) (firstWeakDerivative g j)
    (domainLp_locallyIntegrable _ p _) (domainLp_locallyIntegrable _ p _)).mp
    (sobolev_derivative_distribution _ 1 p g (firstSobolevIndex j))
  have huf : sobolevUnderlying g =ᵐ[volume] F := by simpa using huF
  have heF : (fun x => φ ‖x‖) =ᵐ[volume.restrict ((⊤ : Opens (Space d)) : Set (Space d))] F := by
    simpa using he.symm.trans huf
  have hline := ACL.ae_on_fibers (Ω := (⊤ : Opens (Space d))) j heF
  have hgood : ∀ᵐ z : ACL.Transverse j ∂volume,
      ACL.LocallyAC (fun t => F (ACL.line j z t)) univ ∧
      (fun t => φ ‖ACL.line j z t‖) =ᵐ[volume] (fun t => F (ACL.line j z t)) := by
    filter_upwards [hF, hline] with z hz hez
    constructor
    · simpa [ACL.fiber] using hz.1
    · change ∀ᵐ t ∂volume, φ ‖ACL.line j z t‖ = F (ACL.line j z t)
      simpa [ACL.fiber] using hez
  have hseg : ∀ a b : ℝ, 0 < a → a ≤ b → AbsolutelyContinuousOnInterval φ a b := by
    intro a b ha hab
    let U : Set (ACL.Transverse j) := {z | ‖ACL.line j z 0‖ < a}
    have hU : IsOpen U := isOpen_lt (line_transverse_continuous j).norm continuous_const
    have hz0 : (0 : ACL.Transverse j) ∈ U := by
      have he0 : ACL.line j (0 : ACL.Transverse j) 0 = 0 := by
        ext k
        simp [ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine]
      simpa [U, he0] using ha
    obtain ⟨z, hzU, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (hU.measure_ne_zero volume ⟨0, hz0⟩) (ae_restrict_of_ae hgood)
    exact radial_profile_AC_of_line j z hφ hz.1 hz.2 ha hab hzU
  intro a b hab
  have ha : 0 < a := hab (left_mem_uIcc)
  have hb : 0 < b := hab (right_mem_uIcc)
  rcases le_total a b with h | h
  · exact hseg a b ha h
  · exact (hseg b a hb h).symm


/-- A continuous radial representative of a function supported in a centered
open ball vanishes at its boundary radius (and everywhere beyond it). -/
lemma radial_profile_zero_on_Ici {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    {g : Space d → ℝ} {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Ioi (0 : ℝ)))
    (hrep : g =ᵐ[volume] (fun x => φ ‖x‖))
    (hzero : ∀ᵐ x ∂volume, x ∉ Metric.ball (0 : Space d) R → g x = 0) :
    EqOn φ 0 (Ici R) := by
  let U : Set (Space d) := {x | R < ‖x‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hc : ContinuousOn (fun x : Space d => φ ‖x‖) U :=
    hφ.comp continuous_norm.continuousOn (fun x hx => hR.trans hx)
  have hae : (fun x : Space d => φ ‖x‖) =ᵐ[volume.restrict U] 0 := by
    filter_upwards [hrep.filter_mono (ae_restrict_le (s := U)),
      hzero.filter_mono (ae_restrict_le (s := U)), ae_restrict_mem hU.measurableSet]
      with x hx hxzero hxU
    exact hx.symm.trans (hxzero (by
      intro hxball
      have hxball' : ‖x‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hxball
      exact (not_lt_of_ge hxU.le) hxball'))
  have heq : EqOn (fun x : Space d => φ ‖x‖) 0 U :=
    Measure.eqOn_open_of_ae_eq hae hU hc continuousOn_const
  have hφzero : EqOn φ 0 (Ioi R) := by
    intro r hr
    let : NeZero d := ⟨by omega⟩
    obtain ⟨x, hx⟩ := exists_norm_eq (Space d) (hR.trans hr).le
    have hxU : x ∈ U := by change R < ‖x‖; rwa [hx]
    simpa [hx] using heq hxU
  apply hφzero.of_subset_closure
  · exact hφ.mono (fun r hr => hR.trans_le hr)
  · exact continuousOn_const
  · exact Ioi_subset_Ici_self
  · rw [closure_Ioi]

lemma radial_profile_boundary_zero {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    {g : Space d → ℝ} {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Ioi (0 : ℝ)))
    (hrep : g =ᵐ[volume] (fun x => φ ‖x‖))
    (hzero : ∀ᵐ x ∂volume, x ∉ Metric.ball (0 : Space d) R → g x = 0) :
    φ R = 0 :=
  radial_profile_zero_on_Ici hd hR hφ hrep hzero (by simp)


/-- Exact logarithmic Dirichlet-energy identity for a.e. differentiable profiles. -/
lemma logarithmic_profile_energy {d : ℕ} (hd : 2 ≤ d) {R : ℝ}
    (hR : 0 < R) (φ : ℝ → ℝ)
    (hφ : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), DifferentiableAt ℝ φ r) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
      (|Moser.slope (fun t => profileScale d * φ (logarithmicRadius d R t)) t| ^ d)) =
      ENNReal.ofReal (sphereArea d) *
        ∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal (r ^ (d - 1)) * ENNReal.ofReal (|deriv φ r| ^ d) := by
  rw [← logarithmic_energy_lintegral hd hR (fun r => ENNReal.ofReal (|deriv φ r| ^ d))]
  apply lintegral_congr_ae
  filter_upwards [logarithmic_profile_hasDerivAt_ae hd hR φ hφ] with t ht
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hk : 0 ≤ profileScale d / d * logarithmicRadius d R t :=
    mul_nonneg (div_nonneg (profileScale_pos hd).le hd0.le) (logarithmicRadius_pos hR t).le
  dsimp only [Moser.slope]
  rw [ht.deriv, abs_mul, abs_neg, abs_of_nonneg hk, mul_pow,
    ENNReal.ofReal_mul (pow_nonneg hk _)]

/-- Positive-radius local AC and the radial energy bound imply exactly the
hypotheses of the supplied one-dimensional estimate after normalization. -/
lemma logarithmic_profile_admissible {d : ℕ} (hd : 2 ≤ d) {R : ℝ}
    (hR : 0 < R) (φ : ℝ → ℝ) (hφ : ACL.LocallyAC φ (Ioi 0))
    (hnn : ∀ r > 0, 0 ≤ φ r) (hz : φ R = 0)
    (henergy : ENNReal.ofReal (sphereArea d) *
      (∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal (r ^ (d - 1)) * ENNReal.ofReal (|deriv φ r| ^ d)) ≤ 1) :
    Moser.Admissible d (fun t => profileScale d * φ (logarithmicRadius d R t)) := by
  refine ⟨logarithmic_profile_locallyAC hd hR hφ, ?_, ?_, ?_⟩
  · intro t _
    exact mul_nonneg (profileScale_pos hd).le (hnn _ (logarithmicRadius_pos hR t))
  · rw [logarithmicRadius_zero, hz, mul_zero]
  · rw [logarithmic_profile_energy hd hR φ]
    · exact henergy
    · apply locallyAC_ae_differentiableAt_Ioo
      intro a b ha hab
      apply hφ
      rw [uIcc_of_le hab.le]
      exact fun r hr => ha.trans_le hr.1


lemma exists_measurable_profile {φ : ℝ → ℝ} (hφ : ACL.LocallyAC φ (Ioi 0)) :
    ∃ ψ : ℝ → ℝ, Measurable ψ ∧ ∀ r > 0, ψ r = φ r := by
  classical
  refine ⟨(Ioi 0).indicator φ, ?_, ?_⟩
  · have hc : ContinuousOn φ (Ioi 0) :=
      ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn.continuousOn hφ isOpen_Ioi
    exact hc.measurable_piecewise continuous_const.continuousOn measurableSet_Ioi
  · intro r hr
    exact indicator_of_mem hr _


lemma radial_profile_congr_ae {d : ℕ} (hd : 0 < d)
    {f : Space d → ℝ} {φ ψ : ℝ → ℝ}
    (hf : f =ᵐ[volume] fun x => φ ‖x‖)
    (he : ∀ r > 0, ψ r = φ r) :
    f =ᵐ[volume] fun x => ψ ‖x‖ := by
  let : NeZero d := ⟨hd.ne'⟩
  have hn : ∀ᵐ x : Space d ∂volume, x ≠ 0 := by
    apply ae_iff.mpr
    simp
  filter_upwards [hf, hn] with x hx hx0
  rw [hx, he ‖x‖ (norm_pos_iff.mpr hx0)]

lemma locallyAC_congr_on_positive {φ ψ : ℝ → ℝ}
    (hφ : ACL.LocallyAC φ (Ioi 0)) (he : ∀ r > 0, ψ r = φ r) :
    ACL.LocallyAC ψ (Ioi 0) := by
  intro a b hab
  exact (hφ a b hab).congr (fun r hr => (he r (hab hr)).symm)

lemma exists_measurable_radial_profile {φ : ℝ → ℝ}
    (hac : ACL.LocallyAC φ (Ioi 0)) (hanti : AntitoneOn φ (Ioi 0))
    (hnn : ∀ r > 0, 0 ≤ φ r) :
    ∃ ψ : ℝ → ℝ, Measurable ψ ∧ (∀ r > 0, ψ r = φ r) ∧
      AntitoneOn ψ (Ioi 0) ∧ (∀ r > 0, 0 ≤ ψ r) ∧
      ACL.LocallyAC ψ (Ioi 0) := by
  obtain ⟨ψ, hm, he⟩ := exists_measurable_profile hac
  refine ⟨ψ, hm, he, ?_, ?_, locallyAC_congr_on_positive hac he⟩
  · intro a ha b hb hab
    rw [he a ha, he b hb]
    exact hanti ha hb hab
  · intro r hr
    rw [he r hr]
    exact hnn r hr


lemma weakGradient_aestronglyMeasurable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω 1 p) :
    AEStronglyMeasurable (weakGradient u) (volume.restrict (Ω : Set (Space d))) := by
  have hpi : AEMeasurable (fun x => fun j : Fin d => firstWeakDerivative u j x)
      (volume.restrict (Ω : Set (Space d))) :=
    aemeasurable_pi_iff.mpr fun j => (Lp.aestronglyMeasurable (firstWeakDerivative u j)).aemeasurable
  exact ((PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable hpi).aestronglyMeasurable

lemma radial_energy_le_of_gradient_norm {d : ℕ} (hd : 0 < d)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : Polarization.WholeSobolev d p)
    (φ : ℝ → ℝ) (R : ℝ)
    (hgrad : ∀ᵐ x ∂volume, ‖Polarization.gradient g x‖ = |deriv φ ‖x‖|)
    (hbound : eLpNorm (Polarization.gradient g) (d : ℝ≥0∞) volume ≤ 1) :
    ENNReal.ofReal (sphereArea d) *
      (∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal (r ^ (d - 1)) * ENNReal.ofReal (|deriv φ r| ^ d)) ≤ 1 := by
  have hm : AEStronglyMeasurable (Polarization.gradient g) volume := by
    change AEStronglyMeasurable (weakGradient g) volume
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      weakGradient_aestronglyMeasurable (⊤ : Opens (Space d)) p g
  have hr := radial_ball_lintegral hd R (fun r => ENNReal.ofReal (|deriv φ r| ^ d))
    (by fun_prop)
  calc
    _ = ∫⁻ x in Metric.ball (0 : Space d) R, ENNReal.ofReal (‖Polarization.gradient g x‖ ^ d) := by
      rw [← hr]
      apply lintegral_congr_ae
      filter_upwards [hgrad.filter_mono (ae_restrict_le (s := Metric.ball (0 : Space d) R))] with x hx
      rw [hx]
    _ ≤ ∫⁻ x, ENNReal.ofReal (‖Polarization.gradient g x‖ ^ d) := setLIntegral_le_lintegral _ _
    _ ≤ 1 := naturalEnergy_le_one hd hm hbound

/-- All remaining steps of the sharp estimate once the actual radial profile
and its weak-gradient identity have been obtained. The constant is uniform
in the scalar field, domain, radius and function. -/
lemma exponential_bound_from_radial_data {d : ℕ} (hd : 2 ≤ d)
    [Fact (1 ≤ (d : ℝ≥0∞))] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
        (u : SobolevZero 𝕜 Ω 1 (d : ℝ≥0∞))
        (R : ℝ), 0 < R → ∀ (g : Polarization.WholeSobolev d (d : ℝ≥0∞)) (φ : ℝ → ℝ),
        Rearrangement.IsRearrangement
          (fun x => ‖sobolevUnderlying (sobolevZeroExtensionLI Ω 1 (d : ℝ≥0∞) u) x‖)
          (sobolevUnderlying g) →
        (∀ᵐ x ∂volume, x ∉ Metric.ball (0 : Space d) R → sobolevUnderlying g x = 0) →
        volume (Metric.ball (0 : Space d) R) = volume (Ω : Set (Space d)) →
        Measurable φ → (∀ r > 0, 0 ≤ φ r) → ACL.LocallyAC φ (Ioi 0) →
        sobolevUnderlying g =ᵐ[volume] (fun x => φ ‖x‖) →
        (∀ᵐ x ∂volume, ‖Polarization.gradient g x‖ = |deriv φ ‖x‖|) →
        eLpNorm (Polarization.gradient g) (d : ℝ≥0∞) volume ≤ 1 →
        (∫⁻ x in (Ω : Set (Space d)), ENNReal.ofReal (Real.exp
          (sharpCoefficient d * ‖sobolevUnderlying u.val x‖ ^ criticalPower d))) ≤
            ENNReal.ofReal C * volume (Ω : Set (Space d)) := by
  obtain ⟨C, hC, hball⟩ := radial_exponential_bound_of_admissible hd
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ Ω u R hR g φ hre hzero hvol hm hnn hac hrep hgrad hbound
  have hcont : ContinuousOn φ (Ioi (0 : ℝ)) :=
    ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn.continuousOn hac isOpen_Ioi
  have hz := radial_profile_boundary_zero (by omega : 0 < d) hR hcont hrep hzero
  have henergy := radial_energy_le_of_gradient_norm (by omega : 0 < d)
    (d : ℝ≥0∞) g φ R hgrad hbound
  have hadm := logarithmic_profile_admissible hd hR φ hac hnn hz henergy
  rw [exponential_integral_eq_radial_profile hd Ω (d : ℝ≥0∞) u g φ hre hzero hvol hrep]
  simpa only [hvol] using hball R hR φ hm hnn hadm

lemma ae_radial_of_ae_Ioi {d : ℕ} (hd : 0 < d) {P : ℝ → Prop}
    (hP : MeasurableSet {r | P r}) (hae : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), P r) :
    ∀ᵐ x : Space d ∂volume, P ‖x‖ := by
  let B : Set ℝ := {r | ¬ P r}
  have hB : MeasurableSet B := hP.compl
  let F : ℝ → ℝ≥0∞ := B.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hB
  have hz : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) * F r = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hae] with r hr
    simp [F, B, hr]
  have hzi : ∫⁻ x : Space d, F ‖x‖ = 0 := by rw [radial_lintegral hd F hF, hz, mul_zero]
  have he := (lintegral_eq_zero_iff (hF.comp continuous_norm.measurable)).mp hzi
  filter_upwards [he] with x hx
  by_contra hbad
  simp [F, B, hbad] at hx

lemma radial_ae_differentiableAt {d : ℕ} (hd : 0 < d) {φ : ℝ → ℝ}
    (hφ : ∀ a b : ℝ, 0 < a → a < b → AbsolutelyContinuousOnInterval φ a b) :
    ∀ᵐ x : Space d ∂volume, DifferentiableAt ℝ φ ‖x‖ :=
  ae_radial_of_ae_Ioi hd (measurableSet_of_differentiableAt ℝ φ)
    (locallyAC_ae_differentiableAt_Ioi φ hφ)


lemma ae_eq_of_ae_eq_lines {d : ℕ} (j : Fin d) {f h : Space d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hh : AEStronglyMeasurable h volume)
    (he : ∀ᵐ z : ACL.Transverse j ∂volume,
      (fun t => f (ACL.line j z t)) =ᵐ[volume] (fun t => h (ACL.line j z t))) :
    f =ᵐ[volume] h := by
  let e : ACL.Transverse j × ℝ ≃ᵐ Space d :=
    (MeasurableEquiv.prodComm).trans
      ((ExpandedFA.Sobolev.Lines.coordinateEquiv j).symm.trans (MeasurableEquiv.toLp 2 _))
  have heline (z : ACL.Transverse j) (t : ℝ) : e (z, t) = ACL.line j z t := by
    change WithLp.toLp 2 ((ExpandedFA.Sobolev.Lines.coordinateEquiv j).symm (t, z)) = _
    rw [ExpandedFA.Sobolev.Lines.coordinateEquiv_symm_apply]
    rfl
  have hmp : MeasurePreserving e (volume.prod volume) volume := by
    exact (PiLp.volume_preserving_toLp (Fin d)).comp
      (((ExpandedFA.Sobolev.Lines.coordinateEquiv_measurePreserving j).symm
        (ExpandedFA.Sobolev.Lines.coordinateEquiv j)).comp Measure.measurePreserving_swap)
  have hprod : (f ∘ e) =ᵐ[volume.prod volume] (h ∘ e) := by
    apply ACL.Forward.ae_eq_prod_of_slices
      (hf.comp_measurePreserving hmp) (hh.comp_measurePreserving hmp)
    simpa only [Function.comp_apply, heline] using he
  have hp := (hmp.symm e).quasiMeasurePreserving.ae hprod
  change ∀ᵐ x ∂volume, f x = h x
  simpa only [Function.comp_apply, e.apply_symm_apply] using hp


lemma line_norm_hasDerivAt {d : ℕ} (j : Fin d) (z : ACL.Transverse j) (t : ℝ)
    (hx : ACL.line j z t ≠ 0) :
    HasDerivAt (fun s => ‖ACL.line j z s‖)
      ((ACL.line j z t) j / ‖ACL.line j z t‖) t := by
  have hn : ‖ACL.line j z t‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (ACL.line_hasDerivAt j z t).norm_sq.sqrt (pow_ne_zero 2 hn)
  have he : (fun s => Real.sqrt (‖ACL.line j z s‖ ^ 2)) =
      (fun s => ‖ACL.line j z s‖) := by
    funext s
    exact Real.sqrt_sq (norm_nonneg _)
  rw [he] at h
  convert h using 1
  simp [Real.sqrt_sq, norm_nonneg, coordinateVector, EuclideanSpace.inner_single_right]
  ring

set_option maxHeartbeats 1000000 in
lemma radial_firstWeakDerivative {d : ℕ} (hd : 0 < d) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : Polarization.WholeSobolev d p) {φ : ℝ → ℝ}
    (hφ : ACL.LocallyAC φ (Ioi 0))
    (he : sobolevUnderlying g =ᵐ[volume] (fun x => φ ‖x‖)) (j : Fin d) :
    firstWeakDerivative g j =ᵐ[volume]
      (fun x => deriv φ ‖x‖ * (x j / ‖x‖)) := by
  let : NeZero d := ⟨hd.ne'⟩
  have hΦcont : ContinuousOn φ (Ioi 0) :=
    ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn.continuousOn hφ isOpen_Ioi
  have hdiff : ∀ᵐ x : Space d ∂volume, DifferentiableAt ℝ φ ‖x‖ :=
    radial_ae_differentiableAt hd (fun a b ha hab => hφ a b (by
      rw [uIcc_of_le hab.le]; intro r hr; exact ha.trans_le hr.1))
  have hnonzero : ∀ᵐ x : Space d ∂volume, x ≠ 0 := by
    simp [ae_iff]
  obtain ⟨F, huF, hF⟩ := (acl_characterization d hd ℝ (⊤ : Opens (Space d)) j
    (sobolevUnderlying g) (firstWeakDerivative g j)
    (domainLp_locallyIntegrable _ p _) (domainLp_locallyIntegrable _ p _)).mp
    (sobolev_derivative_distribution _ 1 p g (firstSobolevIndex j))
  have huf : sobolevUnderlying g =ᵐ[volume] F := by simpa using huF
  have heF : (fun x => φ ‖x‖) =ᵐ[volume.restrict ((⊤ : Opens (Space d)) : Set (Space d))] F := by
    simpa using he.symm.trans huf
  have hline := ACL.ae_on_fibers (Ω := (⊤ : Opens (Space d))) j heF
  have hdiffline := ACL.ae_on_fibers (Ω := (⊤ : Opens (Space d))) j (by simpa using hdiff)
  have hnzline := ACL.ae_on_fibers (Ω := (⊤ : Opens (Space d))) j (by simpa using hnonzero)
  apply ae_eq_of_ae_eq_lines j
  · simpa using (Lp.aestronglyMeasurable (firstWeakDerivative g j))
  · exact (((measurable_deriv φ).comp continuous_norm.measurable).mul
      (((PiLp.continuous_apply 2 _ j).measurable).div continuous_norm.measurable)).aestronglyMeasurable
  filter_upwards [hF, hline, hdiffline, hnzline] with z hz hez hdz hnz
  have hzAC : ACL.LocallyAC (fun t => F (ACL.line j z t)) univ := by simpa [ACL.fiber] using hz.1
  have hzcont : Continuous (fun t => F (ACL.line j z t)) :=
    continuousOn_univ.mp (ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn.continuousOn
      hzAC isOpen_univ)
  have hez' : (fun t => φ ‖ACL.line j z t‖) =ᵐ[volume] (fun t => F (ACL.line j z t)) := by
    change ∀ᵐ t ∂volume, φ ‖ACL.line j z t‖ = F (ACL.line j z t)
    simpa [ACL.fiber] using hez
  have hdz' : ∀ᵐ t ∂volume, DifferentiableAt ℝ φ ‖ACL.line j z t‖ := by
    simpa [ACL.fiber] using hdz
  have hnz' : ∀ᵐ t ∂volume, ACL.line j z t ≠ 0 := by simpa [ACL.fiber] using hnz
  have hz' : ∀ᵐ t ∂volume, HasDerivAt (fun s => F (ACL.line j z s))
      (firstWeakDerivative g j (ACL.line j z t)) t := by simpa [ACL.fiber] using hz.2
  let U : Set ℝ := {t | ACL.line j z t ≠ 0}
  have hU : IsOpen U := by
    change IsOpen ((ACL.line j z) ⁻¹' ({(0 : Space d)}ᶜ))
    exact (isClosed_singleton : IsClosed {(0 : Space d)}).isOpen_compl.preimage (ACL.line_contDiff j z).continuous
  have hcRad : ContinuousOn (fun t => φ ‖ACL.line j z t‖) U :=
    hΦcont.comp ((ACL.line_contDiff j z).continuous.norm.continuousOn)
      (fun t ht => norm_pos_iff.mpr ht)
  have heq : EqOn (fun t => φ ‖ACL.line j z t‖) (fun t => F (ACL.line j z t)) U :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hez') hU hcRad hzcont.continuousOn
  filter_upwards [hz', hdz', hnz'] with t ht hdt hnt
  have hdRad := hdt.hasDerivAt.comp t (line_norm_hasDerivAt j z t hnt)
  have hevent : (fun s => φ ‖ACL.line j z s‖) =ᶠ[𝓝 t] (fun s => F (ACL.line j z s)) := by
    filter_upwards [hU.mem_nhds hnt] with s hs
    exact heq hs
  exact (ht.congr_of_eventuallyEq hevent).unique hdRad


lemma radial_gradient_norm {d : ℕ} (hd : 0 < d) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : Polarization.WholeSobolev d p) {φ : ℝ → ℝ}
    (hφ : ACL.LocallyAC φ (Ioi 0))
    (he : sobolevUnderlying g =ᵐ[volume] (fun x => φ ‖x‖)) :
    ∀ᵐ x : Space d ∂volume, ‖Polarization.gradient g x‖ = |deriv φ ‖x‖| := by
  let : NeZero d := ⟨hd.ne'⟩
  have hj (j : Fin d) := radial_firstWeakDerivative hd p g hφ he j
  have hnonzero : ∀ᵐ x : Space d ∂volume, x ≠ 0 := by
    simp [ae_iff]
  filter_upwards [ae_all_iff.mpr hj, hnonzero] with x hx hx0
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  have hgrad : Polarization.gradient g x = (deriv φ ‖x‖ / ‖x‖) • x := by
    apply PiLp.ext
    intro j
    change firstWeakDerivative g j x = (deriv φ ‖x‖ / ‖x‖) * x j
    rw [hx j]
    ring
  rw [hgrad, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg _),
    div_mul_cancel₀ _ hn]

end P102.Sobolev.TrudingerMoser

namespace P102.Sobolev
open P102.U4 TrudingerMoser

/-- Conditional derivation of the full sharp upper bound. The three pending
rearrangement interfaces remain explicit, in their frozen order. -/
theorem trudinger_moser_bound_conditional
    (hExists : PolyaSzegoExpected.Existence)
    (hRadial : PolyaSzegoExpected.RadialCharacterization)
    (hUnique : PolyaSzegoExpected.Uniqueness) : TrudingerMoserExpected.Bound := by
  intro d hd
  let : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
  obtain ⟨C, hC, hbound⟩ := exponential_bound_from_radial_data hd
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ Ω hne hb u hu
  have hd0 : 0 < d := by omega
  obtain ⟨R, hR, hvol, g, _hgs, hre, hrad, hzero, hgrad, _huniq⟩ :=
    rearrangement_reduction_equivolume_conditional hExists hRadial hUnique hd0 Ω hne hb
      (d : ℝ≥0∞) (by exact_mod_cast (by omega : 1 < d)) (by simp) u
  obtain ⟨φ, hanti, hnn, he⟩ := hrad
  have hac := radial_profile_locallyAC hd0 (d : ℝ≥0∞) g hanti he
  obtain ⟨ψ, hmψ, heψ, _hantiψ, hnnψ, hacψ⟩ :=
    exists_measurable_radial_profile hac hanti hnn
  have hrep := radial_profile_congr_ae hd0 he heψ
  exact hbound 𝕜 Ω u R hR g ψ hre hzero hvol hmψ hnnψ hacψ hrep
    (radial_gradient_norm hd0 (d : ℝ≥0∞) g hacψ hrep) (hgrad.trans hu)

end P102.Sobolev

theorem _root_.«P102».«Sobolev».«trudinger_moser_bound» : _root_.«P102».«Sobolev».«TrudingerMoserExpected».«Bound» :=
  @_root_.«P102».«Sobolev».«trudinger_moser_bound_conditional» (@_root_.«P102».«Sobolev».«polya_szego») (@_root_.«P102».«Sobolev».«rearrangement_radial_characterization») (@_root_.«P102».«Sobolev».«rearrangement_unique»)
