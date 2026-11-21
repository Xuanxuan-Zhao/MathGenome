import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.TrudingerMoser
import MathGenome.Internal.FourierSobolev.P102.Sobolev.MoserProfiles
import MathGenome.Internal.FourierSobolev.P102.Sobolev.MoserMembership

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace P102.Sobolev
open P102.U4 TrudingerMoser

/-- The sharp endpoint bound, including finiteness of the extended integral. -/
theorem trudinger_moser_upperBound : TrudingerMoserExpected.UpperBound :=
  trudinger_moser_bound

namespace TrudingerMoser

/-- Every positive power is dominated on [0,∞) by a constant times the
critical exponential. The constant may depend on the power and coefficient. -/
lemma power_le_exponential {a k r : ℝ} (ha : 0 < a) (hk : 0 < k) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → x ^ r ≤ C * Real.exp (a * x ^ k) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (r / k)
  have hkn : r ≤ k * n := (div_le_iff₀ hk).mp hn |>.trans_eq (mul_comm _ _)
  let C : ℝ := 1 + (n.factorial : ℝ) / a ^ n
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun x hx => ?_⟩
  by_cases hx1 : x ≤ 1
  · have hxpow : x ^ r ≤ 1 := Real.rpow_le_one hx hx1 hr.le
    have hExp : 1 ≤ Real.exp (a * x ^ k) := Real.one_le_exp (by positivity)
    have hC1 : 1 ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
    exact hxpow.trans (by nlinarith)
  · have hx1' : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
    have hpow : x ^ r ≤ (x ^ k) ^ n := by
      rw [← Real.rpow_mul_natCast hx]
      exact Real.rpow_le_rpow_of_exponent_le hx1' hkn
    have he := Real.pow_div_factorial_le_exp (x := a * x ^ k) (by positivity) n
    have hfac : (0 : ℝ) < n.factorial := by positivity
    have han : 0 < a ^ n := pow_pos ha _
    have he' : (x ^ k) ^ n ≤ (n.factorial : ℝ) / a ^ n * Real.exp (a * x ^ k) := by
      rw [div_le_iff₀ hfac, mul_pow] at he
      rw [div_mul_eq_mul_div, le_div_iff₀ han]
      nlinarith only [he]
    exact hpow.trans (he'.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
      (Real.exp_pos _).le))

end TrudingerMoser
end P102.Sobolev

namespace P102.Sobolev
open P102.U4 TrudingerMoser

/-- Uniform exponential integrability controls every finite positive Lʳ norm,
without assuming r is an integer or r ≥ 1. -/
theorem trudinger_moser_finiteNorms : TrudingerMoserExpected.UniformFiniteNorms := by
  intro d hd
  let : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
  intro Ω hne hb r hr hrfin
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrtop : r ≠ ⊤ := ne_of_lt hrfin
  have hrReal : 0 < r.toReal := ENNReal.toReal_pos hr0 hrtop
  obtain ⟨C, hC, hbound⟩ := trudinger_moser_bound d hd
  obtain ⟨K, hK, hpower⟩ := power_le_exponential (sharpCoefficient_pos hd)
    (criticalPower_pos hd) hrReal
  let A : ℝ≥0∞ := ENNReal.ofReal K * (ENNReal.ofReal C * volume (Ω : Set (Space d)))
  have hA : A < ⊤ := by
    dsimp [A]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb.measure_lt_top)
  refine ⟨A ^ (1 / r.toReal), ENNReal.rpow_lt_top_of_nonneg (by positivity) hA.ne, ?_⟩
  intro u hu
  have hm := (Lp.memLp (sobolevUnderlying u.val)).aestronglyMeasurable
  have hI : (∫⁻ x in (Ω : Set (Space d)), ‖sobolevUnderlying u.val x‖ₑ ^ r.toReal) ≤ A := by
    calc
      _ ≤ ∫⁻ x in (Ω : Set (Space d)), ENNReal.ofReal K *
          ENNReal.ofReal (Real.exp (sharpCoefficient d * ‖sobolevUnderlying u.val x‖ ^ criticalPower d)) := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) r.toReal_nonneg,
          ← ENNReal.ofReal_mul hK.le]
        exact ENNReal.ofReal_le_ofReal (hpower _ (norm_nonneg _))
      _ = ENNReal.ofReal K * exponentialIntegral Ω (sharpCoefficient d) (sobolevUnderlying u.val) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rfl
      _ ≤ A := by
        dsimp [A]
        gcongr
        exact hbound ℝ Ω hne hb u hu
  have hnorm : eLpNorm (sobolevUnderlying u.val) r (volume.restrict (Ω : Set (Space d))) ≤
      A ^ (1 / r.toReal) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrtop hm]
    exact ENNReal.rpow_le_rpow hI (by positivity)
  exact ⟨hnorm.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by positivity) hA.ne), hnorm⟩

end P102.Sobolev

namespace P102.Sobolev
open P102.U4 TrudingerMoser

/-- Concentration at every supercritical coefficient gives the literal infinite
supremum over the gradient unit ball. This lemma does not assume sharpness. -/
theorem trudinger_moser_sharpness_of_concentration
    (hc : TrudingerMoserExpected.Concentration) : TrudingerMoserExpected.Sharpness := by
  intro d hd
  let : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
  intro Ω hne hb α hα
  obtain ⟨c, R, u, hR, hsub, hu, hfinite, hsup, hexp⟩ := hc d hd Ω hne hb
  apply top_unique
  calc
    ⊤ = ⨆ n, exponentialIntegral Ω α (sobolevUnderlying (u n).val) :=
      (iSup_eq_of_forall_le_of_tendsto (fun _ => le_top) (hexp α hα)).symm
    _ ≤ _ := iSup_le fun n =>
      le_iSup₂_of_le (u n) (show eLpNorm (weakGradient (u n).val) (d : ℝ≥0∞)
        (volume.restrict (Ω : Set (Space d))) ≤ 1 from (hu n).2.2.le) le_rfl

namespace TrudingerMoser

/-- Zero extension preserves every underlying Lʳ norm, including r = ∞,
independently of the exponent used to construct the Sobolev class. -/
lemma zeroExtension_underlying_eLpNorm {d : ℕ}
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : SobolevZero ℝ Ω 1 p) (r : ℝ≥0∞) :
    eLpNorm (sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u)) r volume =
      eLpNorm (sobolevUnderlying u.val) r (volume.restrict (Ω : Set (Space d))) := by
  change eLpNorm (lpZeroExtension Ω p (sobolevUnderlying u.val)) r volume = _
  rw [eLpNorm_congr_ae (lpZeroExtension_ae Ω p (sobolevUnderlying u.val))]
  exact eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet.nullMeasurableSet

end TrudingerMoser

/-- Zero-extending the same concentrating sequence supplies the whole-space
endpoint counterexample. Both the gradient and the finite Lʳ norm stay bounded. -/
theorem trudinger_moser_endpointFailure_of_concentration
    (hc : TrudingerMoserExpected.Concentration) : TrudingerMoserExpected.EndpointFailure := by
  intro d hd
  let : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
  intro r hr hrfin
  let Ω : Opens (Space d) := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
  have hne : (Ω : Set (Space d)).Nonempty := ⟨0, by simp [Ω]⟩
  have hb : Bornology.IsBounded (Ω : Set (Space d)) := Metric.isBounded_ball
  obtain ⟨c, R, u, hR, hsub, hu, hfinite, hsup, hexp⟩ := hc d hd Ω hne hb
  obtain ⟨B, hB, hub⟩ := hfinite r (zero_lt_one.trans_le hr) hrfin
  rintro ⟨C, hC⟩
  have hn (n : ℕ) :
      eLpNorm (sobolevUnderlying (u n).val) ⊤ (volume.restrict (Ω : Set (Space d))) ≤
        (C : ℝ≥0∞) * (1 + B) := by
    let v := sobolevZeroExtensionLI Ω 1 (d : ℝ≥0∞) (u n)
    have hvr : MemLp (sobolevUnderlying v) r volume := by
      change eLpNorm (sobolevUnderlying v) r volume < ⊤
      rw [zeroExtension_underlying_eLpNorm]
      exact (hub n).1
    calc
      _ = eLpNorm (sobolevUnderlying v) ⊤ volume :=
        (zeroExtension_underlying_eLpNorm Ω (d : ℝ≥0∞) (u n) ⊤).symm
      _ ≤ C * (eLpNorm (weakGradient v) (d : ℝ≥0∞) volume +
          eLpNorm (sobolevUnderlying v) r volume) := hC v hvr
      _ = C * (1 + eLpNorm (sobolevUnderlying (u n).val) r
          (volume.restrict (Ω : Set (Space d)))) := by
        dsimp only [v]
        rw [zeroExtension_gradient_eLpNorm, (hu n).2.2, zeroExtension_underlying_eLpNorm]
      _ ≤ _ := by gcongr; exact (hub n).2
  have himpossible : (⊤ : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (1 + B) :=
    le_of_tendsto hsup (Eventually.of_forall hn)
  have hfiniteBound : (C : ℝ≥0∞) * (1 + B) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.mpr ⟨by simp, hB⟩)
  exact (not_le_of_gt hfiniteBound) himpossible

end P102.Sobolev

namespace P102.Sobolev
open P102.U4 TrudingerMoser

/-- Assembly of the source family from the two profile
interfaces. Finite Lʳ bounds follow from the proved upper bound. -/
theorem trudinger_moser_concentration_of_profiles
    (hm : TrudingerMoserExpected.ProfileMembership)
    (hg : TrudingerMoserExpected.ProfileDivergence) : TrudingerMoserExpected.Concentration := by
  intro d hd
  let : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
  intro Ω hne hb
  obtain ⟨c, hc⟩ := hne
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds hc)
  have hex (n : ℕ) := hm d hd Ω c R hR hsub ((n : ℝ) + 1) (by positivity)
  choose u hrep hgrad using hex
  obtain ⟨hcont, hsup, hexp⟩ := hg d hd Ω c R hR hsub
  refine ⟨c, R, u, hR, hsub, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨hcont _ (by positivity), hrep n, hgrad n⟩
  · intro r hr hrfin
    obtain ⟨B, hB, hnorm⟩ := trudinger_moser_finiteNorms d hd Ω ⟨c, hc⟩ hb r hr hrfin
    exact ⟨B, hB, fun n => hnorm (u n) (hgrad n).le⟩
  · exact hsup.congr (fun n => (eLpNorm_congr_ae (hrep n)).symm)
  · intro α hα
    apply (hexp α hα).congr
    intro n
    symm
    apply lintegral_congr_ae
    filter_upwards [hrep n] with x hx
    rw [hx]

/-- Sharpness follows from the two profile interfaces. -/
theorem trudinger_moser_sharpness_of_profiles
    (hm : TrudingerMoserExpected.ProfileMembership)
    (hg : TrudingerMoserExpected.ProfileDivergence) : TrudingerMoserExpected.Sharpness :=
  trudinger_moser_sharpness_of_concentration (trudinger_moser_concentration_of_profiles hm hg)

theorem trudinger_moser_endpointFailure_of_profiles
    (hm : TrudingerMoserExpected.ProfileMembership)
    (hg : TrudingerMoserExpected.ProfileDivergence) : TrudingerMoserExpected.EndpointFailure :=
  trudinger_moser_endpointFailure_of_concentration (trudinger_moser_concentration_of_profiles hm hg)

end P102.Sobolev

namespace P102.Sobolev

/-- The explicit profiles concentrate inside every nonempty bounded open set.
They have gradient norm one, bounded finite norms, and divergent supremum norms
and supercritical exponential integrals. -/
theorem trudinger_moser_concentration : TrudingerMoserExpected.Concentration :=
  trudinger_moser_concentration_of_profiles
    moser_profiles_membership moser_profiles_divergence

/-- Every coefficient strictly above the sharp coefficient gives infinite
supremum over the zero-boundary Sobolev gradient unit ball. -/
theorem trudinger_moser_sharpness : TrudingerMoserExpected.Sharpness :=
  trudinger_moser_sharpness_of_concentration trudinger_moser_concentration

/-- The zero-extended concentrating sequence rules out the whole-space
critical Gagliardo–Nirenberg endpoint, for every finite exponent r ≥ 1. -/
theorem trudinger_moser_endpointFailure : TrudingerMoserExpected.EndpointFailure :=
  trudinger_moser_endpointFailure_of_concentration trudinger_moser_concentration

end P102.Sobolev
