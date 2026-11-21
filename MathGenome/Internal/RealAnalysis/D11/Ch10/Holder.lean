import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.Holder
import MathGenome.Internal.RealAnalysis.D11.Ch10.LpDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Hölder for the shared raw spaces, on arbitrary positive measure spaces. -/
open Set MeasureTheory
open scoped ENNReal NNReal
universe u
noncomputable section
namespace D11.Ch10.Holder
open LpDefinition
open D11.Ch04.EssentialBounds D11.Ch04.AeCommonException
open D11.Ch05.NonnegativeIntegral D11.Ch06.ScalarIntegral

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
private theorem norm_power_integral (μ : Measure X) (p : ℝ) (f : X → 𝕜)
    (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) =
      nonnegativeIntegral μ (fun x => ENNReal.ofReal (‖f x‖ ^ p)) := by
  rw [integral_eq_lintegral]
  congr 1
  funext x
  exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hp

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
private theorem product_integral (μ : Measure X) (f g : X → 𝕜) :
    (∫⁻ x, ENNReal.ofReal ‖f x‖ * ENNReal.ofReal ‖g x‖ ∂μ) =
      nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x * g x‖) := by
  rw [integral_eq_lintegral]
  congr 1
  funext x
  rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]

theorem holder_finite : Specs.D11.Ch10.Holder.holder_finite := by
  intro X 𝕜 _ _ _ _ μ p q f g hpq hf hg
  change f ∈ rawLp μ p at hf
  change g ∈ rawLp μ q at hg
  have hle : nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x * g x‖) ≤
      powerNorm μ p f * powerNorm μ q g := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
      (hf.1.norm.ennreal_ofReal.aemeasurable) (hg.1.norm.ennreal_ofReal.aemeasurable)
    simpa only [Pi.mul_apply, norm_power_integral μ p f hpq.nonneg,
      norm_power_integral μ q g hpq.symm.nonneg, product_integral, powerNorm] using h
  refine ⟨⟨hf.1.mul hg.1, hle.trans_lt (ENNReal.mul_lt_top hf.2 hg.2)⟩, hle⟩

theorem holder_one_top : Specs.D11.Ch10.Holder.holder_one_top := by
  intro X 𝕜 _ _ _ _ μ f g hf hg
  change f ∈ rawLp μ 1 at hf
  change g ∈ rawLInfinity μ at hg
  have hb : ∀ᵐ x ∂μ, ENNReal.ofReal ‖g x‖ ≤ essentialSupNorm μ g := by
    have ha := (almostEverywhere_iff_native μ _).mp (infinity_norm_attained μ g hg)
    filter_upwards [ha] with x hx
    exact (ENNReal.ofReal_le_ofReal hx).trans_eq (ENNReal.ofReal_toReal hg.2.ne)
  have hle : nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x * g x‖) ≤
      powerNorm μ 1 f * essentialSupNorm μ g := by
    rw [← product_integral]
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal ‖f x‖ * essentialSupNorm μ g ∂μ :=
        lintegral_mono_ae (hb.mono (fun x hx => mul_le_mul' le_rfl hx))
      _ = (∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ) * essentialSupNorm μ g :=
        lintegral_mul_const _ hf.1.norm.ennreal_ofReal
      _ = powerNorm μ 1 f * essentialSupNorm μ g := by
        simp only [powerNorm, integral_eq_lintegral, Real.rpow_one, one_div, inv_one,
          ENNReal.rpow_one]
  exact ⟨⟨hf.1.mul hg.1, hle.trans_lt (ENNReal.mul_lt_top hf.2 hg.2)⟩, hle⟩

theorem holder_top_one : Specs.D11.Ch10.Holder.holder_top_one := by
  intro X 𝕜 _ _ _ _ μ f g hf hg
  simpa only [mul_comm] using holder_one_top μ g f hg hf

theorem zero_finite : Specs.D11.Ch10.Holder.zero_finite := by
  intro X 𝕜 _ _ _ _ μ p q f g hpq hf hg hz
  have h := (holder_finite μ p q f g hpq hf hg).2
  rcases hz with hz | hz <;> simp only [hz, zero_mul, mul_zero] at * <;> exact le_antisymm h bot_le

theorem zero_one_top : Specs.D11.Ch10.Holder.zero_one_top := by
  intro X 𝕜 _ _ _ _ μ f g hf hg hz
  have h := (holder_one_top μ f g hf hg).2
  rcases hz with hz | hz <;> simp only [hz, zero_mul, mul_zero] at * <;> exact le_antisymm h bot_le

theorem zero_top_one : Specs.D11.Ch10.Holder.zero_top_one := by
  intro X 𝕜 _ _ _ _ μ f g hf hg hz
  have h := (holder_top_one μ f g hf hg).2
  rcases hz with hz | hz <;> simp only [hz, zero_mul, mul_zero] at * <;> exact le_antisymm h bot_le

/-- Equal normalized nonnegative densities are precisely positive finite
constant multiples. The reverse direction also identifies their integrals. -/
theorem normalized_integrands_iff (μ : Measure X) (F G : X → ℝ≥0∞)
    (hG : Measurable G)
    (hA0 : (∫⁻ x, F x ∂μ) ≠ 0) (hAt : (∫⁻ x, F x ∂μ) ≠ ∞)
    (hB0 : (∫⁻ x, G x ∂μ) ≠ 0) (hBt : (∫⁻ x, G x ∂μ) ≠ ∞) :
    ((fun x => (∫⁻ y, F y ∂μ)⁻¹ * F x) =ᵐ[μ]
      (fun x => (∫⁻ y, G y ∂μ)⁻¹ * G x)) ↔
      ∃ c : ℝ, 0 < c ∧ F =ᵐ[μ] (fun x => ENNReal.ofReal c * G x) := by
  let A := ∫⁻ x, F x ∂μ
  let B := ∫⁻ x, G x ∂μ
  constructor
  · intro h
    let C := A * B⁻¹
    have hC0 : C ≠ 0 := mul_ne_zero hA0 (ENNReal.inv_ne_zero.mpr hBt)
    have hCt : C ≠ ∞ := ENNReal.mul_ne_top hAt (ENNReal.inv_ne_top.mpr hB0)
    refine ⟨C.toReal, ENNReal.toReal_pos hC0 hCt, ?_⟩
    rw [ENNReal.ofReal_toReal hCt]
    filter_upwards [h] with x hx
    calc
      F x = A * (A⁻¹ * F x) := (ENNReal.mul_inv_cancel_left hA0 hAt).symm
      _ = A * (B⁻¹ * G x) := congrArg (fun t => A * t) hx
      _ = C * G x := (mul_assoc _ _ _).symm
  · rintro ⟨c, hc, h⟩
    have hC0 : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc
    have hAB : A = ENNReal.ofReal c * B :=
      (lintegral_congr_ae h).trans (lintegral_const_mul _ hG)
    filter_upwards [h] with x hx
    change A⁻¹ * F x = B⁻¹ * G x
    rw [hx, hAB, ENNReal.mul_inv (Or.inl hC0) (Or.inl ENNReal.ofReal_ne_top)]
    calc
      (ENNReal.ofReal c)⁻¹ * B⁻¹ * (ENNReal.ofReal c * G x) =
          ((ENNReal.ofReal c)⁻¹ * ENNReal.ofReal c) * (B⁻¹ * G x) := by ac_rfl
      _ = B⁻¹ * G x := by rw [ENNReal.inv_mul_cancel hC0 ENNReal.ofReal_ne_top, one_mul]

theorem equality_iff : Specs.D11.Ch10.Holder.equality_iff := by
  intro X 𝕜 _ _ _ _ μ p q f g hpq hf hg hf0 hg0
  change f ∈ rawLp μ p at hf
  change g ∈ rawLp μ q at hg
  change powerNorm μ p f ≠ 0 at hf0
  change powerNorm μ q g ≠ 0 at hg0
  let F : X → ℝ≥0∞ := fun x => ENNReal.ofReal ‖f x‖
  let G : X → ℝ≥0∞ := fun x => ENNReal.ofReal ‖g x‖
  have hF : Measurable F := hf.1.norm.ennreal_ofReal
  have hG : Measurable G := hg.1.norm.ennreal_ofReal
  have hAt : (∫⁻ x, F x ^ p ∂μ) ≠ ∞ := by
    rw [norm_power_integral μ p f hpq.nonneg]
    exact ((rawLp_iff_finite_integral μ p f hpq.lt.le).mp hf).2.ne
  have hBt : (∫⁻ x, G x ^ q ∂μ) ≠ ∞ := by
    rw [norm_power_integral μ q g hpq.symm.nonneg]
    exact ((rawLp_iff_finite_integral μ q g hpq.symm.lt.le).mp hg).2.ne
  have hA0 : (∫⁻ x, F x ^ p ∂μ) ≠ 0 := by
    intro h
    apply hf0
    rw [powerNorm, ← norm_power_integral μ p f hpq.nonneg, h,
      ENNReal.zero_rpow_of_pos hpq.one_div_pos]
  have hB0 : (∫⁻ x, G x ^ q ∂μ) ≠ 0 := by
    intro h
    apply hg0
    rw [powerNorm, ← norm_power_integral μ q g hpq.symm.nonneg, h,
      ENNReal.zero_rpow_of_pos hpq.symm.one_div_pos]
  have heq := ENNReal.lintegral_mul_eq_Lp_mul_Lq_iff_of_ne_zero_of_ne_top
    hpq hF.aemeasurable hG.aemeasurable hAt hBt hA0 hB0
  have hnorm := normalized_integrands_iff μ (fun x => F x ^ p) (fun x => G x ^ q)
    (hG.pow_const q) hA0 hAt hB0 hBt
  change (nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x * g x‖) =
    powerNorm μ p f * powerNorm μ q g ↔ _)
  have heq' : (nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x * g x‖) =
      powerNorm μ p f * powerNorm μ q g) ↔
      ∃ c : ℝ, 0 < c ∧ (fun x => F x ^ p) =ᵐ[μ]
        (fun x => ENNReal.ofReal c * G x ^ q) := by
    simpa only [F, G, Pi.mul_apply, norm_power_integral μ p f hpq.nonneg,
      norm_power_integral μ q g hpq.symm.nonneg, product_integral, powerNorm,
      Pi.smul_apply, smul_eq_mul, Pi.pow_apply] using heq.trans hnorm
  rw [heq']
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, (almostEverywhere_iff_native μ _).mpr ?_⟩
    filter_upwards [h] with x hx
    have hx' := congrArg ENNReal.toReal hx
    simpa only [F, G, ← ENNReal.toReal_rpow, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_ofReal hc.le] using hx'
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    filter_upwards [(almostEverywhere_iff_native μ _).mp h] with x hx
    change (ENNReal.ofReal ‖f x‖) ^ p = ENNReal.ofReal c * (ENNReal.ofReal ‖g x‖) ^ q
    rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.nonneg,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.symm.nonneg,
      ← ENNReal.ofReal_mul hc.le, hx]

end D11.Ch10.Holder
