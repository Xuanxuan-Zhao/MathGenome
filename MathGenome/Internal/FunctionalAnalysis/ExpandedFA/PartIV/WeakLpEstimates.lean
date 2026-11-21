import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.WeakLpEstimates
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.WeakLpBanach
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ExpandedFA.PartIV

variable {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E]

/-- Hölder on each test set, with the powers of its measure cancelled. -/
theorem weakLpN_le_eLpNorm (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : ℝ) (hp : 1 < p) (f : Ω → E) (hf : AEStronglyMeasurable f μ) :
    weakLpN μ p f ≤ eLpNorm f (ENNReal.ofReal p) μ := by
  refine iSup_le fun A => iSup_le fun hA => iSup_le fun hpos => ?_
  have hp0 : 0 < p := by linarith
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ.restrict A) (f := f)
    (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal p by simpa using ENNReal.ofReal_le_ofReal hp.le) hf.restrict
  rw [eLpNorm_one_eq_lintegral_enorm hf.restrict,
    ENNReal.toReal_one, ENNReal.toReal_ofReal hp0.le,
    Measure.restrict_apply_univ, div_one] at hcompare
  have hcancel : (μ A) ^ (1 / p - 1) * (μ A) ^ (1 - 1 / p) = 1 := by
    rw [← ENNReal.rpow_add _ _ hpos.ne' (measure_ne_top μ A)]
    simp
  calc
    _ ≤ (μ A) ^ (1 / p - 1) *
        (eLpNorm f (ENNReal.ofReal p) (μ.restrict A) * (μ A) ^ (1 - 1 / p)) :=
      mul_le_mul' le_rfl hcompare
    _ = eLpNorm f (ENNReal.ofReal p) (μ.restrict A) := by
      calc
        _ = eLpNorm f (ENNReal.ofReal p) (μ.restrict A) *
            ((μ A) ^ (1 / p - 1) * (μ A) ^ (1 - 1 / p)) := by ac_rfl
        _ = _ := by rw [hcancel, mul_one]
    _ ≤ _ := eLpNorm_mono_measure f Measure.restrict_le_self

/-- Factoring the weight in Nq gives the finite-measure comparison. -/
theorem weakLpN_exponent_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (p q : ℝ) (hq : 1 < q) (hqp : q ≤ p) (f : Ω → E) :
    weakLpN μ q f ≤ (μ univ) ^ (1 / q - 1 / p) * weakLpN μ p f := by
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := hq0.trans_le hqp
  have hdiff : 0 ≤ 1 / q - 1 / p := sub_nonneg.mpr (one_div_le_one_div_of_le hq0 hqp)
  refine iSup_le fun A => iSup_le fun hA => iSup_le fun hpos => ?_
  have he : (μ A) ^ (1 / q - 1) =
      (μ A) ^ (1 / q - 1 / p) * (μ A) ^ (1 / p - 1) := by
    rw [← ENNReal.rpow_add _ _ hpos.ne' (measure_ne_top μ A)]
    congr 1
    ring
  rw [he, mul_assoc]
  exact mul_le_mul'
    (ENNReal.rpow_le_rpow (measure_mono (subset_univ A)) hdiff)
    (weakLpN_test μ p f hA hpos)

theorem weakLp_strongToWeak : WeakLpEstimatesSpec.StrongToWeakStatement :=
  fun μ _ p hp f hf => weakLpN_le_eLpNorm μ p hp f hf

theorem weakLp_weakExponent : WeakLpEstimatesSpec.WeakExponentStatement :=
  fun μ _ p q hq hqp f => weakLpN_exponent_le μ p q hq hqp f

/-- Taking a positive power multiplies the distribution exponent and raises Q
by the same power. The one-sided identity suffices for the sharp estimate. -/
theorem weakLpQ_norm_rpow_le (μ : Measure Ω) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (f : Ω → E) :
    weakLpQ μ (p / q) (fun x => ‖f x‖ ^ q) ≤ weakLpQ μ p f ^ q := by
  refine iSup_le fun t => iSup_le fun ht => ?_
  let s : ℝ := t ^ (1 / q)
  have hs : 0 < s := Real.rpow_pos_of_pos ht _
  have hst : s ^ q = t := by
    dsimp [s]
    rw [one_div, Real.rpow_inv_rpow ht.le hq.ne']
  have hdist : DistributionFunctionsSpec.DistributionValue μ (fun x => ‖f x‖ ^ q) t =
      DistributionFunctionsSpec.DistributionValue μ f s := by
    apply congrArg μ
    ext x
    simp only [mem_ofPred_eq, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← hst]
    exact Real.rpow_lt_rpow_iff hs.le (norm_nonneg _) hq
  change ENNReal.ofReal t *
    DistributionFunctionsSpec.DistributionValue μ (fun x => ‖f x‖ ^ q) t ^ (1 / (p / q)) ≤ _
  rw [hdist]
  calc
    _ = (ENNReal.ofReal s * DistributionFunctionsSpec.DistributionValue μ f s ^ (1 / p)) ^ q := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul,
        ENNReal.ofReal_rpow_of_nonneg hs.le hq.le, hst]
      congr 2
      field_simp
    _ ≤ _ := ENNReal.rpow_le_rpow
      (show ENNReal.ofReal s * DistributionFunctionsSpec.DistributionValue μ f s ^ (1 / p) ≤
        weakLpQ μ p f from le_iSup_of_le s (le_iSup_of_le hs le_rfl)) hq.le

/-- Integral form of the sharp weak-to-strong estimate. -/
theorem lintegral_rpow_enorm_le_weakLpQ (μ : Measure Ω) [IsFiniteMeasure μ]
    (p q : ℝ) (hq : 0 < q) (hqp : q < p) (f : Ω → E)
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ ^ q ∂μ) ≤
      ENNReal.ofReal (p / (p - q)) * (μ univ) ^ (1 - q / p) * weakLpQ μ p f ^ q := by
  have hp : 0 < p := hq.trans hqp
  have ha : 1 < p / q := (one_lt_div hq).mpr hqp
  let g : Ω → ℝ := fun x => ‖f x‖ ^ q
  have hg : AEStronglyMeasurable g μ := (hf.norm.aemeasurable.pow_const q).aestronglyMeasurable
  have hi : (∫⁻ x, ‖f x‖ₑ ^ q ∂μ) = ∫⁻ x, ‖g x‖ₑ ∂μ := by
    apply lintegral_congr
    intro x
    simp only [g, ← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (f x)) _)]
    exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hq.le
  rw [hi]
  calc
    _ ≤ (μ univ) ^ (1 - 1 / (p / q)) * weakLpN μ (p / q) g :=
      lintegral_enorm_le_weakLpN μ (p / q) g
    _ ≤ (μ univ) ^ (1 - 1 / (p / q)) *
        (ENNReal.ofReal ((p / q) / (p / q - 1)) * weakLpQ μ (p / q) g) :=
      mul_le_mul' le_rfl (weakLpN_le_conj_mul_weakLpQ μ (p / q) ha g hg)
    _ ≤ (μ univ) ^ (1 - 1 / (p / q)) *
        (ENNReal.ofReal ((p / q) / (p / q - 1)) * weakLpQ μ p f ^ q) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (weakLpQ_norm_rpow_le μ p q hp hq f))
    _ = _ := by
      have he : 1 / (p / q) = q / p := by field_simp
      have hc : (p / q) / (p / q - 1) = p / (p - q) := by field_simp
      rw [he, hc]
      ac_rfl

theorem eLpNorm_le_weakLpQ (μ : Measure Ω) [IsFiniteMeasure μ]
    (p q : ℝ) (hq : 1 ≤ q) (hqp : q < p) (f : Ω → E)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal ((p / (p - q)) ^ (1 / q)) *
        (μ univ) ^ (1 / q - 1 / p) * weakLpQ μ p f := by
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := hq0.trans hqp
  have hc : 0 ≤ p / (p - q) := by positivity
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top hf,
    eLpNorm', ENNReal.toReal_ofReal hq0.le]
  calc
    _ ≤ (ENNReal.ofReal (p / (p - q)) * (μ univ) ^ (1 - q / p) * weakLpQ μ p f ^ q) ^ (1 / q) :=
      ENNReal.rpow_le_rpow (lintegral_rpow_enorm_le_weakLpQ μ p q hq0 hqp f hf)
        (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / q),
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / q),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        ENNReal.ofReal_rpow_of_nonneg hc (by positivity : 0 ≤ 1 / q)]
      rw [show q * (1 / q) = 1 by field_simp, ENNReal.rpow_one]
      congr 2
      field_simp

theorem weakLp_weakToStrong : WeakLpEstimatesSpec.WeakToStrongStatement :=
  fun μ _ p q hq hqp f hf => eLpNorm_le_weakLpQ μ p q hq hqp f hf

/-- The zero cases used by all the extended-valued estimates. -/
theorem weakLp_zeroCases : WeakLpEstimatesSpec.ZeroCasesStatement := by
  intro Ω E _ _
  constructor
  · intro f p hp
    exact ⟨weakLpQ_zero_measure p hp f, weakLpN_zero_measure p f, by simp⟩
  · intro μ _ f p hp hf hQ
    have hN : weakLpN μ p f = 0 := by
      apply le_antisymm _ bot_le
      simpa [hQ] using weakLpN_le_conj_mul_weakLpQ μ p hp f hf
    have hz := (weakLpN_eq_zero_iff μ p f hf).mp hN
    refine ⟨hz, fun q _ => ?_⟩
    rw [eLpNorm_congr_ae hz]
    exact eLpNorm_zero

/-- Integrating the low-level power in the two-distribution interpolation bound. -/
lemma lintegral_Ioc_rpow (b a : ℝ) (hb : -1 < b) (ha : 0 < a) :
    (∫⁻ t : ℝ in Ioc 0 a, ENNReal.ofReal (t ^ b)) =
      ENNReal.ofReal (a ^ (b + 1) / (b + 1)) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ b) (Ioc 0 a) :=
    (intervalIntegral.intervalIntegrable_rpow' hb).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => Real.rpow_nonneg ht.1.le _)),
    ← intervalIntegral.integral_of_le ha.le, integral_rpow (Or.inl hb),
    Real.zero_rpow (by linarith : b + 1 ≠ 0), sub_zero]

/-- Two weak bounds, integrated on the two sides of an arbitrary positive level. -/
theorem lintegral_rpow_enorm_le_two_weakLpQ (μ : Measure Ω) [IsFiniteMeasure μ]
    (p q r : ℝ) (hq : 0 < q) (hqp : q < p) (hpr : p < r)
    (f : Ω → E) (hf : AEStronglyMeasurable f μ)
    (B D a : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (ha : 0 < a)
    (hQB : weakLpQ μ q f ≤ ENNReal.ofReal B)
    (hQD : weakLpQ μ r f ≤ ENNReal.ofReal D) :
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ≤
      ENNReal.ofReal (p * (B ^ q * a ^ (p - q) / (p - q) +
        D ^ r * a ^ (p - r) / (r - p))) := by
  have hp : 0 < p := hq.trans hqp
  have hr : 0 < r := hp.trans hpr
  have hunion : Ioc 0 a ∪ Ioi a = Ioi (0 : ℝ) := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · exact ha.trans ht
    · intro ht
      exact (le_or_gt t a).elim (fun h => Or.inl ⟨ht, h⟩) Or.inr
  have hbound (s C t : ℝ) (hs : 0 < s) (hC : 0 ≤ C) (ht : 0 < t)
      (hQ : weakLpQ μ s f ≤ ENNReal.ofReal C) :
      distribution μ f t * ENNReal.ofReal (t ^ (p - 1)) ≤
        ENNReal.ofReal (C ^ s) * ENNReal.ofReal (t ^ (p - s - 1)) := by
    calc
      _ ≤ (ENNReal.ofReal (C ^ s) * ENNReal.ofReal (t ^ (-s))) *
          ENNReal.ofReal (t ^ (p - 1)) :=
        mul_le_mul' (distribution_le_of_weakLpQ_le μ s hs f C hC hQ t ht) le_rfl
      _ = _ := by
        rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
          ← Real.rpow_add ht]
        congr 2
        ring
  have hi : (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0,
        distribution μ f t * ENNReal.ofReal (t ^ (p - 1)) := by
    simpa only [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, ofReal_norm,
      distribution] using lintegral_rpow_eq_lintegral_meas_lt_mul μ
        (ae_of_all _ (fun x => norm_nonneg (f x))) hf.norm.aemeasurable hp
  rw [hi, ← hunion, lintegral_union measurableSet_Ioi (by
    apply disjoint_left.2
    intro t ht hs
    exact ht.2.not_gt hs)]
  have hl : (∫⁻ t in Ioc 0 a, distribution μ f t * ENNReal.ofReal (t ^ (p - 1))) ≤
      ENNReal.ofReal (B ^ q * a ^ (p - q) / (p - q)) := by
    calc
      _ ≤ ∫⁻ t in Ioc 0 a, ENNReal.ofReal (B ^ q) *
          ENNReal.ofReal (t ^ (p - q - 1)) :=
        setLIntegral_mono' measurableSet_Ioc (fun t ht => hbound q B t hq hB ht.1 hQB)
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_Ioc_rpow _ a (by linarith) ha,
          show p - q - 1 + 1 = p - q by ring,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hB _)]
        congr 1
        ring
  have hu : (∫⁻ t in Ioi a, distribution μ f t * ENNReal.ofReal (t ^ (p - 1))) ≤
      ENNReal.ofReal (D ^ r * a ^ (p - r) / (r - p)) := by
    calc
      _ ≤ ∫⁻ t in Ioi a, ENNReal.ofReal (D ^ r) *
          ENNReal.ofReal (t ^ (p - r - 1)) :=
        setLIntegral_mono' measurableSet_Ioi (fun t ht => hbound r D t hr hD (ha.trans ht) hQD)
      _ = _ := by
        have he : p - r - 1 = -(r - p + 1) := by ring
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, he,
          lintegral_Ioi_rpow_neg (r - p + 1) a (by linarith) ha,
          show 1 - (r - p + 1) = p - r by ring,
          show r - p + 1 - 1 = r - p by ring,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hD _)]
        congr 1
        ring
  calc
    _ ≤ ENNReal.ofReal p * (ENNReal.ofReal (B ^ q * a ^ (p - q) / (p - q)) +
        ENNReal.ofReal (D ^ r * a ^ (p - r) / (r - p))) :=
      mul_le_mul' le_rfl (add_le_add hl hu)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hp.le]

/-- The elementary balancing identity for the two distribution tails. -/
lemma weakLp_interpolation_balance (p q r θ B D : ℝ)
    (hq : 0 < q) (hqp : q < p) (hpr : p < r)
    (hθ : 1 / p = θ / q + (1 - θ) / r) (hB : 0 < B) (hD : 0 < D) :
    let a := D ^ (r / (r - q)) * B ^ (-q / (r - q))
    p * (B ^ q * a ^ (p - q) / (p - q) + D ^ r * a ^ (p - r) / (r - p)) =
      (p / (p - q) + p / (r - p)) * (B ^ θ * D ^ (1 - θ)) ^ p := by
  have hp : 0 < p := hq.trans hqp
  have hr : 0 < r := hp.trans hpr
  have hrq : 0 < r - q := by linarith
  have hθ' : θ = q * (r - p) / (p * (r - q)) := by
    field_simp at hθ ⊢
    nlinarith [hθ]
  subst θ
  have he₁ : q + (-q / (r - q)) * (p - q) =
      (q * (r - p) / (p * (r - q))) * p := by field_simp; ring
  have he₂ : (r / (r - q)) * (p - q) =
      (1 - q * (r - p) / (p * (r - q))) * p := by field_simp; ring
  have he₃ : (-q / (r - q)) * (p - r) =
      (q * (r - p) / (p * (r - q))) * p := by field_simp; ring
  have he₄ : r + (r / (r - q)) * (p - r) =
      (1 - q * (r - p) / (p * (r - q))) * p := by field_simp; ring
  dsimp only
  rw [Real.mul_rpow (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg hB.le _),
    Real.mul_rpow (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg hB.le _),
    Real.mul_rpow (Real.rpow_nonneg hB.le _) (Real.rpow_nonneg hD.le _)]
  simp only [← Real.rpow_mul hB.le, ← Real.rpow_mul hD.le]
  have hlow : B ^ q * (D ^ (r / (r - q) * (p - q)) * B ^ (-q / (r - q) * (p - q))) =
      B ^ (q * (r - p) / (p * (r - q)) * p) *
        D ^ ((1 - q * (r - p) / (p * (r - q))) * p) := by
    calc
      _ = (B ^ q * B ^ (-q / (r - q) * (p - q))) * D ^ (r / (r - q) * (p - q)) := by ring
      _ = _ := by rw [← Real.rpow_add hB, he₁, he₂]
  have hhigh : D ^ r * (D ^ (r / (r - q) * (p - r)) * B ^ (-q / (r - q) * (p - r))) =
      B ^ (q * (r - p) / (p * (r - q)) * p) *
        D ^ ((1 - q * (r - p) / (p * (r - q))) * p) := by
    calc
      _ = B ^ (-q / (r - q) * (p - r)) * (D ^ r * D ^ (r / (r - q) * (p - r))) := by ring
      _ = _ := by rw [← Real.rpow_add hD, he₃, he₄]
  rw [hlow, hhigh]
  ring

/-- A positive real bound on each weak quasi-norm gives interpolation. -/
theorem eLpNorm_le_of_two_weakLpQ_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (p q r θ : ℝ) (hq : 0 < q) (hqp : q < p) (hpr : p < r)
    (hθ : 1 / p = θ / q + (1 - θ) / r)
    (f : Ω → E) (hf : AEStronglyMeasurable f μ)
    (B D : ℝ) (hB : 0 < B) (hD : 0 < D)
    (hQB : weakLpQ μ q f ≤ ENNReal.ofReal B)
    (hQD : weakLpQ μ r f ≤ ENNReal.ofReal D) :
    eLpNorm f (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ((p / (p - q) + p / (r - p)) ^ (1 / p)) *
        ENNReal.ofReal B ^ θ * ENNReal.ofReal D ^ (1 - θ) := by
  have hp : 0 < p := hq.trans hqp
  let a := D ^ (r / (r - q)) * B ^ (-q / (r - q))
  have ha : 0 < a := mul_pos (Real.rpow_pos_of_pos hD _) (Real.rpow_pos_of_pos hB _)
  have hb := lintegral_rpow_enorm_le_two_weakLpQ μ p q r hq hqp hpr f hf B D a hB.le hD.le ha hQB hQD
  rw [weakLp_interpolation_balance p q r θ B D hq hqp hpr hθ hB hD] at hb
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top hf,
    eLpNorm', ENNReal.toReal_ofReal hp.le]
  refine (ENNReal.rpow_le_rpow hb (by positivity : 0 ≤ 1 / p)).trans_eq ?_
  have hK : 0 ≤ p / (p - q) + p / (r - p) := by positivity
  have hprod : 0 ≤ B ^ θ * D ^ (1 - θ) := by positivity
  rw [ENNReal.ofReal_mul hK,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p),
    ENNReal.ofReal_rpow_of_nonneg hK (by positivity : 0 ≤ 1 / p),
    ← ENNReal.ofReal_rpow_of_nonneg hprod hp.le, ← ENNReal.rpow_mul,
    show p * (1 / p) = 1 by field_simp, ENNReal.rpow_one,
    ENNReal.ofReal_mul (Real.rpow_nonneg hB.le _),
    ← ENNReal.ofReal_rpow_of_pos hB, ← ENNReal.ofReal_rpow_of_pos hD, mul_assoc]

/-- The interpolation parameter forced by the reciprocal-exponent identity. -/
lemma weakLp_interpolation_parameter (p q r θ : ℝ)
    (hq : 0 < q) (hqp : q < p) (hpr : p < r)
    (hθ : 1 / p = θ / q + (1 - θ) / r) : 0 < θ ∧ θ < 1 := by
  have hp : 0 < p := hq.trans hqp
  have hr : 0 < r := hp.trans hpr
  have hrq : 0 < r - q := by linarith
  have he : θ = q * (r - p) / (p * (r - q)) := by
    field_simp at hθ ⊢
    nlinarith [hθ]
  rw [he]
  constructor
  · positivity
  · apply (div_lt_one (mul_pos hp hrq)).mpr
    nlinarith

/-- Interpolation between two Banach weak norms, including zero and infinite
values. Its constant depends only on p,q,r. -/
theorem weakLp_interpolation : WeakLpEstimatesSpec.InterpolationStatement := by
  intro p q r hq hqp hpr
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := hq0.trans hqp
  have hr0 : 0 < r := hp0.trans hpr
  let C : ℝ := (p / (p - q) + p / (r - p)) ^ (1 / p)
  have hC : 0 < C := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨C, hC, ?_⟩
  intro Ω E _ _ μ _ θ hθ f hf
  obtain ⟨hθ0, hθ1⟩ := weakLp_interpolation_parameter p q r θ hq0 hqp hpr hθ
  have hθc : 0 < 1 - θ := by linarith
  by_cases hB0 : weakLpN μ q f = 0
  · have hz := (weakLpN_eq_zero_iff μ q f hf).mp hB0
    rw [eLpNorm_congr_ae hz, eLpNorm_zero]
    exact bot_le
  by_cases hD0 : weakLpN μ r f = 0
  · have hz := (weakLpN_eq_zero_iff μ r f hf).mp hD0
    rw [eLpNorm_congr_ae hz, eLpNorm_zero]
    exact bot_le
  by_cases hBtop : weakLpN μ q f = ∞
  · rw [hBtop, ENNReal.top_rpow_of_pos hθ0,
      ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hC),
      ENNReal.top_mul (by simpa only [ne_eq, ENNReal.rpow_eq_zero_iff_of_pos hθc] using hD0)]
    exact le_top
  by_cases hDtop : weakLpN μ r f = ∞
  · rw [hDtop, ENNReal.top_rpow_of_pos hθc,
      ENNReal.mul_top (mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hC)
        (by simpa only [ne_eq, ENNReal.rpow_eq_zero_iff_of_pos hθ0] using hB0))]
    exact le_top
  have hB : 0 < (weakLpN μ q f).toReal := ENNReal.toReal_pos hB0 hBtop
  have hD : 0 < (weakLpN μ r f).toReal := ENNReal.toReal_pos hD0 hDtop
  have hb := eLpNorm_le_of_two_weakLpQ_le μ p q r θ hq0 hqp hpr hθ f hf
    (weakLpN μ q f).toReal (weakLpN μ r f).toReal hB hD
    (by rw [ENNReal.ofReal_toReal hBtop]; exact weakLpQ_le_weakLpN μ q hq0 f hf)
    (by rw [ENNReal.ofReal_toReal hDtop]; exact weakLpQ_le_weakLpN μ r hr0 f hf)
  simpa only [ENNReal.ofReal_toReal hBtop, ENNReal.ofReal_toReal hDtop] using hb

section RadialExample

variable {𝕜 : Type} [RCLike 𝕜]

@[simp] theorem norm_radialWitness (d : ℕ) (p : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖WeakLpEstimatesSpec.radialWitness (𝕜 := 𝕜) d p x‖ = ‖x‖ ^ (-(d : ℝ) / p) := by
  simp only [WeakLpEstimatesSpec.radialWitness, RCLike.norm_ofReal,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]

theorem radialWitness_aestronglyMeasurable (d : ℕ) (p : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) :
    AEStronglyMeasurable (WeakLpEstimatesSpec.radialWitness (𝕜 := 𝕜) d p) μ :=
  RCLike.continuous_ofReal.comp_aestronglyMeasurable
    ((measurable_norm.pow_const (-(d : ℝ) / p)).aestronglyMeasurable)

/-- The superlevel set of the radial witness is contained in the ball whose
volume has precisely the required power decay. -/
theorem weakLpQ_radialWitness_le (d : ℕ) (hd : 0 < d) (p : ℝ) (hp : 0 < p) :
    weakLpQ (volume.restrict (Metric.ball 0 1)) p
      (WeakLpEstimatesSpec.radialWitness (𝕜 := 𝕜) d p) ≤
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) ^ (1 / p) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  let V := EuclideanSpace ℝ (Fin d)
  let w := WeakLpEstimatesSpec.radialWitness (𝕜 := 𝕜) d p
  refine iSup_le fun t => iSup_le fun ht => ?_
  have hs : 0 < t ^ (-p / (d : ℝ)) := Real.rpow_pos_of_pos ht _
  have hsubset : {x : V | t < ‖w x‖} ⊆ Metric.ball 0 (t ^ (-p / (d : ℝ))) := by
    intro x hx
    have hx' : t < ‖x‖ ^ (-(d : ℝ) / p) := by simpa only [w, norm_radialWitness, mem_ofPred_eq] using hx
    have hxn : 0 < ‖x‖ := by
      by_contra hn
      have hz : ‖x‖ = 0 := le_antisymm (not_lt.mp hn) (norm_nonneg x)
      rw [hz, Real.zero_rpow (div_ne_zero (neg_ne_zero.mpr hdR.ne') hp.ne')] at hx'
      exact (ht.trans hx').false
    have hb := Real.rpow_lt_rpow_of_neg ht hx' (div_neg_of_neg_of_pos (neg_neg_of_pos hp) hdR)
    rw [← Real.rpow_mul hxn.le,
      show (-(d : ℝ) / p) * (-p / (d : ℝ)) = 1 by field_simp,
      Real.rpow_one] at hb
    simpa only [Metric.mem_ball, dist_zero_right] using hb
  have hmeasure : DistributionFunctionsSpec.DistributionValue
      (volume.restrict (Metric.ball 0 1)) w t ≤
      ENNReal.ofReal (t ^ (-p)) * volume (Metric.ball (0 : V) 1) := by
    calc
      _ ≤ volume {x : V | t < ‖w x‖} := Measure.restrict_apply_le _ _
      _ ≤ volume (Metric.ball (0 : V) (t ^ (-p / (d : ℝ)))) := measure_mono hsubset
      _ = _ := by
        rw [Measure.addHaar_ball_of_pos volume (0 : V) hs, finrank_euclideanSpace_fin,
          ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
        congr 2
        field_simp
  change ENNReal.ofReal t * DistributionFunctionsSpec.DistributionValue
    (volume.restrict (Metric.ball 0 1)) w t ^ (1 / p) ≤ _
  calc
    _ ≤ ENNReal.ofReal t *
        (ENNReal.ofReal (t ^ (-p)) * volume (Metric.ball (0 : V) 1)) ^ (1 / p) :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hmeasure (by positivity))
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p),
        ← ENNReal.ofReal_rpow_of_pos ht]
      rw [← ENNReal.rpow_mul]
      rw [show -p * (1 / p) = -1 by field_simp, ENNReal.rpow_neg_one,
        ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr ht).ne'
          ENNReal.ofReal_ne_top, one_mul]

/-- Polar integration reduces the pth power to the nonintegrable 1/r. -/
theorem radialWitness_not_memLp (d : ℕ) (hd : 0 < d) (p : ℝ) (hp : 0 < p) :
    ¬ MemLp (WeakLpEstimatesSpec.radialWitness (𝕜 := 𝕜) d p) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball 0 1)) := by
  intro hmem
  let V := EuclideanSpace ℝ (Fin d)
  have hdim : 0 < Module.finrank ℝ V := by simpa only [V, finrank_euclideanSpace_fin] using hd
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hdim
  have hi := hmem.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
  simp only [ENNReal.toReal_ofReal hp.le, norm_radialWitness, ← Real.rpow_mul (norm_nonneg _),
    div_mul_cancel₀ _ hp.ne'] at hi
  have hir : IntegrableOn (fun y : ℝ => y ^ (d - 1) * y ^ (-(d : ℝ))) (Ioo 0 1) := by
    simpa only [V, finrank_euclideanSpace_fin, smul_eq_mul] using
      (integrableOn_fun_norm_addHaar (volume : Measure V)
        (f := fun y : ℝ => y ^ (-(d : ℝ))) (r := 1)).mp hi
  have heq : EqOn (fun y : ℝ => y ^ (d - 1) * y ^ (-(d : ℝ)))
      (fun y => y ^ (-1 : ℝ)) (Ioo 0 1) := by
    intro y hy
    change y ^ (d - 1) * y ^ (-(d : ℝ)) = y ^ (-1 : ℝ)
    rw [← Real.rpow_natCast, ← Real.rpow_add hy.1]
    congr 1
    rw [Nat.cast_sub (show 1 ≤ d from hd), Nat.cast_one]
    ring
  have hbad := intervalIntegral.integrableOn_Ioo_rpow_iff (s := (-1 : ℝ)) zero_lt_one
  have hcontra := hbad.mp (hir.congr_fun heq measurableSet_Ioo)
  exact lt_irrefl _ hcontra

/-- Strictness holds over both scalar fields, on the actual Euclidean ball. -/
theorem weakLp_strictInclusion : WeakLpEstimatesSpec.StrictInclusionStatement := by
  intro 𝕜 _ d hd p hp
  let V := EuclideanSpace ℝ (Fin d)
  let μ : Measure V := volume.restrict (Metric.ball 0 1)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let w := WeakLpEstimatesSpec.radialWitness (𝕜 := 𝕜) d p
  have hw : AEStronglyMeasurable w μ := radialWitness_aestronglyMeasurable d p μ
  have hQ : weakLpQ μ p w < ∞ :=
    (weakLpQ_radialWitness_le d hd p (by linarith)).trans_lt
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) measure_ball_ne_top)
  have hN : weakLpN μ p w < ∞ :=
    (weakLpN_le_conj_mul_weakLpQ μ p hp w hw).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQ)
  exact ⟨fun f hf => (weakLpN_le_eLpNorm μ p hp f hf.aestronglyMeasurable).trans_lt hf,
    hw, hQ, hN, radialWitness_not_memLp d hd p (by linarith)⟩

end RadialExample

end ExpandedFA.PartIV
