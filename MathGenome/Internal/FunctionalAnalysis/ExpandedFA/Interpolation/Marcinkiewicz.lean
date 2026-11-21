import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Interpolation.Marcinkiewicz
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Marcinkiewicz interpolation and unique linear extension, paper.tex:18150–18179.
The independent statements in `MarcinkiewiczSpec` retain arbitrary measures,
real/complex scalars, finite and infinity endpoints, and uniform norm bounds.
Weighted-measure layer cake and Tonelli complete the truncation argument.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal
universe u v w

namespace ExpandedFA.Interpolation
open MarcinkiewiczSpec

variable {X Y E F : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Large-value truncation in the source's decomposition. -/
def highPart (a : ℝ) (f : X → E) : X → E := {x | a < ‖f x‖}.indicator f

/-- Complementary small-value truncation, including equality at the threshold. -/
def lowPart (a : ℝ) (f : X → E) : X → E := {x | a < ‖f x‖}ᶜ.indicator f

omit [MeasurableSpace X] in
theorem highPart_add_lowPart (a : ℝ) (f : X → E) :
    highPart a f + lowPart a f = f := by
  classical
  funext x
  by_cases hx : a < ‖f x‖ <;> simp [highPart, lowPart, hx]

theorem distribution_antitone (μ : Measure X) (f : X → E) :
    Antitone (distribution μ f) := by
  intro a b hab
  exact measure_mono fun x hx => lt_of_le_of_lt hab hx

theorem distribution_congr_ae {μ : Measure X} {f g : X → E} (h : f =ᵐ[μ] g) (t : ℝ) :
    distribution μ f t = distribution μ g t := by
  apply measure_congr
  filter_upwards [h] with x hx
  simp only [hx]

/-- The distribution estimate used after subadditivity. No measurability or
finiteness of the underlying measure is needed for this outer-measure bound. -/
theorem distribution_le_add {ν : Measure Y} {f g h : Y → F}
    (hf : ∀ᵐ y ∂ν, ‖f y‖ ≤ ‖g y‖ + ‖h y‖) (t : ℝ) :
    distribution ν f t ≤ distribution ν g (t / 2) + distribution ν h (t / 2) := by
  calc
    distribution ν f t ≤ ν ({y | t / 2 < ‖g y‖} ∪ {y | t / 2 < ‖h y‖}) := by
      apply measure_mono_ae
      filter_upwards [hf] with y hy
      change (t < ‖f y‖) → (t / 2 < ‖g y‖ ∨ t / 2 < ‖h y‖)
      intro hyt
      by_contra hh
      push Not at hh
      linarith
    _ ≤ distribution ν g (t / 2) + distribution ν h (t / 2) := measure_union_le _ _

/-- If the low image has modulus at most half the level, its distribution
contribution disappears. This is the infinity-endpoint step. -/
theorem distribution_le_of_low_bound {ν : Measure Y} {f g h : Y → F}
    (hf : ∀ᵐ y ∂ν, ‖f y‖ ≤ ‖g y‖ + ‖h y‖)
    {t : ℝ} (hh : ∀ᵐ y ∂ν, ‖h y‖ ≤ t / 2) :
    distribution ν f t ≤ distribution ν g (t / 2) := by
  apply measure_mono_ae
  filter_upwards [hf, hh] with y hy hhy
  change (t < ‖f y‖) → (t / 2 < ‖g y‖)
  intro ht
  linarith

/-- The layer-cake identity, retaining possible infinite values. Mathlib's
formulation applies to arbitrary measures, with no sigma-finiteness assumption. -/
theorem moment_layercake (μ : Measure X) {f : X → E}
    (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) = ENNReal.ofReal p *
      ∫⁻ t in Ioi 0, distribution μ f t * ENNReal.ofReal (t ^ (p - 1)) := by
  convert lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (Eventually.of_forall fun x => norm_nonneg (f x)) hf.norm.aemeasurable hp using 1
  · congr 1
    funext x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  · rfl

/-- Strong measurability of both truncations uses null-measurable level sets,
so no completion of the measure space is assumed. -/
theorem highPart_aestronglyMeasurable {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) (a : ℝ) :
    AEStronglyMeasurable (highPart a f) μ := by
  exact hf.indicator₀ (nullMeasurableSet_lt aemeasurable_const hf.norm.aemeasurable)

theorem lowPart_aestronglyMeasurable {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) (a : ℝ) :
    AEStronglyMeasurable (lowPart a f) μ := by
  exact hf.indicator₀ (nullMeasurableSet_lt aemeasurable_const hf.norm.aemeasurable).compl

/-- Raising the finite extended Lᵖ norm to its exponent gives the moment. -/
theorem eLpNorm_ofReal_rpow {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) {r : ℝ} (hr : 0 < r) :
    eLpNorm f (ENNReal.ofReal r) μ ^ r = ∫⁻ x, ‖f x‖ₑ ^ r ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hr.le, ← ENNReal.rpow_mul, one_div_mul_cancel hr.ne',
    ENNReal.rpow_one]

/-- Bridge from the usual weak-norm convention in the Specs to the powered
level-set inequality used in the proof. This equivalence allows zero constants. -/
theorem endpointEstimate_finite_iff {μ : Measure X} {ν : Measure Y}
    {f : X → E} {g : Y → F} (hf : AEStronglyMeasurable f μ)
    {r : ℝ} (hr : 0 < r) (C : ℝ≥0) :
    endpointEstimate μ ν (ENNReal.ofReal r) C f g ↔
      ∀ t : ℝ, 0 < t → ENNReal.ofReal t ^ r * distribution ν g t ≤
        (C : ℝ≥0∞) ^ r * ∫⁻ x, ‖f x‖ₑ ^ r ∂μ := by
  simp only [endpointEstimate, ENNReal.ofReal_ne_top, ↓reduceIte,
    ENNReal.toReal_ofReal hr.le]
  apply forall_congr'
  intro t
  apply imp_congr_right
  intro _ht
  rw [← ENNReal.rpow_le_rpow_iff hr, ENNReal.mul_rpow_of_nonneg _ _ hr.le,
    ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hr.ne', ENNReal.rpow_one, eLpNorm_ofReal_rpow hf hr]

/-- On the large-value part the lower moment is dominated by the pth moment. -/
theorem highPart_moment_le (μ : Measure X) (f : X → E)
    {a r p : ℝ} (ha : 0 < a) (hr : 0 < r) (hrp : r ≤ p) :
    (∫⁻ x, ‖highPart a f x‖ₑ ^ r ∂μ) ≤
      ENNReal.ofReal (a ^ (r - p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  classical
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  by_cases hx : a < ‖f x‖
  · simp only [highPart, indicator_of_mem (show x ∈ {x | a < ‖f x‖} from hx)]
    have hpos : 0 < ‖f x‖ := ha.trans hx
    have hreal : ‖f x‖ ^ r ≤ a ^ (r - p) * ‖f x‖ ^ p := by
      calc
        ‖f x‖ ^ r = ‖f x‖ ^ (r - p) * ‖f x‖ ^ p := by
          rw [← Real.rpow_add hpos]; congr 1; ring
        _ ≤ a ^ (r - p) * ‖f x‖ ^ p :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos ha hx.le (sub_nonpos.mpr hrp))
            (Real.rpow_nonneg (norm_nonneg _) _)
    simpa only [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (hr.le.trans hrp),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)] using ENNReal.ofReal_le_ofReal hreal
  · simp [highPart, hx, ENNReal.zero_rpow_of_pos hr]

/-- On the small-value part the upper moment is dominated by the pth moment. -/
theorem lowPart_moment_le (μ : Measure X) (f : X → E)
    {a p r : ℝ} (ha : 0 < a) (hp : 0 < p) (hpr : p ≤ r) :
    (∫⁻ x, ‖lowPart a f x‖ₑ ^ r ∂μ) ≤
      ENNReal.ofReal (a ^ (r - p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  classical
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  by_cases hx : a < ‖f x‖
  · simp [lowPart, hx, ENNReal.zero_rpow_of_pos (hp.trans_le hpr)]
  · simp only [lowPart, indicator_of_mem (show x ∈ {x | a < ‖f x‖}ᶜ from hx)]
    have hreal : ‖f x‖ ^ r ≤ a ^ (r - p) * ‖f x‖ ^ p := by
      by_cases hz : ‖f x‖ = 0
      · simp [hz, Real.zero_rpow hp.ne', Real.zero_rpow (hp.trans_le hpr).ne']
      have hpos : 0 < ‖f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      calc
        ‖f x‖ ^ r = ‖f x‖ ^ (r - p) * ‖f x‖ ^ p := by
          rw [← Real.rpow_add hpos]; congr 1; ring
        _ ≤ a ^ (r - p) * ‖f x‖ ^ p :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (norm_nonneg _) (le_of_not_gt hx) (sub_nonneg.mpr hpr))
            (Real.rpow_nonneg (norm_nonneg _) _)
    simpa only [← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (hp.le.trans hpr),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)] using ENNReal.ofReal_le_ofReal hreal

/-- The high part of an intermediate input belongs to the lower endpoint. -/
theorem highPart_memLp {μ : Measure X} {f : X → E} {a r p : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hrp : r ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (highPart a f) (ENNReal.ofReal r) μ := by
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by positivity) ENNReal.ofReal_ne_top (highPart_aestronglyMeasurable hf.aestronglyMeasurable a)).2
  rw [ENNReal.toReal_ofReal hr.le]
  apply (highPart_moment_le μ f ha hr hrp).trans_lt
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  have hp : 0 < p := hr.trans_le hrp
  simpa only [ENNReal.toReal_ofReal hp.le] using
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by positivity) ENNReal.ofReal_ne_top hf

/-- The low part belongs to the finite upper endpoint. -/
theorem lowPart_memLp {μ : Measure X} {f : X → E} {a p r : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hpr : p ≤ r)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (lowPart a f) (ENNReal.ofReal r) μ := by
  have hr : 0 < r := hp.trans_le hpr
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by positivity) ENNReal.ofReal_ne_top (lowPart_aestronglyMeasurable hf.aestronglyMeasurable a)).2
  rw [ENNReal.toReal_ofReal (hp.le.trans hpr)]
  apply (lowPart_moment_le μ f ha hp hpr).trans_lt
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  simpa only [ENNReal.toReal_ofReal hp.le] using
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by positivity) ENNReal.ofReal_ne_top hf

/-- The small-value part satisfies the essential supremum bound. -/
theorem lowPart_eLpNorm_top_le {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) {a : ℝ} (ha : 0 ≤ a) :
    eLpNorm (lowPart a f) ∞ μ ≤ ENNReal.ofReal a := by
  rw [eLpNorm_exponent_top (lowPart_aestronglyMeasurable hf a)]
  apply eLpNormEssSup_le_of_ae_bound
  apply Eventually.of_forall
  intro x
  classical
  by_cases hx : a < ‖f x‖
  · simpa [lowPart, hx] using ha
  · simpa [lowPart, hx] using le_of_not_gt hx

/-- Endpoint membership embeds into the sum domain without additional
representative choices. -/
theorem sumDomain_of_memLp_left {μ : Measure X} {f : X → E}
    {p₀ p₁ : ℝ≥0∞} (hf : MemLp f p₀ μ) : sumDomain μ p₀ p₁ f := by
  refine ⟨f, 0, hf, MemLp.zero, ?_⟩
  simp

theorem sumDomain_of_memLp_right {μ : Measure X} {f : X → E}
    {p₀ p₁ : ℝ≥0∞} (hf : MemLp f p₁ μ) : sumDomain μ p₀ p₁ f := by
  refine ⟨0, f, MemLp.zero, hf, ?_⟩
  simp

/-- Every intermediate input is in the operator's common domain, with an
explicit decomposition into endpoint functions. -/
theorem memLp_sumDomain {μ : Measure X} {f : X → E} {r₀ r₁ p : ℝ}
    (hr₀ : 0 < r₀) (h₀ : r₀ ≤ p) (h₁ : p ≤ r₁)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    sumDomain μ (ENNReal.ofReal r₀) (ENNReal.ofReal r₁) f := by
  refine ⟨highPart 1 f, lowPart 1 f,
    highPart_memLp zero_lt_one hr₀ h₀ hf,
    lowPart_memLp zero_lt_one (hr₀.trans_le h₀) h₁ hf, ?_⟩
  rw [highPart_add_lowPart]

theorem memLp_sumDomain_top {μ : Measure X} {f : X → E} {r₀ p : ℝ}
    (hr₀ : 0 < r₀) (h₀ : r₀ ≤ p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    sumDomain μ (ENNReal.ofReal r₀) ∞ f := by
  refine ⟨highPart 1 f, lowPart 1 f, highPart_memLp zero_lt_one hr₀ h₀ hf, ?_, ?_⟩
  · exact (lowPart_eLpNorm_top_le hf.aestronglyMeasurable zero_le_one).trans_lt
      ENNReal.ofReal_lt_top
  · rw [highPart_add_lowPart]

/-- Solving the powered weak estimate for the distribution, without discarding
infinite values and without excluding the zero weak constant. -/
theorem distribution_le_of_endpointEstimate {μ : Measure X} {ν : Measure Y}
    {f : X → E} {g : Y → F} (hf : AEStronglyMeasurable f μ)
    {r : ℝ} (hr : 0 < r) {C : ℝ≥0}
    (hw : endpointEstimate μ ν (ENNReal.ofReal r) C f g) {t : ℝ} (ht : 0 < t) :
    distribution ν g t ≤ ENNReal.ofReal t ^ (-r) * (C : ℝ≥0∞) ^ r *
      ∫⁻ x, ‖f x‖ₑ ^ r ∂μ := by
  have h := (endpointEstimate_finite_iff hf hr C).1 hw t ht
  have hzero : ENNReal.ofReal t ^ r ≠ 0 := by positivity
  have htop : ENNReal.ofReal t ^ r ≠ ∞ := by finiteness
  calc
    distribution ν g t = (ENNReal.ofReal t ^ r)⁻¹ *
        (ENNReal.ofReal t ^ r * distribution ν g t) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hzero htop, one_mul]
    _ ≤ (ENNReal.ofReal t ^ r)⁻¹ *
        ((C : ℝ≥0∞) ^ r * ∫⁻ x, ‖f x‖ₑ ^ r ∂μ) := mul_le_mul_right h _
    _ = _ := by rw [ENNReal.rpow_neg, mul_assoc]

/-- The exact finite-endpoint distribution inequality before layer integration.
The two moments involve different truncations, which is essential for integrability
in the level parameter; replacing them by the full endpoint moments loses this. -/
theorem distribution_truncation_bound
    {𝕜 : Type*} [RCLike 𝕜] (μ : Measure X) (ν : Measure Y)
    {r₀ r₁ p a t : ℝ} (hr₀ : 0 < r₀) (h₀ : r₀ ≤ p) (h₁ : p ≤ r₁)
    (ha : 0 < a) (ht : 0 < t) {C₀ C₁ : ℝ≥0}
    (T : (X → 𝕜) → Y → 𝕜)
    (hs : SublinearOn μ ν (sumDomain μ (ENNReal.ofReal r₀) (ENNReal.ofReal r₁)) T)
    (hw₀ : endpointBound μ ν (ENNReal.ofReal r₀) C₀ T)
    (hw₁ : endpointBound μ ν (ENNReal.ofReal r₁) C₁ T)
    {f : X → 𝕜} (hf : MemLp f (ENNReal.ofReal p) μ) :
    distribution ν (T f) t ≤
      ENNReal.ofReal (t / 2) ^ (-r₀) * (C₀ : ℝ≥0∞) ^ r₀ *
        (∫⁻ x, ‖highPart a f x‖ₑ ^ r₀ ∂μ) +
      ENNReal.ofReal (t / 2) ^ (-r₁) * (C₁ : ℝ≥0∞) ^ r₁ *
        (∫⁻ x, ‖lowPart a f x‖ₑ ^ r₁ ∂μ) := by
  have hg := highPart_memLp ha hr₀ h₀ hf
  have hh := lowPart_memLp ha (hr₀.trans_le h₀) h₁ hf
  have hadd := hs.add_le (highPart a f) (lowPart a f)
    (sumDomain_of_memLp_left hg) (sumDomain_of_memLp_right hh)
  rw [highPart_add_lowPart] at hadd
  apply (distribution_le_add hadd t).trans
  exact add_le_add
    (distribution_le_of_endpointEstimate hg.aestronglyMeasurable hr₀ (hw₀ _ hg) (half_pos ht))
    (distribution_le_of_endpointEstimate hh.aestronglyMeasurable
      (hr₀.trans_le (h₀.trans h₁)) (hw₁ _ hh) (half_pos ht))

/-- The strong infinity hypothesis bounds output moduli a.e. The inequality
uses the essential supremum, so pointwise bounded representatives are unnecessary. -/
theorem ae_norm_le_of_endpointEstimate_top {μ : Measure X} {ν : Measure Y}
    {f : X → E} {g : Y → F} (hg : AEStronglyMeasurable g ν)
    {C : ℝ≥0} (hw : endpointEstimate μ ν ∞ C f g)
    {a : ℝ} (ha : 0 ≤ a) (hf : eLpNorm f ∞ μ ≤ ENNReal.ofReal a) :
    ∀ᵐ y ∂ν, ‖g y‖ ≤ (C : ℝ) * a := by
  have hw' : eLpNorm g ∞ ν ≤ (C : ℝ≥0∞) * eLpNorm f ∞ μ := by
    simpa only [endpointEstimate, ↓reduceIte] using hw
  filter_upwards [enorm_ae_le_eLpNormEssSup g ν] with y hy
  have h : ‖g y‖ₑ ≤ (C : ℝ≥0∞) * ENNReal.ofReal a := by
    exact hy.trans ((eLpNorm_exponent_top hg).symm.le.trans
      (hw'.trans (mul_le_mul_right hf _)))
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (show 0 ≤ (C : ℝ) from C.2),
    ← ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg C.2 ha)).1 h

/-- Infinity-endpoint level-set estimate. Taking
`a = t / (2 * (C₁ + 1))` always meets the last numerical condition, even
when the given supremum bound is zero. -/
theorem distribution_truncation_bound_top
    {𝕜 : Type*} [RCLike 𝕜] (μ : Measure X) (ν : Measure Y)
    {r₀ p a t : ℝ} (hr₀ : 0 < r₀) (h₀ : r₀ ≤ p)
    (ha : 0 < a) (ht : 0 < t) {C₀ C₁ : ℝ≥0}
    (T : (X → 𝕜) → Y → 𝕜)
    (hs : SublinearOn μ ν (sumDomain μ (ENNReal.ofReal r₀) ∞) T)
    (hw₀ : endpointBound μ ν (ENNReal.ofReal r₀) C₀ T)
    (hw₁ : endpointBound μ ν ∞ C₁ T)
    (hsmall : (C₁ : ℝ) * a ≤ t / 2)
    {f : X → 𝕜} (hf : MemLp f (ENNReal.ofReal p) μ) :
    distribution ν (T f) t ≤
      ENNReal.ofReal (t / 2) ^ (-r₀) * (C₀ : ℝ≥0∞) ^ r₀ *
        (∫⁻ x, ‖highPart a f x‖ₑ ^ r₀ ∂μ) := by
  have hg := highPart_memLp ha hr₀ h₀ hf
  have hlow := lowPart_eLpNorm_top_le hf.aestronglyMeasurable ha.le
  have hh : MemLp (lowPart a f) ∞ μ := hlow.trans_lt ENNReal.ofReal_lt_top
  have hDg : sumDomain μ (ENNReal.ofReal r₀) ∞ (highPart a f) := sumDomain_of_memLp_left hg
  have hDh : sumDomain μ (ENNReal.ofReal r₀) ∞ (lowPart a f) := sumDomain_of_memLp_right hh
  have hadd := hs.add_le (highPart a f) (lowPart a f) hDg hDh
  rw [highPart_add_lowPart] at hadd
  have hlowImage := ae_norm_le_of_endpointEstimate_top
    (hs.measurable _ hDh) (hw₁ _ hh) ha.le hlow
  apply (distribution_le_of_low_bound hadd (hlowImage.mono fun _ hy => hy.trans hsmall)).trans
  exact distribution_le_of_endpointEstimate hg.aestronglyMeasurable hr₀
    (hw₀ _ hg) (half_pos ht)

/-- Exact conversion to the restricted moment, used in Tonelli's computation. -/
theorem highPart_moment_eq {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x, ‖highPart a f x‖ₑ ^ r ∂μ) =
      ∫⁻ x in {x | a < ‖f x‖}, ‖f x‖ₑ ^ r ∂μ := by
  classical
  rw [← lintegral_indicator₀ (nullMeasurableSet_lt aemeasurable_const hf.norm.aemeasurable)]
  apply lintegral_congr
  intro x
  by_cases hx : a < ‖f x‖ <;> simp [highPart, hx, ENNReal.zero_rpow_of_pos hr]

theorem lowPart_moment_eq {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x, ‖lowPart a f x‖ₑ ^ r ∂μ) =
      ∫⁻ x in {x | ‖f x‖ ≤ a}, ‖f x‖ₑ ^ r ∂μ := by
  classical
  rw [← lintegral_indicator₀ (nullMeasurableSet_le hf.norm.aemeasurable aemeasurable_const)]
  apply lintegral_congr
  intro x
  by_cases hx : a < ‖f x‖
  · simp [lowPart, hx, not_le_of_gt hx, ENNReal.zero_rpow_of_pos hr]
  · simp [lowPart, hx, le_of_not_gt hx]

/-- The full endpoint intersection is dense at every finite intermediate
exponent. This holds for arbitrary endpoint exponents and arbitrary measures. -/
theorem intersectionCore_dense {𝕜 : Type*} [RCLike 𝕜] (μ : Measure X)
    (p₀ p₁ p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (hptop : p ≠ ∞) :
    Dense (intersectionCore (𝕜 := 𝕜) μ p₀ p₁ p : Set (Lp 𝕜 p μ)) := by
  apply (Lp.simpleFunc.dense (E := 𝕜) (μ := μ) hptop).mono
  intro f hf
  let fs : Lp.simpleFunc 𝕜 p μ := ⟨f, hf⟩
  have hpzero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp) hp.out)
  have hfin := (SimpleFunc.memLp_iff hpzero hptop).1 (Lp.simpleFunc.memLp fs)
  constructor
  · exact (memLp_congr_ae (Lp.simpleFunc.toSimpleFunc_eq_toFun fs)).1
      (SimpleFunc.memLp_of_finite_measure_preimage p₀ hfin)
  · exact (memLp_congr_ae (Lp.simpleFunc.toSimpleFunc_eq_toFun fs)).1
      (SimpleFunc.memLp_of_finite_measure_preimage p₁ hfin)

/-- The completion step, separated from the analytic interpolation estimate.
Its premise is the strong bound on the intersection; weak bounds are not
silently promoted to strong bounds here. -/
theorem extend_from_intersection_of_bound
    {𝕜 : Type*} [RCLike 𝕜] (μ : Measure X) (ν : Measure Y)
    (p₀ p₁ p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ∞) (C : ℝ≥0)
    (T : intersectionCore μ p₀ p₁ p →ₗ[𝕜] (Y → 𝕜))
    (hb : ∀ f, MemLp (T f) p ν ∧
      eLpNorm (T f) p ν ≤ (C : ℝ≥0∞) * eLpNorm (f.1 : X → 𝕜) p μ) :
    ∃! S : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p ν,
      ‖S‖ ≤ (C : ℝ) ∧ ∀ f, (S f.1 : Y → 𝕜) =ᵐ[ν] T f := by
  let U : intersectionCore μ p₀ p₁ p →ₗ[𝕜] Lp 𝕜 p ν :=
    { toFun := fun f => (hb f).1.toLp (T f)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(hb (f + g)).1.coeFn_toLp,
          Lp.coeFn_add ((hb f).1.toLp (T f)) ((hb g).1.toLp (T g)),
          (hb f).1.coeFn_toLp, (hb g).1.coeFn_toLp] with y hsum hcoe hf hg
        rw [hsum, hcoe, Pi.add_apply, hf, hg, map_add, Pi.add_apply]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(hb (c • f)).1.coeFn_toLp,
          Lp.coeFn_smul c ((hb f).1.toLp (T f)), (hb f).1.coeFn_toLp] with y hcf hcoe hf
        simp only [RingHom.id_apply]
        rw [hcf, hcoe, Pi.smul_apply, hf, map_smul, Pi.smul_apply] }
  have hU : ∀ f, ‖U f‖ ≤ (C : ℝ) * ‖(intersectionCore μ p₀ p₁ p).subtype f‖ := by
    intro f
    change ‖(hb f).1.toLp (T f)‖ ≤ (C : ℝ) * ‖f.1‖
    rw [Lp.norm_toLp]
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.memLp f.1).ne) (hb f).2
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, Lp.norm_def] using h
  have hd : DenseRange (intersectionCore (𝕜 := 𝕜) μ p₀ p₁ p).subtype :=
    (intersectionCore_dense μ p₀ p₁ p hptop).denseRange_val
  let S := U.extendOfNorm (intersectionCore μ p₀ p₁ p).subtype
  have hS : ∀ f, S f.1 = U f :=
    LinearMap.extendOfNorm_eq hd ⟨(C : ℝ), hU⟩
  refine ⟨S, ⟨LinearMap.opNorm_extendOfNorm_le hd C.2 hU, ?_⟩, ?_⟩
  · intro f
    rw [hS f]
    exact (hb f).1.coeFn_toLp
  · intro S' hS'
    have hcomp : S'.toLinearMap.comp (intersectionCore μ p₀ p₁ p).subtype = U := by
      apply LinearMap.ext
      intro f
      apply Lp.ext
      exact (hS'.2 f).trans (hb f).1.coeFn_toLp.symm
    exact (LinearMap.extendOfNorm_unique hd (C : ℝ) hU S' hcomp).symm

/-- A finite bound on pth moments yields both output membership and the norm bound. -/
theorem memLp_and_eLpNorm_le_of_moment_bound
    {μ : Measure X} {ν : Measure Y} {f : X → E} {g : Y → F}
    {p : ℝ} (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : AEStronglyMeasurable g ν) (A : ℝ≥0)
    (hb : (∫⁻ y, ‖g y‖ₑ ^ p ∂ν) ≤ (A : ℝ≥0∞) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :
    MemLp g (ENNReal.ofReal p) ν ∧
      eLpNorm g (ENNReal.ofReal p) ν ≤
        ((A ^ (1 / p) : ℝ≥0) : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) μ := by
  have hfm : (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) < ∞ := by
    rw [← eLpNorm_ofReal_rpow hf.aestronglyMeasurable hp]
    exact ENNReal.rpow_lt_top_of_nonneg hp.le hf.ne
  have hgm : (∫⁻ y, ‖g y‖ₑ ^ p ∂ν) < ∞ :=
    hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hfm)
  have hmem : MemLp g (ENNReal.ofReal p) ν := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by positivity) ENNReal.ofReal_ne_top hg).2
    simpa only [ENNReal.toReal_ofReal hp.le] using hgm
  refine ⟨hmem, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hg,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, ENNReal.coe_rpow_of_nonneg _ (by positivity)]
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ 1 / p by positivity)] using
    ENNReal.rpow_le_rpow hb (show 0 ≤ 1 / p by positivity)

/-- Normalize the level weight in a powered endpoint distribution estimate. -/
theorem truncation_weight_identity {p r t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) * ENNReal.ofReal (t / 2) ^ (-r) =
      ENNReal.ofReal ((2 : ℝ) ^ r) * ENNReal.ofReal (t ^ (p - r - 1)) := by
  rw [ENNReal.ofReal_rpow_of_pos (half_pos ht),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  congr 1
  rw [Real.div_rpow ht.le (by norm_num), Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ)),
    div_inv_eq_mul, ← mul_assoc, ← Real.rpow_add ht]
  rw [show p - 1 + -r = p - r - 1 by ring]
  exact mul_comm _ _

/-- Restricted moments vary monotonically with the truncation threshold. -/
theorem highPart_moment_antitone {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) {r : ℝ} (hr : 0 < r) :
    Antitone (fun a : ℝ => ∫⁻ x, ‖highPart a f x‖ₑ ^ r ∂μ) := by
  intro a b hab
  dsimp only
  rw [highPart_moment_eq hf a hr, highPart_moment_eq hf b hr]
  exact lintegral_mono_set (fun x hx => lt_of_le_of_lt hab hx)

theorem lowPart_moment_monotone {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) {r : ℝ} (hr : 0 < r) :
    Monotone (fun a : ℝ => ∫⁻ x, ‖lowPart a f x‖ₑ ^ r ∂μ) := by
  intro a b hab
  dsimp only
  rw [lowPart_moment_eq hf a hr, lowPart_moment_eq hf b hr]
  exact lintegral_mono_set (fun x hx => le_trans hx hab)

/-- Integrate a single powered distribution contribution. -/
theorem lintegral_truncation_weight (p r : ℝ) (hr : 0 < r) (C : ℝ≥0) (H : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - 1)) *
      (ENNReal.ofReal (t / 2) ^ (-r) * (C : ℝ≥0∞) ^ r * H t)) =
      (ENNReal.ofReal ((2 : ℝ) ^ r) * (C : ℝ≥0∞) ^ r) *
        ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - r - 1)) * H t := by
  have hc : ENNReal.ofReal ((2 : ℝ) ^ r) * (C : ℝ≥0∞) ^ r ≠ ∞ := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.coe_ne_top
  rw [← lintegral_const_mul' _ _ hc]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  calc
    _ = (ENNReal.ofReal (t ^ (p - 1)) * ENNReal.ofReal (t / 2) ^ (-r)) *
        ((C : ℝ≥0∞) ^ r * H t) := by ring
    _ = _ := by rw [truncation_weight_identity ht]; ring

/-- Layer cake plus a two-term level estimate, prior to evaluating truncation kernels. -/
theorem moment_le_of_distribution_truncation_bound
    {ν : Measure Y} {g : Y → F} {p r₀ r₁ : ℝ}
    (hp : 0 < p) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hg : AEStronglyMeasurable g ν) (C₀ C₁ : ℝ≥0)
    (H L : ℝ → ℝ≥0∞) (hH : Measurable H)
    (hd : ∀ t : ℝ, 0 < t → distribution ν g t ≤
      ENNReal.ofReal (t / 2) ^ (-r₀) * (C₀ : ℝ≥0∞) ^ r₀ * H t +
      ENNReal.ofReal (t / 2) ^ (-r₁) * (C₁ : ℝ≥0∞) ^ r₁ * L t) :
    (∫⁻ y, ‖g y‖ₑ ^ p ∂ν) ≤ ENNReal.ofReal p *
      ((ENNReal.ofReal ((2 : ℝ) ^ r₀) * (C₀ : ℝ≥0∞) ^ r₀) *
          (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - r₀ - 1)) * H t) +
        (ENNReal.ofReal ((2 : ℝ) ^ r₁) * (C₁ : ℝ≥0∞) ^ r₁) *
          (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - r₁ - 1)) * L t)) := by
  rw [moment_layercake ν hg hp]
  apply mul_le_mul_right _ _
  calc
    _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - 1)) *
        (ENNReal.ofReal (t / 2) ^ (-r₀) * (C₀ : ℝ≥0∞) ^ r₀ * H t +
         ENNReal.ofReal (t / 2) ^ (-r₁) * (C₁ : ℝ≥0∞) ^ r₁ * L t) := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      simpa only [mul_comm] using mul_le_mul_right (hd t ht) (ENNReal.ofReal (t ^ (p - 1)))
    _ = _ := by
      simp_rw [mul_add]
      rw [lintegral_add_left]
      · rw [lintegral_truncation_weight p r₀ hr₀, lintegral_truncation_weight p r₁ hr₁]
      · exact ((measurable_id.pow_const _).ennreal_ofReal).mul
          ((((measurable_id.div_const 2).ennreal_ofReal.pow_const _).mul_const _).mul hH)

/-- The infinity endpoint has only the high-level contribution. -/
theorem moment_le_of_distribution_truncation_bound_top
    {ν : Measure Y} {g : Y → F} {p r : ℝ}
    (hp : 0 < p) (hr : 0 < r)
    (hg : AEStronglyMeasurable g ν) (C : ℝ≥0) (H : ℝ → ℝ≥0∞)
    (hd : ∀ t : ℝ, 0 < t → distribution ν g t ≤
      ENNReal.ofReal (t / 2) ^ (-r) * (C : ℝ≥0∞) ^ r * H t) :
    (∫⁻ y, ‖g y‖ₑ ^ p ∂ν) ≤ ENNReal.ofReal p *
      ((ENNReal.ofReal ((2 : ℝ) ^ r) * (C : ℝ≥0∞) ^ r) *
        ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - r - 1)) * H t) := by
  rw [moment_layercake ν hg hp]
  apply mul_le_mul_right _ _
  calc
    _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - 1)) *
        (ENNReal.ofReal (t / 2) ^ (-r) * (C : ℝ≥0∞) ^ r * H t) := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      simpa only [mul_comm] using mul_le_mul_right (hd t ht) (ENNReal.ofReal (t ^ (p - 1)))
    _ = _ := lintegral_truncation_weight p r hr C H


lemma high_moment_pointwise {a c r p : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hr : 0 < r) (hrp : r < p) :
    ENNReal.ofReal (a ^ r) * ENNReal.ofReal ((a / c) ^ (p-r)) =
      ENNReal.ofReal (c ^ (r-p)) * ENNReal.ofReal (a ^ p) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha r),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le (r-p))]
  congr 1
  rw [Real.div_rpow ha hc.le, ← mul_div_assoc,
    ← Real.rpow_add_of_nonneg ha hr.le (sub_pos.mpr hrp).le]
  have he : r + (p-r) = p := by ring
  rw [he, show r-p = -(p-r) by ring, Real.rpow_neg hc.le]
  ring

lemma high_moment_integral {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) {r p c : ℝ}
    (hr : 0 < r) (hrp : r < p) (hc : 0 < c) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p-r-1)) *
      ∫⁻ x in {x | c*t < ‖f x‖}, ‖f x‖ₑ ^ r ∂μ) =
      ENNReal.ofReal (c ^ (r-p) / (p-r)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  let ν := μ.withDensity (fun x => ‖f x‖ₑ ^ r)
  have hfm : AEMeasurable (fun x => ‖f x‖ / c) μ := hf.norm.aemeasurable.div_const c
  have hfmν : AEMeasurable (fun x => ‖f x‖ / c) ν :=
    hfm.mono_ac (withDensity_absolutelyContinuous μ _)
  have hnonneg : 0 ≤ᵐ[ν] (fun x => ‖f x‖ / c) :=
    Eventually.of_forall (fun x => div_nonneg (norm_nonneg _) hc.le)
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul ν hnonneg hfmν (sub_pos.mpr hrp)
  have hdist : ∀ t : ℝ, ν {x | t < ‖f x‖ / c} =
      ∫⁻ x in {x | c*t < ‖f x‖}, ‖f x‖ₑ ^ r ∂μ := by
    intro t
    have hset : {x | t < ‖f x‖ / c} = {x | c*t < ‖f x‖} := by
      ext x
      simp only [mem_ofPred_eq, lt_div_iff₀ hc]
      rw [mul_comm t c]
    rw [hset]
    exact withDensity_apply₀ _
      (nullMeasurableSet_lt aemeasurable_const hf.norm.aemeasurable)
  simp_rw [hdist, mul_comm (∫⁻ x in {x | c * _ < ‖f x‖}, ‖f x‖ₑ ^ r ∂μ)] at h
  have hleft : (∫⁻ x, ENNReal.ofReal ((‖f x‖ / c) ^ (p-r)) ∂ν) =
      ENNReal.ofReal (c ^ (r-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul₀
      (hf.enorm.pow_const r) (hfm.pow_const (p-r)).ennreal_ofReal]
    simp only [Pi.mul_apply]
    simp_rw [← ofReal_norm]
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le]
    have hp : 0 ≤ p := hr.le.trans hrp.le
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp,
      high_moment_pointwise (norm_nonneg _) hc hr hrp]
    exact lintegral_const_mul'' _ ((hf.norm.aemeasurable.pow_const p).ennreal_ofReal)
  rw [hleft] at h
  have hq : ENNReal.ofReal (p-r) ≠ 0 := by positivity
  have hqtop : ENNReal.ofReal (p-r) ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    _ = (ENNReal.ofReal (p-r))⁻¹ *
      (ENNReal.ofReal (p-r) * ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p-r-1)) *
        ∫⁻ x in {x | c*t < ‖f x‖}, ‖f x‖ₑ ^ r ∂μ) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hq hqtop, one_mul]
    _ = _ := by
      rw [← h, ← mul_assoc]
      congr 1
      rw [← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hrp),
        ← ENNReal.ofReal_mul (inv_nonneg.mpr (sub_pos.mpr hrp).le)]
      congr 1
      ring

lemma low_moment_tail_integral {p r a : ℝ} (hpr : p < r) (ha : 0 < a) :
  (∫⁻ t in Ici a, ENNReal.ofReal (t ^ (p-r-1))) =
    ENNReal.ofReal (a ^ (p-r) / (r-p)) := by
  rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  have hint := integrableOn_Ioi_rpow_of_lt (show p-r-1 < -1 by linarith) ha
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi a)] fun t : ℝ => t ^ (p-r-1) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (ha.le.trans (le_of_lt ht)) _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnon]
  rw [integral_Ioi_rpow_of_lt (show p-r-1 < -1 by linarith) ha]
  congr 1
  have he : p-r-1+1 = p-r := by ring
  rw [he]
  rw [show r-p = -(p-r) by ring, div_neg]
  ring

lemma low_moment_scalar_kernel {p r c a : ℝ} (hpr : p < r) (hc : 0 < c) (ha : 0 ≤ a) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p-r-1)) *
      ({t : ℝ | a ≤ c*t}.indicator (fun _ => ENNReal.ofReal (a ^ (r-p))) t)) ≤
      ENNReal.ofReal (c ^ (r-p) / (r-p)) := by
  classical
  by_cases haz : a = 0
  · simp [haz, Real.zero_rpow (sub_pos.mpr hpr).ne']
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hac : 0 < a/c := div_pos hap hc
  have hset : {t : ℝ | a ≤ c*t} = Ici (a/c) := by
    ext t
    simp only [mem_ofPred_eq, mem_Ici, div_le_iff₀ hc]
    rw [mul_comm t c]
  rw [hset]
  have hind : (fun t : ℝ => ENNReal.ofReal (t ^ (p-r-1)) *
      ((Ici (a/c)).indicator (fun _ => ENNReal.ofReal (a ^ (r-p))) t)) =
      (Ici (a/c)).indicator (fun t => ENNReal.ofReal (t ^ (p-r-1)) *
        ENNReal.ofReal (a ^ (r-p))) := by
    funext t
    rw [indicator_mul_right]
  rw [hind]
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  rw [inter_eq_left.mpr (show Ici (a/c) ⊆ Ioi 0 from fun t ht => hac.trans_le ht)]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, low_moment_tail_integral hpr hac]
  apply le_of_eq
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hac.le _) (sub_pos.mpr hpr).le)]
  congr 1
  rw [Real.div_rpow ha hc.le]
  rw [show p-r = -(r-p) by ring, Real.rpow_neg ha, Real.rpow_neg hc.le]
  have han := (Real.rpow_pos_of_pos hap (r-p)).ne'
  have hcn := (Real.rpow_pos_of_pos hc (r-p)).ne'
  field_simp


lemma low_moment_integral_measurable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {g : X → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    {p r c : ℝ} (hp : 0 < p) (hpr : p < r) (hc : 0 < c)
    (hfin : (∫⁻ x, ENNReal.ofReal (g x ^ p) ∂μ) ≠ ∞) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p-r-1)) *
      ∫⁻ x in {x | g x ≤ c*t}, ENNReal.ofReal (g x ^ r) ∂μ) ≤
    ENNReal.ofReal (c ^ (r-p) / (r-p)) * ∫⁻ x, ENNReal.ofReal (g x ^ p) ∂μ := by
  classical
  let ν := μ.withDensity (fun x => ENNReal.ofReal (g x ^ p))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfin
  let k : ℝ → X → ℝ≥0∞ := fun t x => ENNReal.ofReal (t ^ (p-r-1)) *
    ({x | g x ≤ c*t}.indicator (fun x => ENNReal.ofReal (g x ^ (r-p))) x)
  have hm : Measurable (Function.uncurry k) := by
    apply Measurable.mul
    · exact (measurable_fst.pow_const _).ennreal_ofReal
    · exact ((hg.comp measurable_snd).pow_const _).ennreal_ofReal.indicator
        (measurableSet_le (hg.comp measurable_snd) (measurable_const.mul measurable_fst))
  have hs (t : ℝ) : MeasurableSet {x | g x ≤ c*t} :=
    measurableSet_le hg measurable_const
  have hv (t : ℝ) :
      (∫⁻ x in {x | g x ≤ c*t}, ENNReal.ofReal (g x ^ (r-p)) ∂ν) =
      ∫⁻ x in {x | g x ≤ c*t}, ENNReal.ofReal (g x ^ r) ∂μ := by
    rw [setLIntegral_withDensity_eq_setLIntegral_mul μ
      (hg.pow_const p).ennreal_ofReal (hg.pow_const (r-p)).ennreal_ofReal
      (hs t)]
    apply lintegral_congr
    intro x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hg0 x) _),
      ← Real.rpow_add_of_nonneg (hg0 x) hp.le (sub_pos.mpr hpr).le]
    congr 2
    ring
  calc
    _ = ∫⁻ t in Ioi 0, ∫⁻ x, k t x ∂ν := by
      apply lintegral_congr
      intro t
      dsimp [k]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_indicator (hs t), hv]
    _ = ∫⁻ x, ∫⁻ t in Ioi 0, k t x ∂volume ∂ν := lintegral_lintegral_swap hm.aemeasurable
    _ ≤ ∫⁻ x, ENNReal.ofReal (c ^ (r-p) / (r-p)) ∂ν := by
      apply lintegral_mono
      intro x
      exact low_moment_scalar_kernel hpr hc (hg0 x)
    _ = _ := by
      rw [lintegral_const]
      dsimp [ν]
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

lemma low_moment_integral_le {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {f : X → E} {p r c : ℝ}
    (hp : 0 < p) (hpr : p < r) (hc : 0 < c)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p-r-1)) *
      ∫⁻ x in {x | ‖f x‖ ≤ c*t}, ‖f x‖ₑ ^ r ∂μ) ≤
    ENNReal.ofReal (c ^ (r-p) / (r-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  let f' := hf.aestronglyMeasurable.mk f
  have hff : f =ᵐ[μ] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hfm : StronglyMeasurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hfp : MemLp f' (ENNReal.ofReal p) μ := (memLp_congr_ae hff).1 hf
  have hpow (a : ℝ) (ha : 0 ≤ a) (x : X) : ‖f' x‖ₑ ^ a = ENNReal.ofReal (‖f' x‖ ^ a) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ha]
  have hfin : (∫⁻ x, ENNReal.ofReal (‖f' x‖ ^ p) ∂μ) ≠ ∞ := by
    simp_rw [← hpow p hp.le]
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (show ENNReal.ofReal p ≠ 0 by positivity) ENNReal.ofReal_ne_top hfp
    simpa [ENNReal.toReal_ofReal hp.le] using h.ne
  have h := low_moment_integral_measurable μ hfm.norm.measurable (fun x => norm_nonneg (f' x))
    hp hpr hc hfin
  simp_rw [← hpow r (hp.trans hpr).le, ← hpow p hp.le] at h
  have hmoment (a : ℝ) : (∫⁻ x, ‖f x‖ₑ ^ a ∂μ) = ∫⁻ x, ‖f' x‖ₑ ^ a ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hff] with x hx
    rw [hx]
  rw [hmoment p]
  convert h using 1
  apply lintegral_congr
  intro t
  congr 1
  rw [← lintegral_indicator₀ (nullMeasurableSet_le hf.aestronglyMeasurable.norm.aemeasurable aemeasurable_const),
    ← lintegral_indicator (measurableSet_le hfm.norm.measurable measurable_const)]
  apply lintegral_congr_ae
  filter_upwards [hff] with x hx
  simp only [indicator_apply, mem_ofPred_eq, hx]

section LinearTruncation
/-- Truncation preserves membership in every endpoint space already containing the input. -/
theorem highPart_memLp_of_memLp {E : Type*} [NormedAddCommGroup E]
    {μ : Measure X} {f : X → E} {q : ℝ≥0∞} (hf : MemLp f q μ) (a : ℝ) :
    MemLp (highPart a f) q μ := by
  exact hf.indicator (nullMeasurableSet_lt aemeasurable_const hf.aestronglyMeasurable.norm.aemeasurable)

theorem lowPart_memLp_of_memLp {E : Type*} [NormedAddCommGroup E]
    {μ : Measure X} {f : X → E} {q : ℝ≥0∞} (hf : MemLp f q μ) (a : ℝ) :
    MemLp (lowPart a f) q μ := by
  exact hf.indicator (nullMeasurableSet_lt aemeasurable_const hf.aestronglyMeasurable.norm.aemeasurable).compl

variable {𝕜 : Type*} [RCLike 𝕜]

def intersectionCoreHighPart (μ : Measure X) (p₀ p₁ p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : ℝ) (f : intersectionCore (𝕜 := 𝕜) μ p₀ p₁ p) :
    intersectionCore (𝕜 := 𝕜) μ p₀ p₁ p :=
  let hg := highPart_memLp_of_memLp (Lp.memLp f.1) a
  ⟨hg.toLp (highPart a (f.1 : X → 𝕜)),
    (memLp_congr_ae hg.coeFn_toLp).2 (highPart_memLp_of_memLp f.2.1 a),
    (memLp_congr_ae hg.coeFn_toLp).2 (highPart_memLp_of_memLp f.2.2 a)⟩

def intersectionCoreLowPart (μ : Measure X) (p₀ p₁ p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : ℝ) (f : intersectionCore (𝕜 := 𝕜) μ p₀ p₁ p) :
    intersectionCore (𝕜 := 𝕜) μ p₀ p₁ p :=
  let hh := lowPart_memLp_of_memLp (Lp.memLp f.1) a
  ⟨hh.toLp (lowPart a (f.1 : X → 𝕜)),
    (memLp_congr_ae hh.coeFn_toLp).2 (lowPart_memLp_of_memLp f.2.1 a),
    (memLp_congr_ae hh.coeFn_toLp).2 (lowPart_memLp_of_memLp f.2.2 a)⟩

theorem intersectionCoreHighPart_coeFn (μ : Measure X) (p₀ p₁ p : ℝ≥0∞)
    [Fact (1 ≤ p)] (a : ℝ) (f : intersectionCore (𝕜 := 𝕜) μ p₀ p₁ p) :
    ((intersectionCoreHighPart μ p₀ p₁ p a f).1 : X → 𝕜) =ᵐ[μ]
      highPart a (f.1 : X → 𝕜) :=
  (highPart_memLp_of_memLp (Lp.memLp f.1) a).coeFn_toLp

theorem intersectionCoreLowPart_coeFn (μ : Measure X) (p₀ p₁ p : ℝ≥0∞)
    [Fact (1 ≤ p)] (a : ℝ) (f : intersectionCore (𝕜 := 𝕜) μ p₀ p₁ p) :
    ((intersectionCoreLowPart μ p₀ p₁ p a f).1 : X → 𝕜) =ᵐ[μ]
      lowPart a (f.1 : X → 𝕜) :=
  (lowPart_memLp_of_memLp (Lp.memLp f.1) a).coeFn_toLp

theorem intersectionCoreHighPart_add_lowPart (μ : Measure X) (p₀ p₁ p : ℝ≥0∞)
    [Fact (1 ≤ p)] (a : ℝ) (f : intersectionCore (𝕜 := 𝕜) μ p₀ p₁ p) :
    intersectionCoreHighPart μ p₀ p₁ p a f + intersectionCoreLowPart μ p₀ p₁ p a f = f := by
  apply Subtype.ext
  apply Lp.ext
  have h := (intersectionCoreHighPart_coeFn μ p₀ p₁ p a f).add
    (intersectionCoreLowPart_coeFn μ p₀ p₁ p a f)
  exact (Lp.coeFn_add _ _).trans (h.trans (Eventually.of_forall
    (congrFun (highPart_add_lowPart a (f.1 : X → 𝕜)))))

/-- The finite-endpoint level estimate for a linear map initially defined only on
its full endpoint intersection. No extension of that map is assumed. -/
theorem distribution_truncation_bound_linear
    (μ : Measure X) (ν : Measure Y) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {r₀ r₁ a t : ℝ} (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (ht : 0 < t)
    {C₀ C₁ : ℝ≥0}
    (T : intersectionCore μ (ENNReal.ofReal r₀) (ENNReal.ofReal r₁) p →ₗ[𝕜] (Y → 𝕜))
    (hw₀ : ∀ f, endpointEstimate μ ν (ENNReal.ofReal r₀) C₀ (f.1 : X → 𝕜) (T f))
    (hw₁ : ∀ f, endpointEstimate μ ν (ENNReal.ofReal r₁) C₁ (f.1 : X → 𝕜) (T f))
    (f : intersectionCore μ (ENNReal.ofReal r₀) (ENNReal.ofReal r₁) p) :
    distribution ν (T f) t ≤
      ENNReal.ofReal (t / 2) ^ (-r₀) * (C₀ : ℝ≥0∞) ^ r₀ *
        (∫⁻ x, ‖highPart a (f.1 : X → 𝕜) x‖ₑ ^ r₀ ∂μ) +
      ENNReal.ofReal (t / 2) ^ (-r₁) * (C₁ : ℝ≥0∞) ^ r₁ *
        (∫⁻ x, ‖lowPart a (f.1 : X → 𝕜) x‖ₑ ^ r₁ ∂μ) := by
  let g := intersectionCoreHighPart μ (ENNReal.ofReal r₀) (ENNReal.ofReal r₁) p a f
  let h := intersectionCoreLowPart μ (ENNReal.ofReal r₀) (ENNReal.ofReal r₁) p a f
  have hsplit : T f = T g + T h := by
    rw [← map_add]
    rw [intersectionCoreHighPart_add_lowPart]
  have hadd : ∀ᵐ y ∂ν, ‖T f y‖ ≤ ‖T g y‖ + ‖T h y‖ := by
    apply Eventually.of_forall
    intro y
    rw [hsplit]
    exact norm_add_le _ _
  have hg := distribution_le_of_endpointEstimate (Lp.memLp g.1).aestronglyMeasurable
    hr₀ (hw₀ g) (half_pos ht)
  have hh := distribution_le_of_endpointEstimate (Lp.memLp h.1).aestronglyMeasurable
    hr₁ (hw₁ h) (half_pos ht)
  have hgm : (∫⁻ x, ‖(g.1 : X → 𝕜) x‖ₑ ^ r₀ ∂μ) =
      ∫⁻ x, ‖highPart a (f.1 : X → 𝕜) x‖ₑ ^ r₀ ∂μ := by
    apply lintegral_congr_ae
    exact (intersectionCoreHighPart_coeFn μ (ENNReal.ofReal r₀)
      (ENNReal.ofReal r₁) p a f).fun_comp (fun z => ‖z‖ₑ ^ r₀)
  have hhm : (∫⁻ x, ‖(h.1 : X → 𝕜) x‖ₑ ^ r₁ ∂μ) =
      ∫⁻ x, ‖lowPart a (f.1 : X → 𝕜) x‖ₑ ^ r₁ ∂μ := by
    apply lintegral_congr_ae
    exact (intersectionCoreLowPart_coeFn μ (ENNReal.ofReal r₀)
      (ENNReal.ofReal r₁) p a f).fun_comp (fun z => ‖z‖ₑ ^ r₁)
  rw [hgm] at hg
  rw [hhm] at hh
  exact (distribution_le_add hadd t).trans (add_le_add hg hh)

/-- The same truncation argument for a strong supremum upper endpoint. -/
theorem distribution_truncation_bound_top_linear
    (μ : Measure X) (ν : Measure Y) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {r₀ a t : ℝ} (hr₀ : 0 < r₀) (ha : 0 ≤ a) (ht : 0 < t)
    {C₀ C₁ : ℝ≥0}
    (T : intersectionCore μ (ENNReal.ofReal r₀) ∞ p →ₗ[𝕜] (Y → 𝕜))
    (hmeas : ∀ f, AEStronglyMeasurable (T f) ν)
    (hw₀ : ∀ f, endpointEstimate μ ν (ENNReal.ofReal r₀) C₀ (f.1 : X → 𝕜) (T f))
    (hw₁ : ∀ f, endpointEstimate μ ν ∞ C₁ (f.1 : X → 𝕜) (T f))
    (hsmall : (C₁ : ℝ) * a ≤ t / 2)
    (f : intersectionCore μ (ENNReal.ofReal r₀) ∞ p) :
    distribution ν (T f) t ≤
      ENNReal.ofReal (t / 2) ^ (-r₀) * (C₀ : ℝ≥0∞) ^ r₀ *
        (∫⁻ x, ‖highPart a (f.1 : X → 𝕜) x‖ₑ ^ r₀ ∂μ) := by
  let g := intersectionCoreHighPart μ (ENNReal.ofReal r₀) ∞ p a f
  let h := intersectionCoreLowPart μ (ENNReal.ofReal r₀) ∞ p a f
  have hsplit : T f = T g + T h := by
    rw [← map_add]
    rw [intersectionCoreHighPart_add_lowPart]
  have hadd : ∀ᵐ y ∂ν, ‖T f y‖ ≤ ‖T g y‖ + ‖T h y‖ := by
    apply Eventually.of_forall
    intro y
    rw [hsplit]
    exact norm_add_le _ _
  have hlow : eLpNorm (h.1 : X → 𝕜) ∞ μ ≤ ENNReal.ofReal a := by
    rw [eLpNorm_congr_ae (intersectionCoreLowPart_coeFn μ (ENNReal.ofReal r₀) ∞ p a f)]
    exact lowPart_eLpNorm_top_le (Lp.memLp f.1).aestronglyMeasurable ha
  have hlowImage := ae_norm_le_of_endpointEstimate_top (hmeas h) (hw₁ h) ha hlow
  have hg := distribution_le_of_endpointEstimate (Lp.memLp g.1).aestronglyMeasurable
    hr₀ (hw₀ g) (half_pos ht)
  have hgm : (∫⁻ x, ‖(g.1 : X → 𝕜) x‖ₑ ^ r₀ ∂μ) =
      ∫⁻ x, ‖highPart a (f.1 : X → 𝕜) x‖ₑ ^ r₀ ∂μ := by
    apply lintegral_congr_ae
    exact (intersectionCoreHighPart_coeFn μ (ENNReal.ofReal r₀) ∞ p a f).fun_comp
      (fun z => ‖z‖ₑ ^ r₀)
  rw [hgm] at hg
  exact (distribution_le_of_low_bound hadd
    (hlowImage.mono fun _ hy => hy.trans hsmall)).trans hg


end LinearTruncation

def finiteMomentConstant (r₀ r₁ p : ℝ) (C₀ C₁ : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal p *
    ((Real.toNNReal ((2:ℝ)^r₀) * C₀^r₀) * Real.toNNReal (1/(p-r₀)) +
     (Real.toNNReal ((2:ℝ)^r₁) * C₁^r₁) * Real.toNNReal (1/(r₁-p)))

def finiteInterpolationConstant (r₀ r₁ p : ℝ) (C₀ C₁ : ℝ≥0) : ℝ≥0 :=
  finiteMomentConstant r₀ r₁ p C₀ C₁ ^ (1/p)

lemma finiteMomentConstant_coe (r₀ r₁ p : ℝ) (C₀ C₁ : ℝ≥0)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    (finiteMomentConstant r₀ r₁ p C₀ C₁ : ℝ≥0∞) =
      ENNReal.ofReal p *
        ((ENNReal.ofReal ((2:ℝ)^r₀) * (C₀:ℝ≥0∞)^r₀) * ENNReal.ofReal (1/(p-r₀)) +
         (ENNReal.ofReal ((2:ℝ)^r₁) * (C₁:ℝ≥0∞)^r₁) * ENNReal.ofReal (1/(r₁-p))) := by
  simp only [finiteMomentConstant, ENNReal.coe_mul, ENNReal.coe_add,
    ENNReal.coe_rpow_of_nonneg _ hr₀.le, ENNReal.coe_rpow_of_nonneg _ hr₁.le,
    ENNReal.ofReal]

/-- Integrating the two truncated endpoint estimates yields a strong bound. -/
theorem strongType_of_distribution_truncation_bound
    {μ : Measure X} {ν : Measure Y} {f : X → E} {g : Y → F}
    {r₀ r₁ p : ℝ} (C₀ C₁ : ℝ≥0)
    (hr₀ : 0 < r₀) (h₀ : r₀ < p) (h₁ : p < r₁)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : AEStronglyMeasurable g ν)
    (hd : ∀ t : ℝ, 0 < t → distribution ν g t ≤
      ENNReal.ofReal (t / 2) ^ (-r₀) * (C₀ : ℝ≥0∞) ^ r₀ *
        (∫⁻ x, ‖highPart t f x‖ₑ ^ r₀ ∂μ) +
      ENNReal.ofReal (t / 2) ^ (-r₁) * (C₁ : ℝ≥0∞) ^ r₁ *
        (∫⁻ x, ‖lowPart t f x‖ₑ ^ r₁ ∂μ)) :
    MemLp g (ENNReal.ofReal p) ν ∧
      eLpNorm g (ENNReal.ofReal p) ν ≤
        (finiteInterpolationConstant r₀ r₁ p C₀ C₁ : ℝ≥0∞) *
          eLpNorm f (ENNReal.ofReal p) μ := by
  have hp := hr₀.trans h₀
  have hr₁ := hp.trans h₁
  apply memLp_and_eLpNorm_le_of_moment_bound hp hf hg
    (finiteMomentConstant r₀ r₁ p C₀ C₁)
  have h := moment_le_of_distribution_truncation_bound hp hr₀ hr₁ hg C₀ C₁
    (fun t => ∫⁻ x, ‖highPart t f x‖ₑ ^ r₀ ∂μ)
    (fun t => ∫⁻ x, ‖lowPart t f x‖ₑ ^ r₁ ∂μ)
    (highPart_moment_antitone hf.aestronglyMeasurable hr₀).measurable hd
  have hhigh : (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p-r₀-1)) *
      ∫⁻ x, ‖highPart t f x‖ₑ ^ r₀ ∂μ) =
      ENNReal.ofReal (1/(p-r₀)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    simp_rw [highPart_moment_eq hf.aestronglyMeasurable _ hr₀]
    simpa only [one_mul, Real.one_rpow] using
      high_moment_integral hf.aestronglyMeasurable hr₀ h₀ (c := 1) zero_lt_one
  have hlow : (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p-r₁-1)) *
      ∫⁻ x, ‖lowPart t f x‖ₑ ^ r₁ ∂μ) ≤
      ENNReal.ofReal (1/(r₁-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    simp_rw [lowPart_moment_eq hf.aestronglyMeasurable _ hr₁]
    simpa only [one_mul, Real.one_rpow] using
      low_moment_integral_le hp h₁ (c := 1) zero_lt_one hf
  rw [hhigh] at h
  apply h.trans
  rw [finiteMomentConstant_coe _ _ _ _ _ hr₀ hr₁]
  calc
    _ ≤ ENNReal.ofReal p *
      ((ENNReal.ofReal ((2:ℝ)^r₀) * (C₀:ℝ≥0∞)^r₀) *
        (ENNReal.ofReal (1/(p-r₀)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) +
       (ENNReal.ofReal ((2:ℝ)^r₁) * (C₁:ℝ≥0∞)^r₁) *
        (ENNReal.ofReal (1/(r₁-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ)) := by
      gcongr
    _ = _ := by ring


theorem marcinkiewicz_finite : MarcinkiewiczSpec.FiniteInterpolation.{u,v,w} := by
  intro r₀ r₁ p C₀ C₁ hr₀ h₀ h₁
  refine ⟨finiteInterpolationConstant r₀ r₁ p C₀ C₁, ?_⟩
  intro X Y 𝕜 _ _ _ μ ν T hs hw₀ hw₁ f hf
  have hr₀pos : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀
  apply strongType_of_distribution_truncation_bound C₀ C₁ hr₀pos h₀ h₁ hf
    (hs.measurable f (memLp_sumDomain hr₀pos h₀.le h₁.le hf))
  intro t ht
  exact distribution_truncation_bound μ ν hr₀pos h₀.le h₁.le ht ht T hs hw₀ hw₁ hf


/-- A positive truncation scale which also handles a zero supremum constant. -/
def infinityTruncationScale (C : ℝ≥0) : ℝ := 1 / (2 * ((C : ℝ) + 1))

theorem infinityTruncationScale_pos (C : ℝ≥0) : 0 < infinityTruncationScale C := by
  unfold infinityTruncationScale
  positivity

theorem infinityTruncationScale_small (C : ℝ≥0) {t : ℝ} (ht : 0 < t) :
    (C : ℝ) * (infinityTruncationScale C * t) ≤ t / 2 := by
  unfold infinityTruncationScale
  have hc : 0 < (C : ℝ) + 1 := by positivity
  have h : (C : ℝ) / ((C : ℝ) + 1) ≤ 1 := (div_le_one hc).2 (by linarith)
  have h' := mul_le_mul_of_nonneg_right h (show 0 ≤ t / 2 by positivity)
  calc
    _ = ((C : ℝ) / ((C : ℝ) + 1)) * (t / 2) := by
      field_simp
    _ ≤ _ := by simpa using h'

/-- Finite moment and norm constants for the strong supremum endpoint. -/
def infinityMomentConstant (r p : ℝ) (C₀ C₁ : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal p * ((Real.toNNReal ((2 : ℝ) ^ r) * C₀ ^ r) *
    Real.toNNReal ((infinityTruncationScale C₁) ^ (r-p) / (p-r)))

def infinityInterpolationConstant (r p : ℝ) (C₀ C₁ : ℝ≥0) : ℝ≥0 :=
  infinityMomentConstant r p C₀ C₁ ^ (1 / p)

/-- Analytic estimate for a single input-output pair at an infinity upper endpoint. -/
theorem strongType_of_distribution_truncation_bound_top
    {μ : Measure X} {ν : Measure Y} {f : X → E} {g : Y → F}
    {r p : ℝ} (hr : 0 < r) (hrp : r < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : AEStronglyMeasurable g ν)
    (C₀ C₁ : ℝ≥0)
    (hd : ∀ t : ℝ, 0 < t → distribution ν g t ≤
      ENNReal.ofReal (t / 2) ^ (-r) * (C₀ : ℝ≥0∞) ^ r *
        (∫⁻ x, ‖highPart (infinityTruncationScale C₁ * t) f x‖ₑ ^ r ∂μ)) :
    MemLp g (ENNReal.ofReal p) ν ∧
      eLpNorm g (ENNReal.ofReal p) ν ≤
        (infinityInterpolationConstant r p C₀ C₁ : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) μ := by
  have hp := hr.trans hrp
  apply memLp_and_eLpNorm_le_of_moment_bound hp hf hg (infinityMomentConstant r p C₀ C₁)
  have hm := moment_le_of_distribution_truncation_bound_top hp hr hg C₀ _ hd
  have hk := high_moment_integral hf.aestronglyMeasurable hr hrp (infinityTruncationScale_pos C₁)
  simp_rw [← highPart_moment_eq hf.aestronglyMeasurable _ hr] at hk
  rw [hk] at hm
  convert hm using 1
  simp only [infinityMomentConstant, ENNReal.coe_mul,
    ENNReal.coe_rpow_of_nonneg _ hr.le, ENNReal.ofReal, mul_assoc]

/-- Marcinkiewicz interpolation with a strong essential supremum upper endpoint. -/
theorem marcinkiewicz_infinity : MarcinkiewiczSpec.InfinityInterpolation.{u,v,w} := by
  intro r p C₀ C₁ hr1 hrp
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  refine ⟨infinityInterpolationConstant r p C₀ C₁, ?_⟩
  intro X Y 𝕜 _ _ _ μ ν T hs hw₀ hw₁ f hf
  apply strongType_of_distribution_truncation_bound_top hr hrp hf
    (hs.measurable f (memLp_sumDomain_top hr hrp.le hf)) C₀ C₁
  intro t ht
  exact distribution_truncation_bound_top μ ν hr hrp.le
    (mul_pos (infinityTruncationScale_pos C₁) ht) ht T hs hw₀ hw₁
    (infinityTruncationScale_small C₁ ht) hf


/-- Real coordinates for a finite lower endpoint and a strictly intermediate exponent. -/
theorem marcinkiewicz_exponent_coordinates
    (p₀ p₁ p : ℝ≥0∞) (hp₀ : 1 ≤ p₀) (h₀ : p₀ < p) (h₁ : p < p₁) :
    p₀ ≠ ∞ ∧ p ≠ ∞ ∧ 1 ≤ p₀.toReal ∧ p₀.toReal < p.toReal ∧
      ENNReal.ofReal p₀.toReal = p₀ ∧ ENNReal.ofReal p.toReal = p := by
  have hpTop : p ≠ ∞ := ne_top_of_lt h₁
  have hp₀Top : p₀ ≠ ∞ := ne_top_of_lt h₀
  refine ⟨hp₀Top, hpTop, ?_, ?_, ENNReal.ofReal_toReal hp₀Top, ENNReal.ofReal_toReal hpTop⟩
  · simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp₀Top).2 hp₀
  · exact (ENNReal.toReal_lt_toReal hp₀Top hpTop).2 h₀

/-- Reduction of the quotient extension conclusion to strong estimates on its
intersection, with real exponent coordinates. -/
theorem linearExtension_of_real_core_bounds
    (hfinite :
      ∀ (r₀ r₁ q : ℝ) (C₀ C₁ : ℝ≥0), 1 ≤ r₀ → r₀ < q → q < r₁ →
      ∃ K : ℝ≥0,
      ∀ {X : Type u} {Y : Type v} {𝕜 : Type w} [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
        (μ : Measure X) (ν : Measure Y) [Fact (1 ≤ ENNReal.ofReal q)]
        (T : intersectionCore μ (ENNReal.ofReal r₀) (ENNReal.ofReal r₁)
          (ENNReal.ofReal q) →ₗ[𝕜] (Y → 𝕜)),
        (∀ f, AEStronglyMeasurable (T f) ν) →
        (∀ f, endpointEstimate μ ν (ENNReal.ofReal r₀) C₀ (f.1 : X → 𝕜) (T f)) →
        (∀ f, endpointEstimate μ ν (ENNReal.ofReal r₁) C₁ (f.1 : X → 𝕜) (T f)) →
        ∀ f, MemLp (T f) (ENNReal.ofReal q) ν ∧
          eLpNorm (T f) (ENNReal.ofReal q) ν ≤
            (K : ℝ≥0∞) * eLpNorm (f.1 : X → 𝕜) (ENNReal.ofReal q) μ)
    (htop :
      ∀ (r₀ q : ℝ) (C₀ C₁ : ℝ≥0), 1 ≤ r₀ → r₀ < q →
      ∃ K : ℝ≥0,
      ∀ {X : Type u} {Y : Type v} {𝕜 : Type w} [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
        (μ : Measure X) (ν : Measure Y) [Fact (1 ≤ ENNReal.ofReal q)]
        (T : intersectionCore μ (ENNReal.ofReal r₀) ∞
          (ENNReal.ofReal q) →ₗ[𝕜] (Y → 𝕜)),
        (∀ f, AEStronglyMeasurable (T f) ν) →
        (∀ f, endpointEstimate μ ν (ENNReal.ofReal r₀) C₀ (f.1 : X → 𝕜) (T f)) →
        (∀ f, endpointEstimate μ ν ∞ C₁ (f.1 : X → 𝕜) (T f)) →
        ∀ f, MemLp (T f) (ENNReal.ofReal q) ν ∧
          eLpNorm (T f) (ENNReal.ofReal q) ν ≤
            (K : ℝ≥0∞) * eLpNorm (f.1 : X → 𝕜) (ENNReal.ofReal q) μ) :
    LinearExtension.{u,v,w} := by
  intro p₀ p₁ p hpFact hp₀ h₀ h₁ C₀ C₁
  rcases marcinkiewicz_exponent_coordinates p₀ p₁ p hp₀ h₀ h₁ with
    ⟨hp₀Top, hpTop, hr₀, hr₀q, hcoord₀, hcoord⟩
  by_cases hp₁Top : p₁ = ∞
  · subst p₁
    obtain ⟨K, hK⟩ := htop p₀.toReal p.toReal C₀ C₁ hr₀ hr₀q
    refine ⟨K, ?_⟩
    intro X Y 𝕜 instX instY inst𝕜 μ ν T hmeas hw₀ hw₁
    apply extend_from_intersection_of_bound μ ν p₀ ∞ p hpTop K T
    have hK' := @hK X Y 𝕜 instX instY inst𝕜 μ ν
    rw [hcoord₀, hcoord] at hK'
    exact hK' T hmeas hw₀ hw₁
  · have hr₁ : p.toReal < p₁.toReal :=
      (ENNReal.toReal_lt_toReal hpTop hp₁Top).2 h₁
    have hcoord₁ := ENNReal.ofReal_toReal hp₁Top
    obtain ⟨K, hK⟩ := hfinite p₀.toReal p₁.toReal p.toReal C₀ C₁ hr₀ hr₀q hr₁
    refine ⟨K, ?_⟩
    intro X Y 𝕜 instX instY inst𝕜 μ ν T hmeas hw₀ hw₁
    apply extend_from_intersection_of_bound μ ν p₀ p₁ p hpTop K T
    have hK' := @hK X Y 𝕜 instX instY inst𝕜 μ ν
    rw [hcoord₀, hcoord₁, hcoord] at hK'
    exact hK' T hmeas hw₀ hw₁

/-- A linear operator on the endpoint intersection has a unique bounded extension
to every strictly intermediate Lp space. -/
theorem marcinkiewicz_linear_extension : MarcinkiewiczSpec.LinearExtension.{u,v,w} := by
  apply linearExtension_of_real_core_bounds
  · intro r₀ r₁ p C₀ C₁ hr₀ h₀ h₁
    refine ⟨finiteInterpolationConstant r₀ r₁ p C₀ C₁, ?_⟩
    intro X Y 𝕜 instX instY inst𝕜 μ ν hpFact T hmeas hw₀ hw₁ f
    have hr₀pos : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀
    apply strongType_of_distribution_truncation_bound C₀ C₁ hr₀pos h₀ h₁
      (Lp.memLp f.1) (hmeas f)
    intro t ht
    exact distribution_truncation_bound_linear μ ν (ENNReal.ofReal p)
      hr₀pos ((hr₀pos.trans h₀).trans h₁) ht T hw₀ hw₁ f
  · intro r₀ p C₀ C₁ hr₀ h₀
    refine ⟨infinityInterpolationConstant r₀ p C₀ C₁, ?_⟩
    intro X Y 𝕜 instX instY inst𝕜 μ ν hpFact T hmeas hw₀ hw₁ f
    have hr₀pos : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀
    apply strongType_of_distribution_truncation_bound_top hr₀pos h₀
      (Lp.memLp f.1) (hmeas f) C₀ C₁
    intro t ht
    exact distribution_truncation_bound_top_linear μ ν (ENNReal.ofReal p)
      hr₀pos (mul_nonneg (infinityTruncationScale_pos C₁).le ht.le) ht
      T hmeas hw₀ hw₁ (infinityTruncationScale_small C₁ ht) f


end ExpandedFA.Interpolation
