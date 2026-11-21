import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.TailAndTruncatedMoments
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.ProbabilityObjects
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Dirac.Basic

open MeasureTheory Set Filter
open scoped ENNReal
namespace ProbabilityFoundations.Ch01
universe u

/-- Pointwise power as a weighted tail integral, including the infinite value. -/
lemma rpow_eq_tail_integral (y : ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    y ^ p = ENNReal.ofReal p * ∫⁻ t : ℝ in Ioi 0,
      {t : ℝ | ENNReal.ofReal t < y}.indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t := by
  classical
  have finite (x : ℝ) (hx : 0 ≤ x) :
      ENNReal.ofReal x ^ p = ENNReal.ofReal p * ∫⁻ t : ℝ in Ioi 0,
        {t : ℝ | ENNReal.ofReal t < ENNReal.ofReal x}.indicator
          (fun t => ENNReal.ofReal (t ^ (p - 1))) t := by
    have h := lintegral_rpow_eq_lintegral_meas_lt_mul (Measure.dirac ())
      (f := fun _ : Unit => x) (Eventually.of_forall fun _ => hx)
      measurable_const.aemeasurable hp
    rw [lintegral_dirac, ← ENNReal.ofReal_rpow_of_nonneg hx hp.le] at h
    rw [h]
    congr 1
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    by_cases htx : t < x
    · have htx' : ENNReal.ofReal t < ENNReal.ofReal x :=
        (ENNReal.ofReal_lt_ofReal_iff (lt_trans ht htx)).mpr htx
      simp [htx, htx']
    · have htx' : ¬ ENNReal.ofReal t < ENNReal.ofReal x :=
        not_lt.mpr (ENNReal.ofReal_le_ofReal (le_of_not_gt htx))
      simp [htx, htx']
  by_cases hy : y = ∞
  · subst y
    rw [ENNReal.top_rpow_of_pos hp]
    symm
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro r
    let x : ℝ := (r : ℝ) ^ p⁻¹
    have hx : 0 ≤ x := Real.rpow_nonneg r.coe_nonneg _
    have heq : ENNReal.ofReal x ^ p = (r : ℝ≥0∞) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hx hp.le]
      simp [x, Real.rpow_inv_rpow r.coe_nonneg hp.ne']
    rw [← heq, finite x hx]
    gcongr
    exact le_top
  · rw [← ENNReal.ofReal_toReal hy]
    exact finite y.toReal ENNReal.toReal_nonneg

/-- Tonelli for an extended-valued random variable and a real threshold. -/
lemma weighted_tail_swap {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (Y : Ω → ℝ≥0∞) (hY : Measurable Y)
    (p : ℝ) (s : Set ℝ) :
    (∫⁻ ω, (∫⁻ t : ℝ in s, {t : ℝ | ENNReal.ofReal t < Y ω}.indicator
      (fun t => ENNReal.ofReal (t ^ (p - 1))) t) ∂P) =
    ∫⁻ t : ℝ in s, ENNReal.ofReal (t ^ (p - 1)) * P {ω | ENNReal.ofReal t < Y ω} := by
  classical
  have hw : Measurable (fun z : Ω × ℝ => ENNReal.ofReal (z.2 ^ (p - 1))) := by fun_prop
  have hm : Measurable (fun z : Ω × ℝ =>
      {z : Ω × ℝ | ENNReal.ofReal z.2 < Y z.1}.indicator
        (fun z => ENNReal.ofReal (z.2 ^ (p - 1))) z) :=
    hw.indicator (measurableSet_lt measurable_snd.ennreal_ofReal
      (hY.comp measurable_fst))
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro t
  exact lintegral_indicator_const (measurableSet_lt measurable_const hY) _

/-- The full moment formula holds for any s-finite measure. -/
lemma lintegral_rpow_eq_tail {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (Y : Ω → ℝ≥0∞) (hY : Measurable Y)
    (p : ℝ) (hp : 0 < p) :
    (∫⁻ ω, Y ω ^ p ∂P) = ENNReal.ofReal p *
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t ^ (p - 1)) * P {ω | ENNReal.ofReal t < Y ω} := by
  simp_rw [rpow_eq_tail_integral _ hp]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, weighted_tail_swap P Y hY]

theorem full_moment : Specs.ProbabilityFoundations.Ch01.TailAndTruncatedMoments.fullMomentType := by
  intro Ω _ P _ Y hY p hp
  exact lintegral_rpow_eq_tail P Y hY p hp

/-- The elementary integral needed at a finite truncation threshold. -/
lemma power_integral {p a : ℝ} (hp : 0 < p) (ha : 0 < a) :
    ENNReal.ofReal a ^ p = ENNReal.ofReal p *
      ∫⁻ t : ℝ in Ioo 0 a, ENNReal.ofReal (t ^ (p - 1)) := by
  have h := rpow_eq_tail_integral (ENNReal.ofReal a) hp
  simp_rw [ENNReal.ofReal_lt_ofReal_iff ha] at h
  rw [setLIntegral_indicator (show MeasurableSet {t : ℝ | t < a} from measurableSet_Iio)] at h
  have hs : {t : ℝ | t < a} ∩ Ioi 0 = Ioo 0 a := by ext; simp [and_comm]
  rwa [hs] at h

lemma power_integral_Ioc {p a : ℝ} (hp : 0 < p) (ha : 0 < a) :
    ENNReal.ofReal a ^ p = ENNReal.ofReal p *
      ∫⁻ t : ℝ in Ioc 0 a, ENNReal.ofReal (t ^ (p - 1)) := by
  rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
  exact power_integral hp ha

/-- Strict and non-strict extended-valued tails agree at almost every
positive real threshold. The exceptional levels form a countable set. -/
lemma ennreal_tail_ae_eq {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ≥0∞) (s : Set ℝ)
    (hs : MeasurableSet s) (hspos : s ⊆ Ioi 0) :
    (fun t : ℝ => P {ω | ENNReal.ofReal t ≤ Y ω}) =ᵐ[volume.restrict s]
      (fun t => P {ω | ENNReal.ofReal t < Y ω}) := by
  have hc := (countable_meas_le_ne_meas_lt P Y).preimage ENNReal.coe_injective
  have hn := (hc.image (fun r : NNReal => (r : ℝ))).ae_notMem (volume.restrict s)
  filter_upwards [hn, self_mem_ae_restrict hs] with t ht hts
  by_contra hne
  have hpos : 0 < t := hspos hts
  let r : NNReal := NNReal.mk t hpos.le
  have hr : ENNReal.ofReal t = (r : ℝ≥0∞) := by
    simp [r, ENNReal.ofReal, Real.toNNReal_of_nonneg hpos.le]
  apply ht
  refine ⟨r, ?_, rfl⟩
  change P {ω | (r : ℝ≥0∞) ≤ Y ω} ≠ P {ω | (r : ℝ≥0∞) < Y ω}
  rwa [← hr]

theorem tail_convention :
    Specs.ProbabilityFoundations.Ch01.TailAndTruncatedMoments.tailConventionType := by
  intro Ω _ P _ Y _ p _ s hs hspos
  apply lintegral_congr_ae
  filter_upwards [ennreal_tail_ae_eq P Y s hs hspos] with t ht
  rw [ht]

lemma moment_on_level {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ≥0∞) (hY : Measurable Y) (p : ℝ) (b : ℝ≥0∞) :
    (∫⁻ ω in {ω | Y ω = b}, Y ω ^ p ∂P) = b ^ p * P {ω | Y ω = b} := by
  have he := measurableSet_eq_fun hY (measurable_const (a := b))
  calc
    _ = ∫⁻ _ in {ω | Y ω = b}, b ^ p ∂P :=
      setLIntegral_congr_fun he (fun ω hω => by rw [hω])
    _ = _ := setLIntegral_const _ _

theorem lower_endpoint :
    Specs.ProbabilityFoundations.Ch01.TailAndTruncatedMoments.lowerEndpointType := by
  intro Ω _ P _ Y hY p a _ _
  have he := measurableSet_eq_fun hY (measurable_const (a := ENNReal.ofReal a))
  have hs : {ω | Y ω ≤ ENNReal.ofReal a} =
      {ω | Y ω < ENNReal.ofReal a} ∪ {ω | Y ω = ENNReal.ofReal a} := by
    ext ω; simp only [mem_ofPred_eq, mem_union]; exact le_iff_lt_or_eq
  have hd : Disjoint {ω | Y ω < ENNReal.ofReal a} {ω | Y ω = ENNReal.ofReal a} := by
    rw [disjoint_left]; intro ω hlt heq; exact (ne_of_lt hlt) heq
  rw [hs, lintegral_union he hd, moment_on_level P Y hY]

theorem upper_endpoint :
    Specs.ProbabilityFoundations.Ch01.TailAndTruncatedMoments.upperEndpointType := by
  intro Ω _ P _ Y hY p a _ _
  have he := measurableSet_eq_fun hY (measurable_const (a := ENNReal.ofReal a))
  have hs : {ω | ENNReal.ofReal a ≤ Y ω} =
      {ω | ENNReal.ofReal a < Y ω} ∪ {ω | Y ω = ENNReal.ofReal a} := by
    ext ω; simp only [mem_ofPred_eq, mem_union]; exact le_iff_lt_or_eq.trans (or_congr Iff.rfl eq_comm)
  have hd : Disjoint {ω | ENNReal.ofReal a < Y ω} {ω | Y ω = ENNReal.ofReal a} := by
    rw [disjoint_left]; intro ω hlt heq; exact (ne_of_gt hlt) heq
  rw [hs, lintegral_union he hd, moment_on_level P Y hY]

/-- Split the power-tail integral of the measure restricted to the upper event.
The lower piece is constant in its tail probability. -/
lemma upper_moment_formula {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (Y : Ω → ℝ≥0∞) (hY : Measurable Y)
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    (∫⁻ ω in {ω | ENNReal.ofReal a < Y ω}, Y ω ^ p ∂P) =
      ENNReal.ofReal a ^ p * P {ω | ENNReal.ofReal a < Y ω} +
      ENNReal.ofReal p * (∫⁻ t : ℝ in Ioi a,
        ENNReal.ofReal (t ^ (p - 1)) * P {ω | ENNReal.ofReal t < Y ω}) := by
  let A := {ω | ENNReal.ofReal a < Y ω}
  have hlow : (∫⁻ t : ℝ in Ioc 0 a, ENNReal.ofReal (t ^ (p - 1)) *
      (P.restrict A) {ω | ENNReal.ofReal t < Y ω}) =
      (∫⁻ t : ℝ in Ioc 0 a, ENNReal.ofReal (t ^ (p - 1))) * P A := by
    rw [← lintegral_mul_const _ (by fun_prop)]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    congr 1
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hY)]
    congr 1
    apply inter_eq_right.mpr
    intro ω hω
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) hω
  have hhigh : (∫⁻ t : ℝ in Ioi a, ENNReal.ofReal (t ^ (p - 1)) *
      (P.restrict A) {ω | ENNReal.ofReal t < Y ω}) =
      ∫⁻ t : ℝ in Ioi a, ENNReal.ofReal (t ^ (p - 1)) *
        P {ω | ENNReal.ofReal t < Y ω} := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    congr 1
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hY)]
    congr 1
    apply inter_eq_left.mpr
    intro ω hω
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.le) hω
  have h := lintegral_rpow_eq_tail (P.restrict A) Y hY p hp
  rw [← Ioc_union_Ioi_eq_Ioi ha.le, lintegral_union measurableSet_Ioi
    (Ioc_disjoint_Ioi le_rfl), hlow, hhigh, mul_add, ← mul_assoc,
    ← power_integral_Ioc hp ha] at h
  exact h

theorem upper_moment : Specs.ProbabilityFoundations.Ch01.TailAndTruncatedMoments.upperMomentType := by
  intro Ω _ P _ Y hY p a hp ha
  exact upper_moment_formula P Y hY p a hp ha

/-- Capping at a finite level retains exactly the lower part of the tail integral. -/
lemma capped_moment {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (Y : Ω → ℝ≥0∞) (hY : Measurable Y)
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    (∫⁻ ω, min (Y ω) (ENNReal.ofReal a) ^ p ∂P) =
      ENNReal.ofReal p * (∫⁻ t : ℝ in Ioo 0 a,
        ENNReal.ofReal (t ^ (p - 1)) * P {ω | ENNReal.ofReal t < Y ω}) := by
  classical
  rw [lintegral_rpow_eq_tail P _ (hY.min measurable_const) p hp]
  congr 1
  have he : (fun t : ℝ => ENNReal.ofReal (t ^ (p - 1)) *
      P {ω | ENNReal.ofReal t < min (Y ω) (ENNReal.ofReal a)}) =
      (Iio a).indicator (fun t => ENNReal.ofReal (t ^ (p - 1)) *
        P {ω | ENNReal.ofReal t < Y ω}) := by
    funext t
    by_cases ht : t < a <;> simp [lt_min_iff, ENNReal.ofReal_lt_ofReal_iff ha, ht]
  rw [he, setLIntegral_indicator measurableSet_Iio]
  have hi : Iio a ∩ Ioi (0 : ℝ) = Ioo 0 a := by ext t; simp [and_comm]
  rw [hi]

lemma capped_moment_decomposition {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ≥0∞) (hY : Measurable Y) (p : ℝ) (b : ℝ≥0∞) :
    (∫⁻ ω, min (Y ω) b ^ p ∂P) =
      (∫⁻ ω in {ω | Y ω ≤ b}, Y ω ^ p ∂P) + b ^ p * P {ω | b < Y ω} := by
  have hB := measurableSet_le hY (measurable_const (a := b))
  have hcomp : {ω | Y ω ≤ b}ᶜ = {ω | b < Y ω} := by ext ω; simp
  rw [← lintegral_add_compl (fun ω => min (Y ω) b ^ p) hB, hcomp]
  congr 1
  · apply setLIntegral_congr_fun hB
    intro ω hω
    simp only [min_eq_left (show Y ω ≤ b from hω)]
  · calc
      _ = ∫⁻ _ in {ω | b < Y ω}, b ^ p ∂P :=
        setLIntegral_congr_fun (measurableSet_lt measurable_const hY)
          (fun ω hω => by rw [min_eq_right hω.le])
      _ = _ := setLIntegral_const _ _

theorem lower_moment : Specs.ProbabilityFoundations.Ch01.TailAndTruncatedMoments.lowerMomentType := by
  intro Ω _ P _ Y hY p a hp ha
  rw [← capped_moment P Y hY p a hp ha,
    capped_moment_decomposition P Y hY]
  symm
  apply ENNReal.add_sub_cancel_right
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
    (measure_ne_top P _)

theorem bounded_terms : Specs.ProbabilityFoundations.Ch01.TailAndTruncatedMoments.boundedTermsType := by
  intro Ω _ P _ Y hY p a hp ha
  have hb : ENNReal.ofReal a ^ p < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top
  have hatom : ENNReal.ofReal a ^ p * P {ω | ENNReal.ofReal a < Y ω} < ∞ :=
    ENNReal.mul_lt_top hb (measure_lt_top P _)
  have hcap : (∫⁻ ω, min (Y ω) (ENNReal.ofReal a) ^ p ∂P) < ∞ := by
    calc
      _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal a ^ p ∂P :=
        lintegral_mono (fun ω => ENNReal.rpow_le_rpow (min_le_right _ _) hp.le)
      _ = ENNReal.ofReal a ^ p := by simp
      _ < ∞ := hb
  refine ⟨?_, ?_, hatom⟩
  · rw [capped_moment_decomposition P Y hY] at hcap
    exact (le_add_right le_rfl).trans_lt hcap
  · rwa [← capped_moment P Y hY p a hp ha]

theorem lower_endpoint_sub :
    Specs.ProbabilityFoundations.Ch01.TailAndTruncatedMoments.lowerEndpointSubType := by
  intro Ω _ P _ Y hY p a hp ha
  rw [lower_endpoint P Y hY p a hp ha, ENNReal.add_sub_cancel_right]
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
    (measure_ne_top P _)

theorem upper_endpoint_sub :
    Specs.ProbabilityFoundations.Ch01.TailAndTruncatedMoments.upperEndpointSubType := by
  intro Ω _ P _ Y hY p a hp ha
  rw [upper_endpoint P Y hY p a hp ha, ENNReal.add_sub_cancel_right]
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
    (measure_ne_top P _)

end ProbabilityFoundations.Ch01
