import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyLowpass
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyWeightedKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

noncomputable section
open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology

namespace ExpandedFA.PartIV.HardyLowpass
open ExpandedFA.Fourier HardyMaximalSpec

lemma weightedNorm_tsum_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (F : ℕ → Euclidean d → 𝕜) :
    weightedNorm (fun x => ∑' n, F n x) ≤ ∑' n, weightedNorm (F n) := by
  apply iSup_le
  intro x
  rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
  calc
    _ ≤ ENNReal.ofReal ((1 + ‖x‖) ^ ((d : ℝ) + 1 / 2)) *
        ∑' n, ‖F n x‖ₑ := mul_le_mul_right (enorm_tsum_le_tsum_enorm) _
    _ = ∑' n, ENNReal.ofReal ((1 + ‖x‖) ^ ((d : ℝ) + 1 / 2)) * ‖F n x‖ₑ :=
      ENNReal.tsum_mul_left.symm
    _ ≤ ∑' n, weightedNorm (F n) :=
      ENNReal.tsum_le_tsum fun n => HardyWeightedKernel.weighted_pointwise (F n) x

lemma decay_of_weighted_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Euclidean d → 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hu : weightedNorm u ≤ ENNReal.ofReal C) (x : Euclidean d) :
    ‖u x‖ ≤ C * (1 + ‖x‖) ^ (-(d : ℝ) - 1 / 2) := by
  have hx := (le_iSup (fun y => ENNReal.ofReal
    ((1 + ‖y‖) ^ ((d : ℝ) + 1 / 2) * ‖u y‖)) x).trans hu
  have hx' : (1 + ‖x‖) ^ ((d : ℝ) + 1 / 2) * ‖u x‖ ≤ C :=
    (ENNReal.ofReal_le_ofReal_iff hC).mp hx
  rw [show -(d : ℝ) - 1 / 2 = -((d : ℝ) + 1 / 2) by ring,
    Real.rpow_neg (by positivity), ← div_eq_mul_inv]
  exact (le_div_iff₀' (by positivity)).mpr hx'

lemma weighted_bound_of_decay {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Euclidean d → 𝕜) {C : ℝ}
    (hu : ∀ x, ‖u x‖ ≤ C * (1 + ‖x‖) ^ (-(d : ℝ) - 1 / 2)) :
    weightedNorm u ≤ ENNReal.ofReal C := by
  apply iSup_le
  intro x
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left (hu x)
    (by positivity : 0 ≤ (1 + ‖x‖) ^ ((d : ℝ) + 1 / 2))
  convert h using 1
  rw [show -(d : ℝ) - 1 / 2 = -((d : ℝ) + 1 / 2) by ring,
    Real.rpow_neg (by positivity)]
  field_simp

lemma integrable_of_weighted_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Euclidean d → 𝕜) (hm : AEStronglyMeasurable u volume)
    (hu : weightedNorm u < ∞) : Integrable u := by
  have hb : weightedNorm u ≤ ENNReal.ofReal (weightedNorm u).toReal := by
    rw [ENNReal.ofReal_toReal hu.ne]
  have hi : Integrable (fun x : Euclidean d =>
      (1 + ‖x‖) ^ (-((d : ℝ) + 1 / 2))) volume := by
    apply integrable_one_add_norm
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    linarith
  apply (hi.const_mul (weightedNorm u).toReal).mono' hm
  exact Filter.Eventually.of_forall fun x => by
    simpa only [neg_add_rev, neg_div, add_comm, sub_eq_add_neg] using
      decay_of_weighted_bound u ENNReal.toReal_nonneg hb x

theorem fixed_kernel_integrable : HardyLowpassSpec.FixedKernelIntegrable := by
  intro 𝕜 _ d Φ hΦ
  obtain ⟨C, hC, hb⟩ := hΦ.2.2 0 Fin.elim0
  have hb' (x : Euclidean d) : ‖Φ x‖ ≤ C / (1 + ‖x‖) ^ (d + 1) := by
    simpa only [coordinatePartial, iteratedFDeriv_zero_apply, add_zero] using hb x
  have hi : Integrable (fun x : Euclidean d => (1 + ‖x‖) ^ (-((d : ℝ) + 1))) volume := by
    apply integrable_one_add_norm
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    linarith
  constructor
  · apply (hi.const_mul C).mono' hΦ.1.continuous.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖),
      ← div_eq_mul_inv, show (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) by simp,
      Real.rpow_natCast] using hb' x
  · apply lt_of_le_of_lt (weighted_bound_of_decay Φ (C := C) ?_) ENNReal.ofReal_lt_top
    intro x
    apply (hb' x).trans
    rw [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_neg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x])
    push_cast
    linarith

theorem schwartz_weighted : HardyLowpassSpec.SchwartzWeighted := by
  intro 𝕜 _ d η
  let C : ℝ := 2 ^ (d + 1) *
    (Finset.Iic (d + 1, 0)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) η
  have hb (x : Euclidean d) : (1 + ‖x‖) ^ (d + 1) * ‖η x‖ ≤ C := by
    simpa [C] using SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := 𝕜) (m := (d + 1, 0)) (k := d + 1) (n := 0) le_rfl le_rfl η x
  have hw : weightedNorm η ≤ ENNReal.ofReal C := by
    apply iSup_le
    intro x
    apply ENNReal.ofReal_le_ofReal
    apply le_trans _ (hb x)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x])
    push_cast
    linarith
  exact hw.trans_lt ENNReal.ofReal_lt_top

/-- Weighted geometric bounds give an actual, everywhere defined integrable
sum. Measurability is enough; continuity is not an extra assumption. -/
lemma weighted_geometric_series {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (F : ℕ → Euclidean d → 𝕜) {B q : ℝ} (hB : 0 ≤ B) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hm : ∀ n, AEStronglyMeasurable (F n) volume)
    (hb : ∀ n, weightedNorm (F n) ≤ ENNReal.ofReal (B * q ^ n)) :
    (∀ x, Summable (fun n => F n x)) ∧
    Integrable (fun x => ∑' n, F n x) ∧
    weightedNorm (fun x => ∑' n, F n x) ≤ ENNReal.ofReal (B / (1 - q)) := by
  have hg : Summable (fun n : ℕ => B * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left B
  have hn (n : ℕ) (x : Euclidean d) : ‖F n x‖ ≤ B * q ^ n := by
    have h := (HardyWeightedKernel.norm_le_weighted (F n) x).trans (hb n)
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hs (x : Euclidean d) : Summable (fun n => F n x) :=
    hg.of_norm_bounded fun n => hn n x
  have hw : weightedNorm (fun x => ∑' n, F n x) ≤ ENNReal.ofReal (B / (1 - q)) := by
    apply (weightedNorm_tsum_le F).trans
    apply (ENNReal.tsum_le_tsum hb).trans_eq
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hg,
      tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]
  refine ⟨hs, ?_, hw⟩
  apply integrable_of_weighted_bound _ _ (hw.trans_lt ENNReal.ofReal_lt_top)
  apply aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (f := fun N x => ∑ n ∈ Finset.range N, F n x)
  · intro N
    exact Finset.aestronglyMeasurable_fun_sum _ fun n _ => hm n
  · exact Filter.Eventually.of_forall fun x => (hs x).hasSum.tendsto_sum_nat

lemma integral_norm_convolve_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {u v : Euclidean d → 𝕜} (hu : Integrable u) (hv : Integrable v) :
    (∫ x, ‖convolve u v x‖) ≤ (∫ x, ‖u x‖) * (∫ x, ‖v x‖) := by
  have hconv : Integrable (convolve u v) :=
    hu.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜) hv
  have hmajor : Integrable (convolve (fun x => ‖u x‖) (fun x => ‖v x‖)) :=
    hu.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hv.norm
  calc
    _ ≤ ∫ x, convolve (fun x => ‖u x‖) (fun x => ‖v x‖) x := by
      apply integral_mono hconv.norm hmajor
      intro x
      change ‖∫ y, u y * v (x - y)‖ ≤ ∫ y, ‖u y‖ * ‖v (x - y)‖
      simpa only [norm_mul] using norm_integral_le_integral_norm
        (fun y => u y * v (x - y))
    _ = _ := by
      exact integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hu.norm hv.norm

/-- A scalar recurrence sufficient for a weighted convolution Neumann series.
The deliberately larger ratio `2*C*a` avoids division by the L¹ norm, so
the case of a zero convolution kernel is retained. -/
lemma geometric_recurrence_bound {C a H L B : ℝ}
    (hC : 1 ≤ C) (ha : 0 ≤ a) (_hH : 0 ≤ H) (_hL : 0 ≤ L) (hB : 0 ≤ B)
    (hHL : H * L ≤ a * B) (u : ℕ → ℝ) (hu0 : u 0 ≤ B)
    (hu : ∀ n, u (n + 1) ≤ C * (H * (L * a ^ n) + a * u n)) :
    ∀ n, u n ≤ B * (2 * C * a) ^ n := by
  have hC0 : 0 ≤ C := by linarith
  have haq : a ≤ 2 * C * a := by nlinarith
  intro n
  induction n with
  | zero => simpa using hu0
  | succ n ih =>
    calc
      u (n + 1) ≤ C * (H * (L * a ^ n) + a * u n) := hu n
      _ ≤ C * (a * B * (2 * C * a) ^ n + a * (B * (2 * C * a) ^ n)) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        apply add_le_add _ (mul_le_mul_of_nonneg_left ih ha)
        calc
          H * (L * a ^ n) = (H * L) * a ^ n := by ring
          _ ≤ (a * B) * a ^ n := mul_le_mul_of_nonneg_right hHL (pow_nonneg ha n)
          _ ≤ (a * B) * (2 * C * a) ^ n :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha haq n) (mul_nonneg ha hB)
      _ = B * (2 * C * a) ^ (n + 1) := by rw [pow_succ]; ring

/-- Iterates starting at η, so the zeroth term is η rather than a Dirac mass. -/
def convolutionIterates {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (h η : Euclidean d → 𝕜) : ℕ → Euclidean d → 𝕜
  | 0 => η
  | n + 1 => convolve h (convolutionIterates h η n)

lemma neumann_series_summable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (hd : 0 < d)
    (h η : Euclidean d → 𝕜) (hh : Integrable h) (hη : Integrable η)
    (hhw : weightedNorm h < ∞) (hηw : weightedNorm η < ∞)
    {a : ℝ} (ha : 0 < a) (hla : (∫ x, ‖h x‖) ≤ a)
    (hsmall : 2 * (2 : ℝ) ^ ((d : ℝ) + 1 / 2) * a < 1) :
    (∀ x, Summable (fun n => convolutionIterates h η n x)) ∧
    Integrable (fun x => ∑' n, convolutionIterates h η n x) ∧
    weightedNorm (fun x => ∑' n, convolutionIterates h η n x) < ∞ ∧
    (∑' n, weightedNorm (convolutionIterates h η n)) < ∞ := by
  let C : ℝ := 2 ^ ((d : ℝ) + 1 / 2)
  let H : ℝ := (weightedNorm h).toReal
  let L : ℝ := ∫ x, ‖η x‖
  let B : ℝ := (weightedNorm η).toReal + H * L / a
  have hC : 1 ≤ C := Real.one_le_rpow (by norm_num) (by positivity)
  have hC0 : 0 ≤ C := by linarith
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hL : 0 ≤ L := integral_nonneg fun x => norm_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi (n : ℕ) : Integrable (convolutionIterates h η n) := by
    induction n with
    | zero => exact hη
    | succ n ih => exact hh.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜) ih
  have hil (n : ℕ) : (∫ x, ‖convolutionIterates h η n x‖) ≤ L * a ^ n := by
    induction n with
    | zero => simp [convolutionIterates, L]
    | succ n ih =>
      apply (integral_norm_convolve_le hh (hi n)).trans
      calc
        _ ≤ a * (L * a ^ n) := mul_le_mul hla ih
          (integral_nonneg fun x => norm_nonneg _) ha.le
        _ = _ := by rw [pow_succ]; ring
  have hwfin (n : ℕ) : weightedNorm (convolutionIterates h η n) < ∞ := by
    induction n with
    | zero => exact hηw
    | succ n ih =>
      apply (HardyWeightedKernel.weighted_convolution hd h _ hh (hi n) hhw ih).trans_lt
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hhw ENNReal.ofReal_lt_top,
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top ih⟩)
  have hrec (n : ℕ) :
      (weightedNorm (convolutionIterates h η (n + 1))).toReal ≤
        C * (H * (L * a ^ n) + a * (weightedNorm (convolutionIterates h η n)).toReal) := by
    have hconv := HardyWeightedKernel.weighted_convolution hd h _ hh (hi n) hhw (hwfin n)
    have hleft : weightedNorm h * ENNReal.ofReal
        (∫ x, ‖convolutionIterates h η n x‖) ≠ ∞ :=
      ENNReal.mul_ne_top hhw.ne ENNReal.ofReal_ne_top
    have hright₂ : ENNReal.ofReal (∫ x, ‖h x‖) *
        weightedNorm (convolutionIterates h η n) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hwfin n).ne
    have hright := ENNReal.mul_ne_top (a := ENNReal.ofReal C)
      ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨hleft, hright₂⟩)
    have h' := (ENNReal.toReal_le_toReal (hwfin (n + 1)).ne hright).mpr hconv
    rw [ENNReal.toReal_mul, ENNReal.toReal_add hleft hright₂] at h'
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0,
      ENNReal.toReal_ofReal (integral_nonneg fun x => norm_nonneg _)] at h'
    apply h'.trans
    apply mul_le_mul_of_nonneg_left _ hC0
    exact add_le_add (mul_le_mul_of_nonneg_left (hil n) hH)
      (mul_le_mul_of_nonneg_right hla ENNReal.toReal_nonneg)
  have hHL : H * L ≤ a * B := by
    have he : a * (H * L / a) = H * L := mul_div_cancel₀ _ ha.ne'
    dsimp [B]
    nlinarith [ENNReal.toReal_nonneg (a := weightedNorm η)]
  have hb0 : (weightedNorm (convolutionIterates h η 0)).toReal ≤ B := by
    dsimp [convolutionIterates, B]
    exact le_add_of_nonneg_right (by positivity)
  have hbound := geometric_recurrence_bound hC ha.le hH hL hB hHL
    (fun n => (weightedNorm (convolutionIterates h η n)).toReal) hb0 hrec
  have hb (n : ℕ) : weightedNorm (convolutionIterates h η n) ≤
      ENNReal.ofReal (B * (2 * C * a) ^ n) := by
    rw [← ENNReal.ofReal_toReal (hwfin n).ne]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  obtain ⟨hs, hi, hw⟩ := weighted_geometric_series (convolutionIterates h η)
    hB (by positivity : 0 ≤ 2 * C * a) hsmall (fun n => (hi n).aestronglyMeasurable) hb
  refine ⟨hs, hi, hw.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  apply (ENNReal.tsum_le_tsum hb).trans_lt
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((summable_geometric_of_lt_one (by positivity : 0 ≤ 2 * C * a) hsmall).mul_left B)]
  exact ENNReal.ofReal_lt_top

lemma convolve_tsum_of_weighted_summable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (h : Euclidean d → 𝕜) (hh : Integrable h)
    (F : ℕ → Euclidean d → 𝕜) (hm : ∀ n, AEStronglyMeasurable (F n) volume)
    (hw : (∑' n, weightedNorm (F n)) < ∞) (x : Euclidean d) :
    convolve h (fun y => ∑' n, F n y) x = ∑' n, convolve h (F n) x := by
  have hint (n : ℕ) :
      AEStronglyMeasurable (fun y => h y * F n (x - y)) volume :=
    hh.aestronglyMeasurable.mul
      ((hm n).comp_measurePreserving (volume.measurePreserving_sub_left x))
  have hfin : (∑' n, ∫⁻ y, ‖h y * F n (x - y)‖ₑ) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ∑' n, (∫⁻ y, ‖h y‖ₑ) * weightedNorm (F n) := by
        apply ENNReal.tsum_le_tsum
        intro n
        rw [← lintegral_mul_const'' _ hh.aestronglyMeasurable.enorm]
        apply lintegral_mono
        intro y
        change ‖h y * F n (x - y)‖ₑ ≤ ‖h y‖ₑ * weightedNorm (F n)
        rw [enorm_mul]
        exact mul_le_mul_right (HardyWeightedKernel.norm_le_weighted (F n) (x - y)) _
      _ = (∫⁻ y, ‖h y‖ₑ) * ∑' n, weightedNorm (F n) := ENNReal.tsum_mul_left
      _ < ∞ := ENNReal.mul_lt_top hh.hasFiniteIntegral hw
  change (∫ y, h y * ∑' n, F n (x - y)) = ∑' n, ∫ y, h y * F n (x - y)
  simp_rw [← tsum_mul_left]
  exact integral_tsum hint hfin

lemma neumann_series_equation {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (hd : 0 < d)
    (h η : Euclidean d → 𝕜) (hh : Integrable h) (hη : Integrable η)
    (hhw : weightedNorm h < ∞) (hηw : weightedNorm η < ∞)
    {a : ℝ} (ha : 0 < a) (hla : (∫ x, ‖h x‖) ≤ a)
    (hsmall : 2 * (2 : ℝ) ^ ((d : ℝ) + 1 / 2) * a < 1) :
    ∃ S : Euclidean d → 𝕜, Integrable S ∧ weightedNorm S < ∞ ∧
      (∀ x, S x = η x + convolve h S x) := by
  obtain ⟨hs, hi, hw, hsum⟩ := neumann_series_summable hd h η hh hη hhw hηw ha hla hsmall
  have hiF (n : ℕ) : Integrable (convolutionIterates h η n) := by
    induction n with
    | zero => exact hη
    | succ n ih => exact hh.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜) ih
  refine ⟨fun x => ∑' n, convolutionIterates h η n x, hi, hw, ?_⟩
  intro x
  rw [convolve_tsum_of_weighted_summable h hh _
    (fun n => (hiF n).aestronglyMeasurable) hsum]
  exact (hs x).tsum_eq_zero_add

lemma weighted_convolve_lt_top {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (hd : 0 < d)
    {u v : Euclidean d → 𝕜} (hu : Integrable u) (hv : Integrable v)
    (huw : weightedNorm u < ∞) (hvw : weightedNorm v < ∞) :
    weightedNorm (convolve u v) < ∞ := by
  apply (HardyWeightedKernel.weighted_convolution hd u v hu hv huw hvw).trans_lt
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top huw ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvw⟩)

lemma weightedNorm_norm {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (u : Euclidean d → 𝕜) :
    weightedNorm (fun x => ‖u x‖) = weightedNorm u := by
  simp only [weightedNorm, norm_norm]

lemma convolve_assoc {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (hd : 0 < d)
    {u v w : Euclidean d → 𝕜} (hu : Integrable u) (hv : Integrable v) (hw : Integrable w)
    (huw : weightedNorm u < ∞) (hvw : weightedNorm v < ∞) (hww : weightedNorm w < ∞) :
    convolve (convolve u v) w = convolve u (convolve v w) := by
  have hnormv : weightedNorm (fun x => ‖v x‖) < ∞ := by rwa [weightedNorm_norm]
  have hnormw : weightedNorm (fun x => ‖w x‖) < ∞ := by rwa [weightedNorm_norm]
  have hnormu : weightedNorm (fun x => ‖u x‖) < ∞ := by rwa [weightedNorm_norm]
  have hint : Integrable (convolve (fun x => ‖v x‖) (fun x => ‖w x‖)) :=
    hv.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hw.norm
  have hweight := weighted_convolve_lt_top hd hv.norm hw.norm hnormv hnormw
  ext x
  exact convolution_assoc (ContinuousLinearMap.mul 𝕜 𝕜) (ContinuousLinearMap.mul 𝕜 𝕜)
    (ContinuousLinearMap.mul 𝕜 𝕜) (ContinuousLinearMap.mul 𝕜 𝕜)
    (fun a b c => mul_assoc a b c)
    hu.aestronglyMeasurable hv.aestronglyMeasurable hw.aestronglyMeasurable
    (hu.ae_convolution_exists _ hv) (hv.norm.ae_convolution_exists _ hw.norm)
    (HardyWeightedKernel.convolution_absolute hd _ _ hu.norm hint hnormu hweight x)

lemma convolve_comm {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (u v : Euclidean d → 𝕜) :
    convolve u v = convolve v u := by
  ext x
  calc
    convolve u v x = ∫ y, u (x - y) * v y := convolution_eq_swap (ContinuousLinearMap.mul 𝕜 𝕜)
    _ = convolve v u x := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact mul_comm _ _

lemma convolutionIterates_integrable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {h η : Euclidean d → 𝕜} (hh : Integrable h) (hη : Integrable η) (n : ℕ) :
    Integrable (convolutionIterates h η n) := by
  induction n with
  | zero => exact hη
  | succ n ih => exact hh.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜) ih

lemma convolutionIterates_weighted {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (hd : 0 < d)
    {h η : Euclidean d → 𝕜} (hh : Integrable h) (hη : Integrable η)
    (hhw : weightedNorm h < ∞) (hηw : weightedNorm η < ∞) (n : ℕ) :
    weightedNorm (convolutionIterates h η n) < ∞ := by
  induction n with
  | zero => exact hηw
  | succ n ih =>
      exact weighted_convolve_lt_top hd hh
        (convolutionIterates_integrable hh hη n) hhw ih

lemma convolve_reproduces_iterates {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (hd : 0 < d)
    {h η ζ : Euclidean d → 𝕜} (hh : Integrable h) (hη : Integrable η) (hζ : Integrable ζ)
    (hhw : weightedNorm h < ∞) (hηw : weightedNorm η < ∞) (hζw : weightedNorm ζ < ∞)
    (hrepro : convolve ζ η = η) (n : ℕ) :
    convolve ζ (convolutionIterates h η n) = convolutionIterates h η n := by
  induction n with
  | zero => exact hrepro
  | succ n ih =>
    change convolve ζ (convolve h (convolutionIterates h η n)) =
      convolve h (convolutionIterates h η n)
    rw [← convolve_assoc hd hζ hh (convolutionIterates_integrable hh hη n)
      hζw hhw (convolutionIterates_weighted hd hh hη hhw hηw n),
      convolve_comm ζ h,
      convolve_assoc hd hh hζ (convolutionIterates_integrable hh hη n)
        hhw hζw (convolutionIterates_weighted hd hh hη hhw hηw n), ih]

theorem resolve_defect : HardyLowpassSpec.ResolveDefect := by
  intro 𝕜 _ d hd Φ η ζ c hΦ hη hζ hΦw hηw hζw hrepro h hh hhw hsmall
  let Cw : ℝ := 2 * (2 : ℝ) ^ ((d : ℝ) + 1 / 2)
  have hCw : 0 < Cw := by dsimp [Cw]; positivity
  obtain ⟨a, hla, haCw⟩ := exists_between hsmall
  have ha : 0 < a := (integral_nonneg fun x => norm_nonneg (h x)).trans_lt hla
  have hsmall' : Cw * a < 1 := by
    rw [mul_comm]
    exact (lt_div_iff₀ hCw).mp (by simpa [Cw, one_div] using haCw)
  obtain ⟨hs, hS, hSw, hsum⟩ := neumann_series_summable hd h η hh hη hhw hηw ha hla.le hsmall'
  let S : Euclidean d → 𝕜 := fun x => ∑' n, convolutionIterates h η n x
  have hζS : convolve ζ S = S := by
    ext x
    rw [convolve_tsum_of_weighted_summable ζ hζ _
      (fun n => (convolutionIterates_integrable hh hη n).aestronglyMeasurable) hsum]
    simp_rw [convolve_reproduces_iterates hd hh hη hζ hhw hηw hζw hrepro]
    rfl
  have hseq (x : Euclidean d) : S x = η x + convolve h S x := by
    rw [convolve_tsum_of_weighted_summable h hh _
      (fun n => (convolutionIterates_integrable hh hη n).aestronglyMeasurable) hsum]
    exact (hs x).tsum_eq_zero_add
  have hΦζ : Integrable (convolve Φ ζ) :=
    hΦ.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜) hζ
  have hΦζw := weighted_convolve_lt_top hd hΦ hζ hΦw hζw
  have hprod : convolve (convolve Φ ζ) S = convolve Φ S := by
    rw [convolve_assoc hd hΦ hζ hS hΦw hζw hSw, hζS]
  have hexpr (x : Euclidean d) : convolve h S x = S x - c⁻¹ * convolve Φ S x := by
    have h₁ := HardyWeightedKernel.convolution_absolute hd ζ S hζ hS hζw hSw x
    have h₂ := HardyWeightedKernel.convolution_absolute hd (convolve Φ ζ) S hΦζ hS hΦζw hSw x
    change (∫ y, (ζ y - c⁻¹ * convolve Φ ζ y) * S (x - y)) = _
    simp_rw [sub_mul, mul_assoc]
    rw [integral_sub h₁ (h₂.const_mul c⁻¹), integral_const_mul]
    change convolve ζ S x - c⁻¹ * convolve (convolve Φ ζ) S x = _
    rw [hζS, hprod]
  have hcore (x : Euclidean d) : c⁻¹ * convolve Φ S x = η x := by
    have heq := hseq x
    rw [hexpr] at heq
    linear_combination heq
  refine ⟨fun x => c⁻¹ * S x, ‖c⁻¹‖ * (weightedNorm S).toReal,
    hS.const_mul c⁻¹, by positivity, ?_, ?_⟩
  · intro x
    rw [norm_mul]
    have hb : weightedNorm S ≤ ENNReal.ofReal (weightedNorm S).toReal := by
      rw [ENNReal.ofReal_toReal hSw.ne]
    exact (mul_le_mul_of_nonneg_left
      (decay_of_weighted_bound S ENNReal.toReal_nonneg hb x) (norm_nonneg _)).trans_eq (by ring)
  · intro x
    calc
      η x = c⁻¹ * convolve Φ S x := (hcore x).symm
      _ = c⁻¹ * convolve S Φ x := by rw [convolve_comm Φ S]
      _ = convolve (fun y => c⁻¹ * S y) Φ x := by
        change c⁻¹ * (∫ y, S y * Φ (x - y)) = ∫ y, (c⁻¹ * S y) * Φ (x - y)
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with y
        exact (mul_assoc _ _ _).symm

/-- Assemble the inverse from the analytic small-defect estimate. -/
theorem lowpass_inverse_of_small_defect (hdefect : HardyLowpassSpec.SmallDefect) :
    HardyLowpassSpec.LowpassInverse := by
  intro 𝕜 _ d hd Φ hΦ
  obtain ⟨R, η, ζ, hlow, hrepro, hh, hhw, hsmall⟩ := hdefect hd Φ hΦ
  obtain ⟨hΦi, hΦw⟩ := fixed_kernel_integrable Φ hΦ
  obtain ⟨Ψ, C, hΨ, hC, hdecay, hid⟩ := resolve_defect hd Φ η ζ (∫ x, Φ x)
    hΦi η.integrable ζ.integrable hΦw (schwartz_weighted η) (schwartz_weighted ζ)
    hrepro hh hhw hsmall
  exact ⟨R, η, Ψ, C, hlow, hΨ, hC, hdecay, hid⟩

theorem small_defect_of_scaled_cutoffs_and_dilation : HardyLowpassSpec.SmallDefectAssembly := by
  intro hcut herr 𝕜 _ d hd Φ hΦ
  obtain ⟨η₀, ζ₀, hscale⟩ := hcut (𝕜 := 𝕜) d
  obtain ⟨hΦi, hΦw⟩ := fixed_kernel_integrable Φ hΦ
  obtain ⟨R, hR, hh, hhw, hsmall⟩ := herr hd Φ hΦi hΦw hΦ.2.1 ζ₀
    (2 * (2 : ℝ) ^ ((d : ℝ) + 1 / 2))⁻¹ (by positivity)
  obtain ⟨η, ζ, hη, hζ, hlow, hrepro⟩ := hscale R hR
  refine ⟨R, η, ζ, hlow, hrepro, ?_⟩
  rw [hζ]
  exact ⟨hh, hhw, hsmall⟩

lemma exists_schwartz_cutoff (d : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ χ : Schwartz ℂ d,
      tsupport χ ⊆ Metric.ball 0 b ∧
      ∀ ξ ∈ Metric.ball (0 : Euclidean d) a, χ ξ = 1 := by
  let f : ContDiffBump (0 : Euclidean d) :=
    ⟨a, (a + b) / 2, ha, by linarith⟩
  have hc : HasCompactSupport (fun x => (f x : ℂ)) :=
    f.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp f.contDiff
  refine ⟨hc.toSchwartzMap hs, ?_, ?_⟩
  · have hsub : tsupport (fun x => (f x : ℂ)) ⊆ tsupport f := by
      apply closure_mono
      intro x hx
      simpa only [Function.mem_support, Complex.ofReal_ne_zero] using hx
    apply hsub.trans
    rw [f.tsupport_eq]
    apply Metric.closedBall_subset_ball
    dsimp [f]
    linarith
  · intro ξ hξ
    change (f ξ : ℂ) = 1
    rw [f.one_of_mem_closedBall (Metric.ball_subset_closedBall hξ)]
    rfl

theorem nested_cutoffs : HardyLowpassSpec.NestedCutoffs := by
  intro d R hR
  obtain ⟨χ₀, hχ₀, hχ₀one⟩ := exists_schwartz_cutoff d
    (a := 1 / R) (b := 2 / R) (by positivity) (by gcongr; norm_num)
  obtain ⟨χ₁, hχ₁, hχ₁one⟩ := exists_schwartz_cutoff d
    (a := 2 / R) (b := 4 / R) (by positivity) (by gcongr; norm_num)
  let η : Schwartz ℂ d := 𝓕⁻ χ₀
  let ζ : Schwartz ℂ d := 𝓕⁻ χ₁
  have hη : schwartzFourier η = χ₀ := by
    simpa only [schwartzFourier, FourierTransform.fourierCLM_apply, η] using
      (FourierTransform.fourier_fourierInv_eq χ₀)
  have hζ : schwartzFourier ζ = χ₁ := by
    simpa only [schwartzFourier, FourierTransform.fourierCLM_apply, ζ] using
      (FourierTransform.fourier_fourierInv_eq χ₁)
  refine ⟨η, ζ, by simpa [hη] using hχ₀, ?_, by simpa [hζ] using hχ₁, ?_, ?_⟩
  · simpa [hη] using hχ₀one
  · simpa [hζ] using hχ₁one
  · have hprod : SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) ζ η = η := by
      apply (FourierTransform.fourierCLE ℂ (Schwartz ℂ d)).injective
      ext ξ
      change schwartzFourier (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) ζ η) ξ =
        schwartzFourier η ξ
      rw [Inversion.fourier_convolution, hζ, hη]
      by_cases hξ : χ₀ ξ = 0
      · simp [hξ]
      · have hm : ξ ∈ Metric.ball (0 : Euclidean d) (2 / R) :=
          hχ₀ (subset_tsupport χ₀ (by exact hξ))
        rw [hχ₁one ξ hm, one_mul]
    intro x
    have h := congrArg (fun f : Schwartz ℂ d => f x) hprod
    simpa only [SchwartzMap.convolution_apply, convolve] using h



def dilationEquiv {d : ℕ} (R : ℝ) (hR : 0 < R) : Euclidean d ≃L[ℝ] Euclidean d :=
  { LinearEquiv.smulOfNeZero ℝ (Euclidean d) R⁻¹ (inv_ne_zero hR.ne') with
    continuous_toFun := by change Continuous (fun x : Euclidean d => R⁻¹ • x); fun_prop
    continuous_invFun := by change Continuous (fun x : Euclidean d => (R⁻¹)⁻¹ • x); fun_prop }

def dilateSchwartz {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (R : ℝ) (hR : 0 < R) (ζ : Schwartz 𝕜 d) : Schwartz 𝕜 d :=
  (R ^ d)⁻¹ • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (dilationEquiv R hR) ζ

@[simp] lemma dilateSchwartz_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (R : ℝ) (hR : 0 < R) (ζ : Schwartz 𝕜 d) (x : Euclidean d) :
    dilateSchwartz R hR ζ x = dilate R ζ x := by
  rfl

lemma dilate_schwartz_integrable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (R : ℝ) (hR : 0 < R) (ζ : Schwartz 𝕜 d) : Integrable (dilate R ζ) := by
  change Integrable (dilateSchwartz R hR ζ : Euclidean d → 𝕜)
  exact (dilateSchwartz R hR ζ).integrable

lemma dilate_schwartz_weighted {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (R : ℝ) (hR : 0 < R) (ζ : Schwartz 𝕜 d) : weightedNorm (dilate R ζ) < ∞ := by
  change weightedNorm (dilateSchwartz R hR ζ) < ∞
  exact schwartz_weighted _

lemma integralFourier_dilate {d : ℕ} (R : ℝ) (hR : 0 < R)
    (f : Euclidean d → ℂ) (ξ : Euclidean d) :
    integralFourier (dilate R f) ξ = integralFourier f (R • ξ) := by
  have hpoint (x : Euclidean d) :
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) *
        dilate R f x = (R ^ d)⁻¹ •
          (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
            (inner ℝ (R⁻¹ • x) (R • ξ) : ℝ)) * f (R⁻¹ • x)) := by
    simp [dilate, real_inner_smul_left, real_inner_smul_right,
      hR.ne']
    ring
  unfold integralFourier
  simp_rw [hpoint]
  rw [integral_smul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x : Euclidean d => Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      (inner ℝ x (R • ξ) : ℝ)) * f x) hR.le]
  simp [finrank_euclideanSpace, hR.ne']

lemma scalarFourier_dilate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (R : ℝ) (hR : 0 < R) (f : Euclidean d → 𝕜) (ξ : Euclidean d) :
    HardyLowpassSpec.scalarFourier (dilate R f) ξ =
      HardyLowpassSpec.scalarFourier f (R • ξ) := by
  unfold HardyLowpassSpec.scalarFourier
  rw [show (fun x => RCLike.map 𝕜 ℂ (dilate R f x)) =
    dilate R (fun x => RCLike.map 𝕜 ℂ (f x)) by
      funext x
      simp [dilate]]
  exact integralFourier_dilate R hR _ ξ

lemma continuous_integral_norm_translate_sub {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    Continuous (fun h : Euclidean d => ∫ x, ‖f x - f (x - h)‖) := by
  let F : Lp 𝕜 1 (volume : Measure (Euclidean d)) := hf.toL1 f
  let g : Euclidean d → C(Euclidean d, Euclidean d) :=
    fun h => ⟨fun x => x - h, continuous_id.sub continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.sub continuous_fst)
  have hc : Continuous (fun h =>
      F - Lp.compMeasurePreserving (g h) (measurePreserving_sub_right volume h) F) :=
    continuous_const.sub (continuous_const.compMeasurePreservingLp hg
      (fun h => measurePreserving_sub_right volume h) (by simp))
  convert hc.norm using 1
  ext h
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub F (Lp.compMeasurePreserving (g h)
      (measurePreserving_sub_right volume h) F),
    Lp.coeFn_compMeasurePreserving F (measurePreserving_sub_right volume h),
    hf.coeFn_toL1,
    (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toL1]
    with x hx₁ hx₂ hx₃ hx₄
  rw [hx₁]
  change ‖f x - f (x - h)‖ = ‖F x - (Lp.compMeasurePreserving
    (fun x : Euclidean d => x - h) (measurePreserving_sub_right volume h) F) x‖
  rw [hx₂]
  change ‖f x - f (x - h)‖ = ‖(hf.toL1 f) x - F (x - h)‖
  rw [hx₃]
  have hx₄' : F (x - h) = f (x - h) := hx₄
  rw [hx₄']

lemma integral_norm_translate_sub_tendsto_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    Tendsto (fun h : Euclidean d => ∫ x, ‖f x - f (x - h)‖) (𝓝 0) (𝓝 0) := by
  simpa only [sub_zero, sub_self, norm_zero, integral_zero] using
    (continuous_integral_norm_translate_sub hf).tendsto 0

lemma integral_norm_translate_sub_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {f : Euclidean d → 𝕜} (hf : Integrable f) (h : Euclidean d) :
    (∫ x, ‖f x - f (x - h)‖) ≤ 2 * ∫ x, ‖f x‖ := by
  have ht : Integrable (fun x => f (x - h)) :=
    hf.comp_sub_right h
  calc
    _ ≤ ∫ x, (‖f x‖ + ‖f (x - h)‖) :=
      integral_mono (hf.sub ht).norm (hf.norm.add ht.norm) (fun x => norm_sub_le _ _)
    _ = 2 * ∫ x, ‖f x‖ := by
      rw [integral_add hf.norm ht.norm,
        integral_sub_right_eq_self (fun x => ‖f x‖) h]
      ring



lemma convolve_dilate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (R : ℝ) (hR : 0 < R) (f g : Euclidean d → 𝕜) (x : Euclidean d) :
    convolve (dilate R f) (dilate R g) x = dilate R (convolve f g) x := by
  have hpoint (y : Euclidean d) :
      dilate R f y * dilate R g (x - y) =
        ((R ^ d)⁻¹ * (R ^ d)⁻¹) •
          (f (R⁻¹ • y) * g (R⁻¹ • x - R⁻¹ • y)) := by
    simp only [dilate, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [convolve, convolution_def, ContinuousLinearMap.mul_apply', dilate]
  change (∫ y, dilate R f y * dilate R g (x - y)) = _
  simp_rw [hpoint]
  rw [integral_smul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume
    (fun y : Euclidean d => f y * g (R⁻¹ • x - y)) hR.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_smul]
  congr 1
  field_simp

open HardyLowpassSpec in
lemma isLowpass_dilate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (hη : IsLowpass η 1) (R : ℝ) (hR : 0 < R) :
    IsLowpass (dilateSchwartz R hR η) R := by
  obtain ⟨_, hsmooth, _, hsupp, hone⟩ := hη
  have hfour : scalarFourier (dilateSchwartz R hR η) =
      (scalarFourier η) ∘ (fun ξ : Euclidean d => R • ξ) := by
    funext ξ
    exact scalarFourier_dilate R hR η ξ
  have hsub : tsupport (scalarFourier (dilateSchwartz R hR η)) ⊆
      Metric.ball 0 (2 / R) := by
    rw [hfour]
    intro ξ hξ
    have ht := tsupport_comp_subset_preimage (scalarFourier η)
      (by fun_prop : Continuous (fun ξ : Euclidean d => R • ξ)) hξ
    have hb := hsupp ht
    have hb' : R * ‖ξ‖ < 2 := by
      simpa only [div_one, Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hR] using hb
    rw [Metric.mem_ball, dist_zero_right]
    apply (lt_div_iff₀ hR).mpr
    nlinarith
  refine ⟨hR, ?_, ?_, hsub, ?_⟩
  · rw [hfour]
    exact hsmooth.comp (by fun_prop)
  · exact (isCompact_closedBall (0 : Euclidean d) (2 / R)).of_isClosed_subset
      (isClosed_tsupport _) (hsub.trans Metric.ball_subset_closedBall)
  · intro ξ hξ
    rw [hfour]
    apply hone
    have hξ' : ‖ξ‖ * R < 1 := (lt_div_iff₀ hR).mp (by
      simpa only [Metric.mem_ball, dist_zero_right] using hξ)
    simpa only [div_one, Metric.mem_ball, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hR, mul_comm] using hξ'



lemma exists_even_real_schwartz_cutoff (d : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ χ : Schwartz ℂ d,
      tsupport χ ⊆ Metric.ball 0 b ∧
      (∀ ξ ∈ Metric.ball (0 : Euclidean d) a, χ ξ = 1) ∧
      (∀ ξ, χ (-ξ) = χ ξ) ∧
      (∀ ξ, (χ ξ).im = 0) := by
  let f : ContDiffBump (0 : Euclidean d) :=
    ⟨a, (a + b) / 2, ha, by linarith⟩
  have hc : HasCompactSupport (fun x => (f x : ℂ)) :=
    f.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp f.contDiff
  refine ⟨hc.toSchwartzMap hs, ?_, ?_, ?_, ?_⟩
  · have hsub : tsupport (fun x => (f x : ℂ)) ⊆ tsupport f := by
      apply closure_mono
      intro x hx
      simpa only [Function.mem_support, Complex.ofReal_ne_zero] using hx
    apply hsub.trans
    rw [f.tsupport_eq]
    apply Metric.closedBall_subset_ball
    dsimp [f]
    linarith
  · intro ξ hξ
    change (f ξ : ℂ) = 1
    rw [f.one_of_mem_closedBall (Metric.ball_subset_closedBall hξ)]
    rfl
  · intro ξ
    change (f (-ξ) : ℂ) = (f ξ : ℂ)
    rw [f.neg]
  · intro ξ
    exact Complex.ofReal_im _

lemma fourierInv_real_of_even_real {d : ℕ} (χ : Schwartz ℂ d)
    (he : ∀ ξ, χ (-ξ) = χ ξ) (hr : ∀ ξ, (χ ξ).im = 0) :
    ∀ x, ((𝓕⁻ χ : Schwartz ℂ d) x).im = 0 := by
  intro x
  apply Complex.conj_eq_iff_im.mp
  rw [show (𝓕⁻ χ : Schwartz ℂ d) x = 𝓕⁻ (χ : Euclidean d → ℂ) x from
    congrFun (SchwartzMap.fourierInv_coe χ) x]
  rw [Real.fourierInv_eq', ← integral_conj]
  conv_rhs => rw [← integral_neg_eq_self (fun y : Euclidean d =>
    Complex.exp ((↑(2 * Real.pi * inner ℝ y x) * Complex.I)) • χ y) volume]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, inner_neg_left, he y, Complex.conj_eq_iff_im.mpr (hr y)]
  congr 2
  push_cast
  ring

/-- A real-valued complex Schwartz function viewed in either scalar field. -/
def realSchwartzLift {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Schwartz ℂ d) : Schwartz 𝕜 d :=
  (SchwartzMap.postcompCLM (RCLike.ofRealCLM (K := 𝕜)))
    (SchwartzMap.postcompCLM Complex.reCLM f)

@[simp] lemma realSchwartzLift_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Schwartz ℂ d) (x : Euclidean d) :
    realSchwartzLift (𝕜 := 𝕜) f x = ((f x).re : 𝕜) := rfl

lemma scalarFourier_realSchwartzLift {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Schwartz ℂ d) (hf : ∀ x, (f x).im = 0) :
    HardyLowpassSpec.scalarFourier (realSchwartzLift (𝕜 := 𝕜) f) = schwartzFourier f := by
  funext ξ
  rw [schwartz_integral]
  unfold HardyLowpassSpec.scalarFourier
  congr 1
  funext x
  apply Complex.ext <;> simp [RCLike.map_apply, hf x]

lemma convolve_realSchwartzLift {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u v : Schwartz ℂ d) (hu : ∀ x, (u x).im = 0) (hv : ∀ x, (v x).im = 0) (x : Euclidean d) :
    convolve (realSchwartzLift (𝕜 := 𝕜) u) (realSchwartzLift (𝕜 := 𝕜) v) x =
      ((convolve u v x).re : 𝕜) := by
  have hprod (y : Euclidean d) : u y * v (x-y) =
      (((u y).re * (v (x-y)).re : ℝ) : ℂ) := by
    have hu' := (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr (hu y))).symm
    have hv' := (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr (hv (x-y)))).symm
    rw [hu', hv']
    simp
  change (∫ y, ((u y).re : 𝕜) * ((v (x-y)).re : 𝕜)) =
    ((∫ y, u y * v (x-y)).re : 𝕜)
  simp_rw [← RCLike.ofReal_mul, hprod]
  simp only [integral_ofReal, integral_complex_ofReal, Complex.ofReal_re]

lemma exists_real_nested_cutoffs (d : ℕ) :
    ∃ η ζ : Schwartz ℂ d,
      (tsupport (schwartzFourier η) ⊆ Metric.ball 0 2) ∧
      (∀ ξ ∈ Metric.ball (0 : Euclidean d) 1, schwartzFourier η ξ = 1) ∧
      (∀ x, (η x).im = 0) ∧ (∀ x, (ζ x).im = 0) ∧
      (∀ x, convolve ζ η x = η x) := by
  obtain ⟨χ₀, hχ₀, hχ₀one, hχ₀even, hχ₀real⟩ := exists_even_real_schwartz_cutoff d
    (a := 1) (b := 2) (by norm_num) (by norm_num)
  obtain ⟨χ₁, hχ₁, hχ₁one, hχ₁even, hχ₁real⟩ := exists_even_real_schwartz_cutoff d
    (a := 2) (b := 4) (by norm_num) (by norm_num)
  let η : Schwartz ℂ d := 𝓕⁻ χ₀
  let ζ : Schwartz ℂ d := 𝓕⁻ χ₁
  have hη : schwartzFourier η = χ₀ := by
    simpa only [schwartzFourier, FourierTransform.fourierCLM_apply, η] using
      (FourierTransform.fourier_fourierInv_eq χ₀)
  have hζ : schwartzFourier ζ = χ₁ := by
    simpa only [schwartzFourier, FourierTransform.fourierCLM_apply, ζ] using
      (FourierTransform.fourier_fourierInv_eq χ₁)
  refine ⟨η, ζ, by simpa [hη] using hχ₀, ?_,
    fourierInv_real_of_even_real χ₀ hχ₀even hχ₀real,
    fourierInv_real_of_even_real χ₁ hχ₁even hχ₁real, ?_⟩
  · simpa [hη] using hχ₀one
  · have hprod : SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) ζ η = η := by
      apply (FourierTransform.fourierCLE ℂ (Schwartz ℂ d)).injective
      ext ξ
      change schwartzFourier (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) ζ η) ξ =
        schwartzFourier η ξ
      rw [Inversion.fourier_convolution, hζ, hη]
      by_cases hξ : χ₀ ξ = 0
      · simp [hξ]
      · have hm : ξ ∈ Metric.ball (0 : Euclidean d) 2 :=
          hχ₀ (subset_tsupport χ₀ (by exact hξ))
        rw [hχ₁one ξ hm, one_mul]
    intro x
    have h := congrArg (fun f : Schwartz ℂ d => f x) hprod
    simpa only [SchwartzMap.convolution_apply, convolve] using h

lemma exists_base_scalar_cutoffs {𝕜 : Type} [RCLike 𝕜] (d : ℕ) :
    ∃ η ζ : Schwartz 𝕜 d, HardyLowpassSpec.IsLowpass η 1 ∧ convolve ζ η = η := by
  obtain ⟨ηC, ζC, hsupp, hone, hrealη, hrealζ, hrepro⟩ := exists_real_nested_cutoffs d
  let η := realSchwartzLift (𝕜 := 𝕜) ηC
  let ζ := realSchwartzLift (𝕜 := 𝕜) ζC
  have hF : HardyLowpassSpec.scalarFourier η = schwartzFourier ηC :=
    scalarFourier_realSchwartzLift ηC hrealη
  refine ⟨η, ζ, ?_, ?_⟩
  · refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
    · rw [hF]
      exact (schwartzFourier ηC).smooth ⊤
    · rw [hF]
      exact (isCompact_closedBall (0 : Euclidean d) 2).of_isClosed_subset
        (isClosed_tsupport _) (hsupp.trans Metric.ball_subset_closedBall)
    · simpa [hF] using hsupp
    · simpa [hF] using hone
  · funext x
    simpa only [η, ζ, realSchwartzLift_apply, hrepro] using
      convolve_realSchwartzLift (𝕜 := 𝕜) ζC ηC hrealζ hrealη x

theorem scaled_cutoffs : HardyLowpassSpec.ScaledCutoffs := by
  intro 𝕜 _ d
  obtain ⟨η₀, ζ₀, hη₀, hrepro⟩ := exists_base_scalar_cutoffs (𝕜 := 𝕜) d
  refine ⟨η₀, ζ₀, ?_⟩
  intro R hR
  refine ⟨dilateSchwartz R hR η₀, dilateSchwartz R hR ζ₀, rfl, rfl,
    isLowpass_dilate η₀ hη₀ R hR, ?_⟩
  funext x
  change convolve (dilate R ζ₀) (dilate R η₀) x = dilate R η₀ x
  rw [convolve_dilate R hR, hrepro]



lemma integral_norm_defect_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ ζ : Euclidean d → 𝕜) (hΦ : Integrable Φ) (hζ : Integrable ζ)
    (hc : (∫ y, Φ y) ≠ 0) :
    (∫ x, ‖ζ x - (∫ y, Φ y)⁻¹ * convolve Φ ζ x‖) ≤
      ‖(∫ y, Φ y)⁻¹‖ * ∫ y, ‖Φ y‖ * (∫ x, ‖ζ x - ζ (x-y)‖) := by
  let F : Euclidean d × Euclidean d → 𝕜 :=
    fun p => Φ p.2 * (ζ p.1 - ζ (p.1-p.2))
  have hF : Integrable F (volume.prod volume) := by
    have h₁ := (hζ.mul_prod hΦ)
    have h₂ := hΦ.convolution_integrand (ContinuousLinearMap.mul 𝕜 𝕜) hζ
    apply (h₁.sub h₂).congr
    filter_upwards [] with p
    change ζ p.1 * Φ p.2 - Φ p.2 * ζ (p.1-p.2) = Φ p.2 * (ζ p.1 - ζ (p.1-p.2))
    ring
  have hh : Integrable (fun x => ζ x - (∫ y, Φ y)⁻¹ * convolve Φ ζ x) :=
    hζ.sub ((hΦ.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜) hζ).const_mul _)
  have heq (x : Euclidean d) (hxi : Integrable (fun y => F (x,y))) :
      ζ x - (∫ y, Φ y)⁻¹ * convolve Φ ζ x = (∫ y, Φ y)⁻¹ * ∫ y, F (x,y) := by
    have hconst : Integrable (fun y => Φ y * ζ x) := hΦ.mul_const _
    have hconv : Integrable (fun y => Φ y * ζ (x-y)) := by
      convert hconst.sub hxi using 1
      ext y
      simp [F, mul_sub]
    simp only [F, mul_sub]
    rw [integral_sub hconst hconv, integral_mul_const, mul_sub,
      ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rfl
  calc
    _ ≤ ∫ x, ‖(∫ y, Φ y)⁻¹‖ * ∫ y, ‖F (x,y)‖ := by
      apply integral_mono_ae hh.norm (hF.integral_norm_prod_left.const_mul _)
      filter_upwards [hF.prod_right_ae] with x hx
      rw [heq x hx, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = ‖(∫ y, Φ y)⁻¹‖ * ∫ y, ∫ x, ‖F (x,y)‖ := by
      rw [integral_const_mul, integral_integral_swap hF.norm]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [F, norm_mul, integral_const_mul]

lemma integral_norm_dilate_translate_sub {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (ζ : Euclidean d → 𝕜) {R : ℝ} (hR : 0 < R) (y : Euclidean d) :
    (∫ x, ‖dilate R ζ x - dilate R ζ (x-y)‖) =
      ∫ x, ‖ζ x - ζ (x-R⁻¹ • y)‖ := by
  have heq : (fun x => ‖dilate R ζ x - dilate R ζ (x-y)‖) =
      fun x => (R ^ d)⁻¹ * ‖ζ (R⁻¹ • x) - ζ (R⁻¹ • x - R⁻¹ • y)‖ := by
    ext x
    simp only [dilate, smul_sub]
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hR.le _))]
  rw [heq, integral_const_mul]
  change (R ^ d)⁻¹ * (∫ x, (fun z => ‖ζ z - ζ (z-R⁻¹ • y)‖) (R⁻¹ • x)) = _
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun z => ‖ζ z - ζ (z-R⁻¹ • y)‖) hR.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d hR.ne'), one_mul]

lemma weightedNorm_sub_mul_finite {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u v : Euclidean d → 𝕜) (c : 𝕜)
    (hu : weightedNorm u < ∞) (hv : weightedNorm v < ∞) :
    weightedNorm (fun x => u x - c * v x) < ∞ := by
  have hu' : weightedNorm u ≤ ENNReal.ofReal (weightedNorm u).toReal := by
    rw [ENNReal.ofReal_toReal hu.ne]
  have hv' : weightedNorm v ≤ ENNReal.ofReal (weightedNorm v).toReal := by
    rw [ENNReal.ofReal_toReal hv.ne]
  apply lt_of_le_of_lt (weighted_bound_of_decay _ (C :=
    (weightedNorm u).toReal + ‖c‖ * (weightedNorm v).toReal) ?_) ENNReal.ofReal_lt_top
  intro x
  calc
    ‖u x - c * v x‖ ≤ ‖u x‖ + ‖c‖ * ‖v x‖ := by simpa only [norm_mul] using norm_sub_le (u x) (c * v x)
    _ ≤ (weightedNorm u).toReal * (1 + ‖x‖) ^ (-(d : ℝ) - 1 / 2) +
        ‖c‖ * ((weightedNorm v).toReal * (1 + ‖x‖) ^ (-(d : ℝ) - 1 / 2)) :=
      add_le_add (decay_of_weighted_bound u ENNReal.toReal_nonneg hu' x)
        (mul_le_mul_of_nonneg_left (decay_of_weighted_bound v ENNReal.toReal_nonneg hv' x) (norm_nonneg _))
    _ = _ := by ring

lemma slow_translation_integral_tendsto_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ ζ : Euclidean d → 𝕜) (hΦ : Integrable Φ) (hζ : Integrable ζ) :
    Tendsto (fun t : ℝ => ∫ y, ‖Φ y‖ * (∫ x, ‖ζ x - ζ (x-t • y)‖))
      (𝓝[>] 0) (𝓝 0) := by
  have hT := continuous_integral_norm_translate_sub hζ
  have ht (y : Euclidean d) : Tendsto (fun t : ℝ => t • y) (𝓝[>] 0) (𝓝 0) := by
    have hs : Continuous (fun t : ℝ => t • y) := continuous_id.smul continuous_const
    simpa using (hs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlim : ∀ᵐ y : Euclidean d ∂volume,
      Tendsto (fun t : ℝ => ‖Φ y‖ * (∫ x, ‖ζ x - ζ (x-t • y)‖))
        (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [] with y
    simpa using (tendsto_const_nhds (x := ‖Φ y‖)).mul ((integral_norm_translate_sub_tendsto_zero hζ).comp (ht y))
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun y : Euclidean d => ‖Φ y‖ * (∫ x, ‖ζ x - ζ (x-t • y)‖)) volume := by
    have hsmul : Continuous (fun y : Euclidean d => t • y) := by fun_prop
    exact hΦ.norm.aestronglyMeasurable.mul (hT.comp hsmul).aestronglyMeasurable
  have hbound (t : ℝ) : ∀ᵐ y : Euclidean d ∂volume,
      ‖‖Φ y‖ * (∫ x, ‖ζ x - ζ (x-t • y)‖)‖ ≤ ‖Φ y‖ * (2 * ∫ x, ‖ζ x‖) := by
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (integral_nonneg fun x => norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (integral_norm_translate_sub_le hζ (t • y)) (norm_nonneg _)
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (μ := (volume : Measure (Euclidean d)))
    (F := fun t : ℝ => fun y : Euclidean d => ‖Φ y‖ * (∫ x, ‖ζ x - ζ (x-t • y)‖))
    (f := fun _ : Euclidean d => (0 : ℝ))
    (fun y => ‖Φ y‖ * (2 * ∫ x, ‖ζ x‖))
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall hbound)
    (hΦ.norm.mul_const _) hlim
  simpa using hdct

theorem dilation_defect : HardyLowpassSpec.DilationDefect := by
  intro 𝕜 _ d hd Φ hΦ hΦw hc ζ ε hε
  have ht' : Tendsto (fun t : ℝ => ‖(∫ y, Φ y)⁻¹‖ *
      ∫ y, ‖Φ y‖ * (∫ x, ‖ζ x - ζ (x-t • y)‖)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ‖(∫ y, Φ y)⁻¹‖)).mul
      (slow_translation_integral_tendsto_zero Φ ζ hΦ ζ.integrable)
  have hsmall := ht'.eventually (gt_mem_nhds hε)
  have htpos' : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, htpos, htsmall⟩ := (htpos'.and hsmall).exists
  refine ⟨t⁻¹, inv_pos.mpr htpos, ?_⟩
  have hζi := dilate_schwartz_integrable t⁻¹ (inv_pos.mpr htpos) ζ
  have hζw := dilate_schwartz_weighted t⁻¹ (inv_pos.mpr htpos) ζ
  have hcvi : Integrable (convolve Φ (dilate t⁻¹ ζ)) :=
    hΦ.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜) hζi
  have hcvw : weightedNorm (convolve Φ (dilate t⁻¹ ζ)) < ∞ := by
    apply lt_of_le_of_lt (HardyWeightedKernel.weighted_convolution hd _ _ hΦ hζi hΦw hζw)
    finiteness
  refine ⟨hζi.sub (hcvi.const_mul _),
    weightedNorm_sub_mul_finite _ _ _ hζw hcvw, ?_⟩
  apply lt_of_le_of_lt (integral_norm_defect_le Φ (dilate t⁻¹ ζ) hΦ hζi hc)
  simpa only [integral_norm_dilate_translate_sub _ (inv_pos.mpr htpos), inv_inv] using htsmall

/-- Slow dilation produces the small defect used by the weighted inverse. -/
theorem small_defect : HardyLowpassSpec.SmallDefect :=
  small_defect_of_scaled_cutoffs_and_dilation scaled_cutoffs dilation_defect

/-- The low-frequency convolution inverse with the manuscript's pointwise decay. -/
theorem lowpass_inverse : HardyLowpassSpec.LowpassInverse :=
  lowpass_inverse_of_small_defect small_defect

end ExpandedFA.PartIV.HardyLowpass
