import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.MinkowskiIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch10.LpDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch08.Fubini
import Mathlib.MeasureTheory.Integral.MeanInequalities

open Set MeasureTheory
open scoped ENNReal NNReal
universe u v
noncomputable section
namespace D11.Ch10.MinkowskiIntegral

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]

/-- Cancel the finite truncated power integral in the Hölder estimate. -/
lemma root_le_of_le_mul (p q : ℝ) (hpq : p.HolderConjugate q)
    (B A : ℝ≥0∞) (hBt : B ≠ ∞) (h : B ≤ A * B ^ (1 / q)) :
    B ^ (1 / p) ≤ A := by
  by_cases hB0 : B = 0
  · rw [hB0, ENNReal.zero_rpow_of_pos hpq.one_div_pos]
    exact bot_le
  have hq : 1 / q = 1 - 1 / p := by
    have hh := hpq.inv_add_inv_eq_one
    simp only [one_div] at *
    linarith
  have hBroot0 : B ^ (1 / p) ≠ 0 := by simp [hB0, hBt]
  have hBroott : B ^ (1 / p) ≠ ∞ := by finiteness
  suffices hh : 1 ≤ B ^ (-(1 / p)) * A by
    rwa [← ENNReal.mul_le_mul_iff_right hBroot0 hBroott, ← mul_assoc,
      ← ENNReal.rpow_add _ _ hB0 hBt, add_neg_cancel, ENNReal.rpow_zero,
      one_mul, mul_one] at hh
  rw [hq, sub_eq_add_neg, ENNReal.rpow_add _ _ hB0 hBt, ENNReal.rpow_one] at h
  conv_rhs at h => enter [2]; rw [mul_comm]
  conv_lhs at h => rw [← one_mul B]
  rwa [← mul_assoc, ENNReal.mul_le_mul_iff_left hB0 hBt, mul_comm] at h

/-- The estimate for a bounded finite-support truncation of the inner integral. -/
lemma truncated_bound (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (p q : ℝ) (hpq : p.HolderConjugate q) (F : X × Y → ℝ≥0∞)
    (hF : Measurable F) (t : X → ℝ≥0∞) (ht : Measurable t)
    (htu : ∀ x, t x ≤ ∫⁻ y, F (x,y) ∂ν)
    (htfin : (∫⁻ x, t x ^ p ∂μ) ≠ ∞) :
    (∫⁻ x, t x ^ p ∂μ) ^ (1 / p) ≤
      ∫⁻ y, (∫⁻ x, F (x,y) ^ p ∂μ) ^ (1 / p) ∂ν := by
  apply root_le_of_le_mul p q hpq _ _ htfin
  calc
    (∫⁻ x, t x ^ p ∂μ) ≤ ∫⁻ x, (∫⁻ y, F (x,y) ∂ν) * t x ^ (p-1) ∂μ := by
      apply lintegral_mono
      intro x
      calc
        t x ^ p = t x * t x ^ (p-1) := by
          nth_rw 2 [← ENNReal.rpow_one (t x)]
          rw [← ENNReal.rpow_add_of_nonneg 1 (p-1) zero_le_one
            hpq.sub_one_pos.le, add_sub_cancel]
        _ ≤ _ := mul_le_mul' (htu x) le_rfl
    _ = ∫⁻ x, ∫⁻ y, F (x,y) * t x ^ (p-1) ∂ν ∂μ := by
      congr 1
      funext x
      exact (lintegral_mul_const _ (hF.comp measurable_prodMk_left)).symm
    _ = ∫⁻ y, ∫⁻ x, F (x,y) * t x ^ (p-1) ∂μ ∂ν :=
      lintegral_lintegral_swap (hF.mul ((ht.comp measurable_fst).pow_const _)).aemeasurable
    _ ≤ ∫⁻ y, (∫⁻ x, F (x,y) ^ p ∂μ) ^ (1 / p) *
        (∫⁻ x, t x ^ p ∂μ) ^ (1 / q) ∂ν := by
      apply lintegral_mono
      intro y
      exact ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq
        (hF.comp measurable_prodMk_right).aemeasurable ht.aemeasurable
    _ = _ := lintegral_mul_const _
      ((hF.pow_const p).lintegral_prod_left.pow_const (1/p))

/-- Positive powers preserve the increasing approximation suprema, including infinity. -/
lemma rpow_iSup (a : ℕ → ℝ≥0∞) (p : ℝ) (hp : 0 < p) :
    (⨆ n, a n) ^ p = ⨆ n, (a n) ^ p :=
  (ENNReal.orderIsoRpow p hp).map_iSup a

lemma integral_root_iSup (μ : Measure X) (p : ℝ) (hp : 0 < p)
    (f : ℕ → X → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    (∫⁻ x, (⨆ n, f n x) ^ p ∂μ) ^ (1/p) =
      ⨆ n, (∫⁻ x, f n x ^ p ∂μ) ^ (1/p) := by
  simp_rw [rpow_iSup _ p hp]
  rw [lintegral_iSup (fun n => (hf n).pow_const p)
    (fun i j hij x => ENNReal.rpow_le_rpow (hmono hij x) hp.le)]
  exact rpow_iSup _ (1/p) (one_div_pos.mpr hp)

/-- Minkowski's integral inequality for arbitrary nonnegative extended-valued
functions on the ordinary product. All displayed integrals are extended. -/
theorem lintegral_minkowski (μ : Measure X) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] (p : ℝ) (hp : 1 ≤ p)
    (F : X × Y → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, (∫⁻ y, F (x,y) ∂ν) ^ p ∂μ) ^ (1/p) ≤
      ∫⁻ y, (∫⁻ x, F (x,y) ^ p ∂μ) ^ (1/p) ∂ν := by
  classical
  rcases hp.eq_or_lt with hp | hp
  · subst p
    simpa using (lintegral_lintegral_swap (μ := μ) (ν := ν)
      (f := fun x y => F (x,y)) hF.aemeasurable).le
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let q := p / (p-1)
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  let u : X → ℝ≥0∞ := fun x => ∫⁻ y, F (x,y) ∂ν
  have hu : Measurable u := hF.lintegral_prod_right'
  let A := ∫⁻ y, (∫⁻ x, F (x,y) ^ p ∂μ) ^ (1/p) ∂ν
  have bound_on_set (D : Set X) (hD : MeasurableSet D) (hDfin : μ D < ∞) :
      (∫⁻ x, (D.indicator u x) ^ p ∂μ) ^ (1/p) ≤ A := by
    let t : ℕ → X → ℝ≥0∞ := fun n => D.indicator (fun x => min (u x) n)
    have ht (n : ℕ) : Measurable (t n) := (hu.min measurable_const).indicator hD
    have htmono : Monotone t := by
      intro i j hij x
      by_cases hx : x ∈ D
      · simp only [t, indicator_of_mem hx]
        exact min_le_min_left _ (Nat.cast_le.mpr hij)
      · simp [t, hx]
    have htsup (x : X) : (⨆ n, t n x) = D.indicator u x := by
      by_cases hx : x ∈ D
      · simp only [t, indicator_of_mem hx]
        rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
      · simp [t, hx]
    have hbound (n : ℕ) : (∫⁻ x, t n x ^ p ∂μ) ^ (1/p) ≤ A := by
      apply truncated_bound μ ν p q hpq F hF (t n) (ht n)
      · intro x
        by_cases hx : x ∈ D
        · change D.indicator (fun x => min (u x) n) x ≤ u x
          rw [indicator_of_mem hx]
          exact min_le_left _ _
        · simp [t, hx]
      · apply ne_top_of_le_ne_top (b := (n : ℝ≥0∞) ^ p * μ D)
          (ENNReal.mul_ne_top (by finiteness) hDfin.ne)
        calc
          (∫⁻ x, t n x ^ p ∂μ) ≤ ∫⁻ x, D.indicator (fun _ => (n : ℝ≥0∞) ^ p) x ∂μ := by
            apply lintegral_mono
            intro x
            by_cases hx : x ∈ D
            · simp only [t, indicator_of_mem hx]
              exact ENNReal.rpow_le_rpow (min_le_right _ _) hp0.le
            · simp [t, hx, ENNReal.zero_rpow_of_pos hp0]
          _ = _ := lintegral_indicator_const hD _
    calc
      _ = (∫⁻ x, (⨆ n, t n x) ^ p ∂μ) ^ (1/p) := by simp_rw [htsup]
      _ = _ := integral_root_iSup μ p hp0 t ht htmono
      _ ≤ A := iSup_le hbound
  have hmono : Monotone (fun n => (spanningSets μ n).indicator u) := by
    intro i j hij x
    by_cases hx : x ∈ spanningSets μ i
    · simp [hx, monotone_spanningSets μ hij hx]
    · simp only [indicator_of_notMem hx]
      exact bot_le
  have hsup (x : X) : (⨆ n, (spanningSets μ n).indicator u x) = u x := by
    apply le_antisymm
    · exact iSup_le (fun n => indicator_le_self' (fun _ _ => bot_le) x)
    · obtain ⟨n, hn⟩ := mem_iUnion.mp (show x ∈ ⋃ n, spanningSets μ n by
        rw [iUnion_spanningSets]; trivial)
      exact le_iSup_of_le n (by simp [hn])
  calc
    _ = (∫⁻ x, (⨆ n, (spanningSets μ n).indicator u x) ^ p ∂μ) ^ (1/p) := by
      simp_rw [hsup]; rfl
    _ = _ := integral_root_iSup μ p hp0 _
      (fun n => hu.indicator (measurableSet_spanningSets μ n)) hmono
    _ ≤ A := iSup_le (fun n => bound_on_set _ (measurableSet_spanningSets μ n)
      (measure_spanningSets_lt_top μ n))

open D11.Ch05.NonnegativeIntegral D11.Ch10.LpDefinition
open D11.Ch06.ScalarIntegral D11.Ch08.Fubini
open D11.Ch04.AeCommonException

/-- The shared finite-power formula written using extended norms. -/
lemma powerNorm_lintegral {𝕜 : Type} [NormedAddCommGroup 𝕜]
    (μ : Measure X) (p : ℝ) (hp : 0 ≤ p) (f : X → 𝕜) :
    powerNorm μ p f = (∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) ^ (1/p) := by
  rw [powerNorm, integral_eq_lintegral]
  congr 2
  funext x
  exact (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp).symm

/-- The full nonnegative theorem using the source integral and its measurable
section maps, with no finiteness restriction on either side. -/
theorem nonnegative_minkowski : Specs.D11.Ch10.MinkowskiIntegral.nonnegative_minkowski.{u,v} := by
  intro X Y _ _ μ ν hμ hν p hp F hF
  let : SigmaFinite μ := hμ
  let : SigmaFinite ν := hν
  change Measurable (fun y => (nonnegativeIntegral μ (fun x => F (x,y) ^ p)) ^ (1/p)) ∧
    Measurable (fun x => nonnegativeIntegral ν (fun y => F (x,y))) ∧
    (nonnegativeIntegral μ (fun x => (nonnegativeIntegral ν (fun y => F (x,y))) ^ p)) ^ (1/p) ≤
      nonnegativeIntegral ν (fun y => (nonnegativeIntegral μ (fun x => F (x,y) ^ p)) ^ (1/p))
  simp_rw [integral_eq_lintegral]
  exact ⟨(hF.pow_const p).lintegral_prod_left'.pow_const (1/p),
    hF.lintegral_prod_right', lintegral_minkowski μ ν p hp F hF⟩

/-- The scalar theorem: actual absolute section integrability, a measurable
null exceptional set, and the bound on the canonical zero-extended integral. -/
theorem scalar_minkowski : Specs.D11.Ch10.MinkowskiIntegral.scalar_minkowski.{u,v} := by
  intro X Y 𝕜 _ _ _ _ _ μ ν hμ hν p hp F hF hA
  let : SigmaFinite μ := hμ
  let : SigmaFinite ν := hν
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let H : X × Y → ℝ≥0∞ := fun z => ENNReal.ofReal ‖F z‖
  have hH : Measurable H := hF.norm.ennreal_ofReal
  let u : X → ℝ≥0∞ := fun x => ∫⁻ y, H (x,y) ∂ν
  have hu : Measurable u := hH.lintegral_prod_right'
  let A : ℝ≥0∞ := ∫⁻ y, (∫⁻ x, H (x,y) ^ p ∂μ) ^ (1/p) ∂ν
  have hAeq : nonnegativeIntegral ν (fun y => powerNorm μ p (fun x => F (x,y))) = A := by
    rw [integral_eq_lintegral]
    apply lintegral_congr
    intro y
    exact powerNorm_lintegral μ p hp0.le _
  change nonnegativeIntegral ν (fun y => powerNorm μ p (fun x => F (x,y))) < ∞ at hA
  have hAt : A < ∞ := hAeq ▸ hA
  have hbound : (∫⁻ x, u x ^ p ∂μ) ^ (1/p) ≤ A :=
    lintegral_minkowski μ ν p hp H hH
  have hpower : (∫⁻ x, u x ^ p ∂μ) < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.mpr hp0)).mp (hbound.trans_lt hAt)
  have hu_ae : ∀ᵐ x ∂μ, u x < ∞ := by
    filter_upwards [ae_lt_top (hu.pow_const p) hpower.ne] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos hp0).mp hx
  have hi (x : X) : scalarIntegrable ν (fun y => F (x,y)) ↔ u x < ∞ := by
    change (Measurable (fun y => F (x,y)) ∧
      nonnegativeIntegral ν (fun y => ENNReal.ofReal ‖F (x,y)‖) < ∞) ↔ _
    rw [integral_eq_lintegral]
    exact and_iff_right (hF.comp measurable_prodMk_left)
  have hi_ae : ∀ᵐ x ∂μ, scalarIntegrable ν (fun y => F (x,y)) :=
    hu_ae.mono (fun x hx => (hi x).mpr hx)
  have hbad : {x | ¬ scalarIntegrable ν (fun y => F (x,y))} = {x | u x = ∞} := by
    ext x
    change (¬ scalarIntegrable ν (fun y => F (x,y))) ↔ u x = ∞
    rw [hi]
    exact not_lt_top_iff
  have hbadm : MeasurableSet {x | ¬ scalarIntegrable ν (fun y => F (x,y))} := by
    rw [hbad]
    exact measurableSet_eq_fun hu measurable_const
  have hbad0 : μ {x | ¬ scalarIntegrable ν (fun y => F (x,y))} = 0 :=
    ae_iff.mp hi_ae
  let g := sectionIntegralLeft ν F
  have hgeq : g = fun x => ∫ y, F (x,y) ∂ν := sectionIntegralLeft_eq_integral ν F hF
  have hg : Measurable g := by
    rw [hgeq]
    exact hF.stronglyMeasurable.integral_prod_right'.measurable
  have hdom (x : X) : ENNReal.ofReal ‖g x‖ ≤ u x := by
    rw [hgeq]
    simpa only [u, H, ofReal_norm] using
      (enorm_integral_le_lintegral_enorm (μ := ν) (fun y => F (x,y)))
  have hgnorm : powerNorm μ p g ≤ A := by
    rw [powerNorm_lintegral μ p hp0.le g]
    exact (ENNReal.rpow_le_rpow
      (lintegral_mono fun x => ENNReal.rpow_le_rpow (hdom x) hp0.le)
      (one_div_pos.mpr hp0).le).trans hbound
  have hnormm : Measurable (fun y => powerNorm μ p (fun x => F (x,y))) := by
    simp_rw [powerNorm_lintegral μ p hp0.le]
    exact (hH.pow_const p).lintegral_prod_left'.pow_const (1/p)
  refine ⟨hnormm, (almostEverywhere_iff_native μ _).mpr hi_ae,
    hbadm, hbad0, ?_, ?_⟩
  · change Measurable g ∧ powerNorm μ p g < ∞
    exact ⟨hg, hgnorm.trans_lt hAt⟩
  · change powerNorm μ p g ≤ nonnegativeIntegral ν
      (fun y => powerNorm μ p (fun x => F (x,y)))
    rw [hAeq]
    exact hgnorm

end D11.Ch10.MinkowskiIntegral
