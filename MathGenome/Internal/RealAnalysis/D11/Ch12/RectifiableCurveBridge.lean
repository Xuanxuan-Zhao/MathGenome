import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.RectifiableCurveBridge
import MathGenome.Internal.RealAnalysis.D11.Ch12.CurveLength
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcFtc
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 800000
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace D11.Ch12.RectifiableCurveBridge

def CoordinatesAC : Specs.D11.Ch12.RectifiableCurveBridge.CoordinatesAC_type :=
  Specs.D11.Ch12.RectifiableCurveBridge.CoordinatesAC_value

noncomputable def extendedLength : Specs.D11.Ch12.RectifiableCurveBridge.extendedLength_type :=
  Specs.D11.Ch12.RectifiableCurveBridge.extendedLength_value

noncomputable def arcLengthMeasure : Specs.D11.Ch12.RectifiableCurveBridge.arcLengthMeasure_type :=
  Specs.D11.Ch12.RectifiableCurveBridge.arcLengthMeasure_value

noncomputable def arcLengthIntegral : Specs.D11.Ch12.RectifiableCurveBridge.arcLengthIntegral_type :=
  Specs.D11.Ch12.RectifiableCurveBridge.arcLengthIntegral_value

variable {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a b : ℝ}

theorem rectifiable_iff (_hab : a < b) (_hc : ContinuousOn γ (Icc a b)) :
    Rectifiable γ a b ↔ ∀ i, BV (fun t => γ t i) a b :=
  rectifiable_iff_coordinates_bv γ a b

lemma coordinate_ftc (hab : a < b) (hAC : CoordinatesAC γ a b) (i : Fin d) :
    (∀ᵐ t ∂volume, t ∈ Ioo a b →
      HasDerivAt (fun s => γ s i) (deriv (fun s => γ s i) t) t) ∧
    IntegrableOn (deriv (fun s => γ s i)) (Icc a b) ∧
    ∀ t ∈ Icc a b, γ t i = γ a i + ∫ s in a..t, deriv (fun s => γ s i) s :=
  ((AcFtc.ftc_real (fun t => γ t i) hab).2.1.mp (hAC i))

/-- Coordinate FTCs use a common exceptional set before forming the vector. -/
theorem vector_ftc (hab : a < b) (hAC : CoordinatesAC γ a b) :
    IntegrableOn (deriv γ) (Icc a b) ∧
    (∀ᵐ t ∂volume, t ∈ Ioo a b →
      HasDerivAt γ (deriv γ t) t ∧
      ∀ i, HasDerivAt (fun s => γ s i) (deriv γ t i) t) ∧
    ∀ t ∈ Icc a b, γ t = γ a + ∫ s in a..t, deriv γ s := by
  let v : ℝ → EuclideanSpace ℝ (Fin d) :=
    fun t => WithLp.toLp 2 (fun i => deriv (fun s => γ s i) t)
  have hi : IntegrableOn v (Icc a b) :=
    integrable_piLp_iff.mpr (fun i => (coordinate_ftc γ hab hAC i).2.1)
  have hd : ∀ᵐ t ∂volume, t ∈ Ioo a b →
      HasDerivAt γ (v t) t := by
    have hall := (ae_all_iff.mpr (fun i : Fin d => (coordinate_ftc γ hab hAC i).1))
    filter_upwards [hall] with t ht hti
    have hp : HasDerivAt (fun t i => γ t i)
        (fun i => deriv (fun s => γ s i) t) t :=
      hasDerivAt_pi.mpr (fun i => ht i hti)
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp
  have heq : v =ᵐ[volume.restrict (Icc a b)] deriv γ := by
    rw [Filter.EventuallyEq, ← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hd] with t ht hti
    exact (ht hti).deriv.symm
  have hig : IntegrableOn (deriv γ) (Icc a b) := hi.congr heq
  refine ⟨hig, ?_, ?_⟩
  · filter_upwards [hd] with t ht hti
    have ht' := ht hti
    refine ⟨ht'.deriv ▸ ht', ?_⟩
    intro i
    exact (PiLp.proj 2 (fun _ : Fin d => ℝ) i).hasFDerivAt.comp_hasDerivAt t
      (ht'.deriv ▸ ht')
  · intro t ht
    have hint : IntervalIntegrable (deriv γ) volume a t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
        (hig.mono_set (Icc_subset_Icc le_rfl ht.2))
    have hiv : IntervalIntegrable v volume a t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
        (hi.mono_set (Icc_subset_Icc le_rfl ht.2))
    have hint_eq : (∫ s in a..t, deriv γ s) = ∫ s in a..t, v s := by
      apply intervalIntegral.integral_congr_ae_restrict
      exact ae_restrict_of_ae_restrict_of_subset (by
        rw [uIoc_of_le ht.1]
        exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2)) heq.symm
    rw [hint_eq]
    ext i
    rw [PiLp.add_apply]
    have hei : (∫ s in a..t, v s) i = ∫ s in a..t, deriv (fun s => γ s i) s := by
      rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
      exact eval_integral_piLp (fun i => hiv.1.eval_piLp i) i
    rw [hei]
    exact (coordinate_ftc γ hab hAC i).2.2 t ht

lemma ac_rectifiable (hab : a ≤ b) (hAC : CoordinatesAC γ a b) : Rectifiable γ a b :=
  (rectifiable_iff_coordinates_bv γ a b).mpr (fun i => AcBasic.bv hab (hAC i))

/-- Coordinate variations control increments of the Euclidean length function. -/
lemma length_increment_le_coordinate_variations (hR : Rectifiable γ a b)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    ‖realLengthFunction γ a y - realLengthFunction γ a x‖ ≤
      ‖(∑ i : Fin d, (variationFunction (fun t => γ t i) a y).toReal) -
        ∑ i : Fin d, (variationFunction (fun t => γ t i) a x).toReal‖ := by
  have hc : ∀ i : Fin d, BV (fun t => γ t i) a b :=
    (rectifiable_iff_coordinates_bv γ a b).mp hR
  have hfin (i : Fin d) {u v : ℝ} (hu : a ≤ u) (hv : v ≤ b) :
      variation (fun t => γ t i) u v ≠ ⊤ := by
    apply ne_top_of_le_ne_top (hc i).ne
    rw [variation_eq_eVariationOn, variation_eq_eVariationOn]
    exact eVariationOn.mono _ (Icc_subset_Icc hu hv)
  rw [lengthFunction_subinterval γ hR hx.1 hxy hy.2,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hle := ENNReal.toReal_mono
    (show (∑ i : Fin d, variation (fun t => γ t i) x y) ≠ ⊤ from
      ENNReal.sum_ne_top.mpr (fun i _ => hfin i hx.1 hy.2))
    (length_le_sum_coordinate_variation γ x y)
  rw [ENNReal.toReal_sum (fun i _ => hfin i hx.1 hy.2)] at hle
  refine hle.trans ?_
  have heq : (∑ i : Fin d, (variation (fun t => γ t i) x y).toReal) =
      (∑ i : Fin d, (variationFunction (fun t => γ t i) a y).toReal) -
        ∑ i : Fin d, (variationFunction (fun t => γ t i) a x).toReal := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [variationFunction]
    rw [variation_additive _ hx.1 hxy,
      ENNReal.toReal_add (hfin i le_rfl hx.2) (hfin i hx.1 hy.2)]
    simp
  rw [heq, Real.norm_eq_abs]
  exact le_abs_self _

/-- The actual Euclidean length function is AC, using one scalar sum to control
all its increments. This proof does not assume the speed integral formula. -/
theorem length_ac (hab : a < b) (hAC : CoordinatesAC γ a b) :
    AbsolutelyContinuousOnInterval (realLengthFunction γ a) a b := by
  have hR := ac_rectifiable γ hab.le hAC
  have hsum : AbsolutelyContinuousOnInterval
      (fun t => ∑ i : Fin d, (variationFunction (fun t => γ t i) a t).toReal) a b := by
    simpa only [one_mul] using AcBasic.finite_linear_combination
      (Finset.univ : Finset (Fin d)) (fun _ => (1 : ℝ))
      (fun i t => (variationFunction (fun s => γ s i) a t).toReal) hab.le
      (fun i _ => AcBasic.variation_ac hab.le (hAC i))
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := hsum ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n u v huv hends hdis hlen
  exact (Finset.sum_le_sum (fun j _ =>
    length_increment_le_coordinate_variations γ hR (hends j).1 (hends j).2 (huv j).le)).trans_lt
      (hh n u v huv hends hdis hlen)

lemma speed_integrable (hab : a < b) (hAC : CoordinatesAC γ a b) :
    IntegrableOn (fun t => ‖deriv γ t‖) (Icc a b) :=
  (vector_ftc γ hab hAC).1.norm

lemma vector_increment (hab : a < b) (hAC : CoordinatesAC γ a b)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    γ y - γ x = ∫ t in x..y, deriv γ t := by
  have hf := vector_ftc γ hab hAC
  have hi (t : ℝ) (ht : t ∈ Icc a b) : IntervalIntegrable (deriv γ) volume a t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
      (hf.1.mono_set (Icc_subset_Icc le_rfl ht.2))
  rw [hf.2.2 y hy, hf.2.2 x hx, add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left (hi y hy) (hi x hx)

/-- Summing the norm bound for vector integrals over any strict partition gives
the upper length bound. -/
lemma length_le_integral_speed (hab : a < b) (hAC : CoordinatesAC γ a b) :
    curveLength γ a b ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
  have hi := speed_integrable γ hab hAC
  have his {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      IntervalIntegrable (fun t => ‖deriv γ t‖) volume x y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr
      (hi.mono_set (Icc_subset_Icc hx.1 hy.2))
  apply iSup_le
  intro p
  have hm (j : ℕ) (hj : j < p.length) : p.point j ≤ p.point (j+1) :=
    p.strictMono.monotoneOn (by simp; omega) (by simp; omega) (Nat.le_succ _)
  calc
    partitionSum γ p = ENNReal.ofReal
        (∑ j ∈ Finset.range p.length, ‖γ (p.point (j+1)) - γ (p.point j)‖) := by
      rw [ENNReal.ofReal_sum_of_nonneg (by intros; positivity)]
      simp only [partitionSum, ofReal_norm]
    _ ≤ ENNReal.ofReal (∑ j ∈ Finset.range p.length,
        ∫ t in p.point j..p.point (j+1), ‖deriv γ t‖) := by
      apply ENNReal.ofReal_le_ofReal
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [vector_increment γ hab hAC
        (AcBasic.partition_point_mem p (by omega)) (AcBasic.partition_point_mem p (by omega))]
      exact intervalIntegral.norm_integral_le_integral_norm (hm j hj')
    _ = ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
      congr 1
      have h := intervalIntegral.sum_integral_adjacent_intervals
        (a := p.point) (n := p.length) (fun j hj => his
          (AcBasic.partition_point_mem p (by omega)) (AcBasic.partition_point_mem p (by omega))
          (hm j hj))
      simpa only [p.start, p.finish] using h

/-- A right secant of the curve is bounded by the corresponding length
increment; passing to derivatives supplies the reverse integral inequality. -/
lemma speed_le_length_derivative (hR : Rectifiable γ a b) {t : ℝ}
    (ht : t ∈ Ioo a b)
    (hγ : HasDerivAt γ (deriv γ t) t)
    (hL : HasDerivAt (realLengthFunction γ a) (deriv (realLengthFunction γ a) t) t) :
    ‖deriv γ t‖ ≤ deriv (realLengthFunction γ a) t := by
  have hγlim := hγ.tendsto_slope.norm.mono_left (nhdsGT_le_nhdsNE t)
  have hLlim := hL.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)
  apply le_of_tendsto_of_tendsto hγlim hLlim
  have hmem : ∀ᶠ y in 𝓝[>] t, y ∈ Ioo t b :=
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2))
  filter_upwards [hmem] with y hy
  have hinc : ‖γ y - γ t‖ ≤ realLengthFunction γ a y - realLengthFunction γ a t := by
    rw [lengthFunction_subinterval γ hR ht.1.le hy.1.le hy.2.le]
    exact norm_sub_le_variation γ hy.1.le (rectifiable_subinterval γ hR ht.1.le hy.2.le)
  simp only [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (sub_pos.mpr hy.1), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hinc (inv_nonneg.mpr (sub_nonneg.mpr hy.1.le))

/-- FTC for the AC length function closes the lower bound. -/
lemma length_eq_integral_speed (hab : a < b) (hAC : CoordinatesAC γ a b) :
    curveLength γ a b = ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
  have hR := ac_rectifiable γ hab.le hAC
  have hγ := vector_ftc γ hab hAC
  have hL := (AcFtc.ftc_real (realLengthFunction γ a) hab).2.1.mp (length_ac γ hab hAC)
  have hi := speed_integrable γ hab hAC
  have him : IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hi
  have hiL : IntervalIntegrable (deriv (realLengthFunction γ a)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hL.2.1
  have hle : (∫ t in a..b, ‖deriv γ t‖) ≤ ∫ t in a..b, deriv (realLengthFunction γ a) t := by
    apply intervalIntegral.integral_mono_ae_restrict hab.le him hiL
    have haes : ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Ioo a b := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    have hγd : ∀ᵐ t ∂volume.restrict (Icc a b),
        t ∈ Ioo a b → HasDerivAt γ (deriv γ t) t :=
      (ae_restrict_of_ae hγ.2.1).mono (fun t ht hti => (ht hti).1)
    have hLd := ae_restrict_of_ae (s := Icc a b) hL.1
    filter_upwards [haes, hγd, hLd] with t ht hgt hlt
    exact speed_le_length_derivative γ hR ht (hgt ht) (hlt ht)
  have hLb := hL.2.2 b ⟨hab.le, le_rfl⟩
  have hLa : realLengthFunction γ a a = 0 := by
    simp [realLengthFunction, curveLength_self]
  rw [hLa, zero_add] at hLb
  rw [← hLb] at hle
  apply le_antisymm (length_le_integral_speed γ hab hAC)
  calc
    ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) ≤ ENNReal.ofReal (realLengthFunction γ a b) :=
      ENNReal.ofReal_le_ofReal hle
    _ = curveLength γ a b := ENNReal.ofReal_toReal hR.ne

lemma coordinatesAC_mono (hAC : CoordinatesAC γ a b) {x y : ℝ}
    (hax : a ≤ x) (hyb : y ≤ b) : CoordinatesAC γ x y := by
  intro i ε hε
  obtain ⟨δ, hδ, hh⟩ := hAC i ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n u v huv hends hdis hlen
  exact hh n u v huv (fun j => ⟨Icc_subset_Icc hax hyb (hends j).1,
    Icc_subset_Icc hax hyb (hends j).2⟩) hdis hlen

theorem length_formula (hab : a < b) (hAC : CoordinatesAC γ a b) :
    Rectifiable γ a b ∧ IntegrableOn (fun t => ‖deriv γ t‖) (Icc a b) ∧
    curveLength γ a b = ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) ∧
    ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b →
      curveLength γ x y = ENNReal.ofReal (∫ t in x..y, ‖deriv γ t‖) ∧
      realLengthFunction γ a y - realLengthFunction γ a x = ∫ t in x..y, ‖deriv γ t‖ := by
  have hR := ac_rectifiable γ hab.le hAC
  refine ⟨hR, speed_integrable γ hab hAC, length_eq_integral_speed γ hab hAC, ?_⟩
  intro x y hax hxy hyb
  have hlen : curveLength γ x y = ENNReal.ofReal (∫ t in x..y, ‖deriv γ t‖) := by
    rcases hxy.eq_or_lt with h | h
    · subst y; simp [curveLength_self]
    · exact length_eq_integral_speed γ h (coordinatesAC_mono γ hAC hax hyb)
  refine ⟨hlen, ?_⟩
  rw [lengthFunction_subinterval γ hR hax hxy hyb, hlen, ENNReal.toReal_ofReal]
  exact intervalIntegral.integral_nonneg hxy (fun _ _ => norm_nonneg _)

theorem length_function_formula (hab : a < b) (hAC : CoordinatesAC γ a b)
    (t : ℝ) (ht : t ∈ Icc a b) :
    realLengthFunction γ a t = ∫ s in a..t, ‖deriv γ s‖ := by
  have h := (length_formula γ hab hAC).2.2.2 a t le_rfl ht.1 ht.2
  simpa [realLengthFunction, curveLength_self] using h.2

lemma ac_continuous (hab : a ≤ b) (hAC : CoordinatesAC γ a b) :
    ContinuousOn γ (Icc a b) := by
  have hp : ContinuousOn (fun t i => γ t i) (Icc a b) :=
    continuousOn_pi.mpr (fun i => (AcBasic.uniformContinuousOn hab (hAC i)).continuousOn)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous.comp_continuousOn hp

lemma extendedLength_continuous (hab : a ≤ b) (hc : ContinuousOn γ (Icc a b))
    (hR : Rectifiable γ a b) : Continuous (extendedLength γ a b) :=
  (realLengthFunction_continuous γ hab hc hR).comp_continuous
    (NormalizedStieltjes.clamp_continuous a b) (NormalizedStieltjes.clamp_mem hab)

lemma extendedLength_monotone (hab : a ≤ b) (hR : Rectifiable γ a b) :
    Monotone (extendedLength γ a b) := by
  intro x y hxy
  exact realLengthFunction_monotone γ hR (NormalizedStieltjes.clamp_mem hab x)
    (NormalizedStieltjes.clamp_mem hab y) (NormalizedStieltjes.clamp_mono a b hxy)

theorem stieltjes_generator (hab : a < b) (hc : ContinuousOn γ (Icc a b))
    (hR : Rectifiable γ a b) :
    PositiveStieltjes.PositiveGenerator (extendedLength γ a b) := by
  refine ⟨extendedLength_monotone γ hab.le hR,
    fun x => (extendedLength_continuous γ hab.le hc hR).continuousAt.continuousWithinAt,
    ?_, realLengthFunction γ a b, ?_⟩
  · apply Tendsto.congr' (f₁ := fun _ : ℝ => (0 : ℝ)) _ tendsto_const_nhds
    filter_upwards [eventually_le_atBot a] with x hx
    dsimp [extendedLength, Specs.D11.Ch12.RectifiableCurveBridge.extendedLength_value]
    rw [max_eq_left ((min_le_right b x).trans hx)]
    change 0 = (curveLength γ a a).toReal
    simp [curveLength_self]
  · intro x
    change |realLengthFunction γ a (max a (min b x))| ≤ realLengthFunction γ a b
    rw [abs_of_nonneg (lengthFunction_nonnegative γ a _).2]
    exact realLengthFunction_monotone γ hR (NormalizedStieltjes.clamp_mem hab.le x)
      ⟨hab.le, le_rfl⟩ (NormalizedStieltjes.clamp_mem hab.le x).2

lemma arcLengthMeasure_eq_stieltjes (hab : a < b) (hc : ContinuousOn γ (Icc a b))
    (hR : Rectifiable γ a b) :
    arcLengthMeasure γ a b = PositiveStieltjes.stieltjesMeasure
      (extendedLength γ a b) (stieltjes_generator γ hab hc hR) := by
  classical
  change (if h : PositiveStieltjes.PositiveGenerator (extendedLength γ a b) then
    PositiveStieltjes.stieltjesMeasure (extendedLength γ a b) h else 0) = _
  exact dite_eq_left (stieltjes_generator γ hab hc hR)

/-- Equality of finite measures is tested on all initial intervals. The
constant tails of the true length function account for both endpoints. -/
theorem stieltjes_density (hab : a < b) (hAC : CoordinatesAC γ a b) :
    arcLengthMeasure γ a b =
      (volume.restrict (Icc a b)).withDensity (fun t => ENNReal.ofReal ‖deriv γ t‖) := by
  let μ := volume.restrict (Icc a b)
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ‖deriv γ t‖
  have hi := speed_integrable γ hab hAC
  have hw : (∫⁻ t, w t ∂μ) ≠ ⊤ := by
    rw [show (∫⁻ t, w t ∂μ) = ENNReal.ofReal (∫ t, ‖deriv γ t‖ ∂μ) from
      (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => norm_nonneg _))).symm]
    exact ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (μ.withDensity w) := isFiniteMeasure_withDensity hw
  have hR := ac_rectifiable γ hab.le hAC
  have hc := ac_continuous γ hab.le hAC
  let hG := stieltjes_generator γ hab hc hR
  rw [arcLengthMeasure_eq_stieltjes γ hab hc hR]
  letI := PositiveStieltjes.stieltjesMeasure_finite (extendedLength γ a b) hG
  apply Measure.ext_of_Iic
  intro x
  rw [PositiveStieltjes.stieltjesMeasure_Iic]
  change ENNReal.ofReal (extendedLength γ a b x) = μ.withDensity w (Iic x)
  rw [withDensity_apply _ measurableSet_Iic]
  have hrestrict : μ.restrict (Iic x) = volume.restrict (Iic x ∩ Icc a b) :=
    Measure.restrict_restrict measurableSet_Iic
  rw [hrestrict, ← ofReal_integral_eq_lintegral_ofReal
    (hi.mono_set inter_subset_right) (Eventually.of_forall (fun _ => norm_nonneg _))]
  congr 1
  by_cases hx : x < a
  · have he : Iic x ∩ Icc a b = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hx.not_ge (ht.2.1.trans ht.1)
    rw [he, setIntegral_empty]
    dsimp [extendedLength, Specs.D11.Ch12.RectifiableCurveBridge.extendedLength_value]
    rw [max_eq_left ((min_le_right b x).trans hx.le)]
    change (curveLength γ a a).toReal = 0
    simp [curveLength_self]
  · have hax : a ≤ x := le_of_not_gt hx
    have hmin : min b x ∈ Icc a b := ⟨le_min hab.le hax, min_le_left _ _⟩
    have he : Iic x ∩ Icc a b = Icc a (min b x) := by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]; tauto
    rw [he, ← restrict_Ioc_eq_restrict_Icc,
      ← intervalIntegral.integral_of_le hmin.1]
    dsimp [extendedLength, Specs.D11.Ch12.RectifiableCurveBridge.extendedLength_value]
    rw [max_eq_right hmin.1]
    exact length_function_formula γ hab hAC _ hmin

/-- Bounded continuous functions on the compact image are integrable for the
parametrized Stieltjes measure, and density change gives the speed formula.
Neither the definition nor the proof identifies repeated traversals. -/
theorem arc_integral_formula {K : Type} [RCLike K] (hab : a < b)
    (hAC : CoordinatesAC γ a b) (h : EuclideanSpace ℝ (Fin d) → K)
    (hh : ContinuousOn h (γ '' Icc a b)) :
    IntegrableOn (fun t => h (γ t)) (Ioc a b) (arcLengthMeasure γ a b) ∧
    IntervalIntegrable (fun t => ‖deriv γ t‖ • h (γ t)) volume a b ∧
    arcLengthIntegral γ a b h = ∫ t in a..b, ‖deriv γ t‖ • h (γ t) := by
  have hc : ContinuousOn (fun t => h (γ t)) (Icc a b) :=
    hh.comp (ac_continuous γ hab.le hAC) (fun t ht => mem_image_of_mem γ ht)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hi : IntegrableOn (fun t => ‖deriv γ t‖ • h (γ t)) (Icc a b) := by
    exact (speed_integrable γ hab hAC).smul_bdd C
      (hc.aestronglyMeasurable measurableSet_Icc)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hC))
  have hw : Measurable (fun t => ENNReal.ofReal ‖deriv γ t‖) :=
    (measurable_deriv γ).norm.ennreal_ofReal
  have htop (μ : Measure ℝ) : ∀ᵐ t ∂μ, ENNReal.ofReal ‖deriv γ t‖ < ⊤ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hν : Integrable (fun t => h (γ t)) (arcLengthMeasure γ a b) := by
    rw [stieltjes_density γ hab hAC]
    apply (integrable_withDensity_iff_integrable_smul' hw (htop _)).mpr
    simpa only [IntegrableOn, ENNReal.toReal_ofReal (norm_nonneg _)] using hi
  refine ⟨hν.integrableOn, (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hi, ?_⟩
  change (∫ t in Ioc a b, h (γ t) ∂arcLengthMeasure γ a b) = _
  rw [stieltjes_density γ hab hAC,
    setIntegral_withDensity_eq_setIntegral_toReal_smul hw (htop _) _ measurableSet_Ioc]
  simp_rw [ENNReal.toReal_ofReal (norm_nonneg _)]
  rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Icc_self,
    intervalIntegral.integral_of_le hab.le]

end D11.Ch12.RectifiableCurveBridge
