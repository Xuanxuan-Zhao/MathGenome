import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcPrimitive
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch12.BvDefinition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace D11.Ch12.AcPrimitive

/-- The pointwise indefinite integral, with its prescribed additive constant. -/
def primitive {𝕂 : Type*} [RCLike 𝕂] (f : ℝ → 𝕂) (c : 𝕂) (a x : ℝ) : 𝕂 :=
  c + ∫ t in a..x, f t

variable {𝕂 : Type*} [RCLike 𝕂] {a b : ℝ} {f : ℝ → 𝕂}

lemma intervalIntegrable_of_integrableOn (hab : a ≤ b) (hf : IntegrableOn f (Icc a b)) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hf

lemma primitive_increment (hf : IntervalIntegrable f volume a b) (c : 𝕂)
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
    primitive f c a v - primitive f c a u = ∫ t in u..v, f t := by
  dsimp [primitive]
  rw [add_sub_add_left_eq_sub]
  apply intervalIntegral.integral_interval_sub_left
  · exact hf.mono_set (by rw [uIcc_of_le hv.1, uIcc_of_le (hu.1.trans hu.2)]; exact Icc_subset_Icc le_rfl hv.2)
  · exact hf.mono_set (by rw [uIcc_of_le hu.1, uIcc_of_le (hu.1.trans hu.2)]; exact Icc_subset_Icc le_rfl hu.2)

theorem primitive_formula : Specs.D11.Ch12.AcPrimitive.primitive_formula := by
  intro 𝕂 _ a b f c hab hf x hx
  refine ⟨(intervalIntegrable_of_integrableOn hab.le hf).mono_set ?_, rfl⟩
  exact uIcc_subset_uIcc_left (by simpa only [uIcc_of_le hab.le] using hx)

theorem primitive_derivative : Specs.D11.Ch12.AcPrimitive.primitive_derivative := by
  intro 𝕂 _ a b f c hab hf
  have h := (intervalIntegrable_of_integrableOn hab.le hf).ae_hasDerivAt_integral
  filter_upwards [h] with x hx hxi
  exact (hx (by simpa [uIcc_of_le hab.le] using Ioo_subset_Icc_self hxi) a
    (by simp [hab.le])).const_add c

theorem primitive_representative_independent :
    Specs.D11.Ch12.AcPrimitive.primitive_representative_independent := by
  intro 𝕂 _ a b f g c hab hf hg heq x hx
  dsimp [Specs.D11.Ch12.AcPrimitive.primitive_value]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have h := ae_restrict_iff' measurableSet_Icc |>.mp heq
  filter_upwards [h] with t ht htx
  apply ht
  rw [uIoc_of_le hx.1] at htx
  exact ⟨htx.1.le, htx.2.trans hx.2⟩

/-- Absolute continuity follows directly from small-set control of the
absolute integral. No regularity of the density beyond L1 is needed. -/
theorem primitive_ac : Specs.D11.Ch12.AcPrimitive.primitive_ac := by
  intro 𝕂 _ a b f c hab hf
  have hfi := intervalIntegrable_of_integrableOn hab.le hf
  -- Choose the small-set bound separately for each desired error.
  intro ε hε
  obtain ⟨η, hη, hsmall⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    hf.hasFiniteIntegral.ne (ENNReal.ofReal_pos.mpr hε).ne'
  obtain ⟨δ, _, hδ, hδη⟩ := ENNReal.lt_iff_exists_real_btwn.mp hη
  refine ⟨δ, ENNReal.ofReal_pos.mp hδ, ?_⟩
  intro n u v huv hends hdis hlength
  let E : Fin n → Set ℝ := fun j => Ioc (u j) (v j)
  have hEsub (j : Fin n) : E j ⊆ Icc a b :=
    fun _ ht => ⟨(hends j).1.1.trans ht.1.le, ht.2.trans (hends j).2.2⟩
  have hEd : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    simpa only [E, Ioc_disjoint_Ioc, Ioo_disjoint_Ioo] using hdis hij
  have hmass : (volume.restrict (Icc a b)) (⋃ j, E j) < η := by
    calc
      _ ≤ volume (⋃ j, E j) := Measure.restrict_le_self _
      _ ≤ ∑ j, volume (E j) := measure_iUnion_fintype_le volume E
      _ = ENNReal.ofReal (∑ j, (v j - u j)) := by
        simp only [E, Real.volume_Ioc]
        exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => sub_nonneg.mpr (huv j).le)).symm
      _ < η := (ENNReal.ofReal_lt_ofReal_iff (ENNReal.ofReal_pos.mp hδ)).mpr hlength |>.trans hδη
  have hsum : ENNReal.ofReal (∑ j, ‖primitive f c a (v j) - primitive f c a (u j)‖) ≤
      ∫⁻ t in ⋃ j, E j, ‖f t‖ₑ ∂(volume.restrict (Icc a b)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => norm_nonneg _),
      lintegral_iUnion (fun _ => measurableSet_Ioc) hEd, tsum_fintype]
    apply Finset.sum_le_sum
    intro j hj
    rw [ofReal_norm, primitive_increment hfi c (hends j).1 (hends j).2,
      intervalIntegral.integral_of_le (huv j).le]
    have hr : (volume.restrict (Icc a b)).restrict (E j) = volume.restrict (E j) :=
      Measure.restrict_restrict_of_subset (hEsub j)
    change _ ≤ ∫⁻ t, ‖f t‖ₑ ∂((volume.restrict (Icc a b)).restrict (E j))
    rw [hr]
    exact enorm_integral_le_lintegral_enorm _
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp (hsum.trans_lt (hsmall _ hmass))

lemma partition_point_mem {a b : ℝ} (p : D11.Ch12.IntervalPartition a b)
    {i : ℕ} (hi : i ≤ p.length) : p.point i ∈ Icc a b := by
  constructor
  · simpa only [p.start] using p.strictMono.monotoneOn (by simp) (by simpa) (Nat.zero_le i)
  · simpa only [p.finish] using p.strictMono.monotoneOn (by simpa) (by simp) hi

/-- The elementary upper variation bound, retaining the exact scalar norm. -/
lemma variation_primitive_le (hab : a ≤ b) (hf : IntegrableOn f (Icc a b)) (c : 𝕂) :
    D11.Ch12.variation (primitive f c a) a b ≤ ENNReal.ofReal (∫ t in a..b, ‖f t‖) := by
  have hfi := intervalIntegrable_of_integrableOn hab hf
  apply iSup_le
  intro p
  have hpiece (i : ℕ) (hi : i < p.length) :
      IntervalIntegrable (fun t => ‖f t‖) volume (p.point i) (p.point (i + 1)) := by
    apply hfi.norm.mono_set
    apply uIcc_subset_uIcc <;>
      simpa only [uIcc_of_le hab] using partition_point_mem p (by omega)
  have hbound : (∑ i ∈ Finset.range p.length,
      ‖primitive f c a (p.point (i + 1)) - primitive f c a (p.point i)‖) ≤
      ∫ t in a..b, ‖f t‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.range p.length, ∫ t in p.point i..p.point (i + 1), ‖f t‖ := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i < p.length := Finset.mem_range.mp hi
        rw [primitive_increment hfi c (partition_point_mem p (by omega))
          (partition_point_mem p (by omega))]
        exact intervalIntegral.norm_integral_le_integral_norm
          (p.strictMono.monotoneOn (by simp; omega) (by simp; omega) (by omega))
      _ = ∫ t in a..b, ‖f t‖ := by
        simpa only [p.start, p.finish] using intervalIntegral.sum_integral_adjacent_intervals hpiece
  simpa only [D11.Ch12.partitionSum, ← ofReal_norm,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)] using ENNReal.ofReal_le_ofReal hbound

/-- The totalized derivative gives a measurable zero extension on the
actual exceptional set, which is Borel and null. -/
theorem primitive_measurable_derivative :
    Specs.D11.Ch12.AcPrimitive.primitive_measurable_derivative := by
  intro 𝕂 _ _ _ a b f c hab hf
  let F := Specs.D11.Ch12.AcPrimitive.primitive_value f c a
  have hd := primitive_derivative f c hab hf
  let N := {x ∈ Ioo a b | ¬ DifferentiableAt ℝ F x}
  have hN : MeasurableSet N :=
    measurableSet_Ioo.inter (measurableSet_of_differentiableAt ℝ F).compl
  have hN0 : volume N = 0 := by
    have h : ∀ᵐ x, x ∈ Ioo a b → DifferentiableAt ℝ F x :=
      hd.mono (fun x hx hi => (hx hi).differentiableAt)
    simpa only [ae_iff, not_imp, N] using h
  have heq : deriv F =ᵐ[volume.restrict (Icc a b)] f := by
    rw [Filter.EventuallyEq, ← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hd] with x hx hi
    exact (hx hi).deriv
  refine ⟨N, hN, hN0, fun x hx => hx.1, measurable_deriv F,
    fun x hx => deriv_zero_of_not_differentiableAt hx.2, ?_, heq, hf.congr heq.symm⟩
  intro x hx
  exact (show DifferentiableAt ℝ F x from by
    by_contra h
    exact hx.2 ⟨hx.1, h⟩).hasDerivAt

/-- The norm of a vector derivative is controlled by the derivative of
its cumulative real variation. The proof uses right slopes, so it applies
unchanged to complex-valued curves. -/
lemma norm_derivative_le_variation_derivative {F : ℝ → 𝕂} (hBV : BoundedVariationOn F (Icc a b))
    (hab : a ≤ b) {x : ℝ} (hx : x ∈ Ioo a b) {w : 𝕂}
    (hF : HasDerivAt F w x)
    (hV : DifferentiableAt ℝ (variationOnFromTo F (Icc a b) a) x) :
    ‖w‖ ≤ deriv (variationOnFromTo F (Icc a b) a) x := by
  let V := variationOnFromTo F (Icc a b) a
  have hcomp : ∀ᶠ y in 𝓝[>] x, ‖slope F x y‖ ≤ slope V x y := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hx.2)] with y hxy hyb
    have hxs : x ∈ Icc a b := Ioo_subset_Icc_self hx
    have hys : y ∈ Icc a b := ⟨hx.1.le.trans hxy.le, hyb.le⟩
    have hincr : ‖F y - F x‖ ≤ V y - V x := by
      rw [show V y - V x = (eVariationOn F (Icc a b ∩ Icc x y)).toReal by
        dsimp only [V]
        rw [variationOnFromTo.sub_right hBV.locallyBoundedVariationOn
          (show a ∈ Icc a b from ⟨le_rfl, hab⟩) hys hxs,
          variationOnFromTo.eq_of_le F (Icc a b) hxy.le]]
      simpa only [dist_eq_norm] using
        (hBV.mono inter_subset_left).dist_le
          (show y ∈ Icc a b ∩ Icc x y from ⟨hys, hxy.le, le_rfl⟩)
          (show x ∈ Icc a b ∩ Icc x y from ⟨hxs, le_rfl, hxy.le⟩)
    simpa only [slope_def_module, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (y - x)⁻¹ from inv_nonneg.mpr (sub_nonneg.mpr hxy.le)), smul_eq_mul] using
      mul_le_mul_of_nonneg_left hincr (inv_nonneg.mpr (sub_nonneg.mpr hxy.le))
  exact le_of_tendsto_of_tendsto
    (hF.tendsto_slope.norm.mono_left (nhdsGT_le_nhdsNE x))
    (hV.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)) hcomp

/-- The reverse bound uses the real monotone variation function. -/
theorem primitive_variation : Specs.D11.Ch12.AcPrimitive.primitive_variation := by
  intro 𝕂 _ a b f c hab hf
  let F := primitive f c a
  have hu := variation_primitive_le hab.le hf c
  have hBV : BoundedVariationOn F (Icc a b) := by
    rw [← D11.Ch12.bv_iff_boundedVariationOn]
    exact lt_of_le_of_lt hu ENNReal.ofReal_lt_top
  let V := variationOnFromTo F (Icc a b) a
  have hmono : MonotoneOn V (Icc a b) :=
    variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn ⟨le_rfl, hab.le⟩
  have hm : MonotoneOn V (uIcc a b) := by simpa only [uIcc_of_le hab.le] using hmono
  have hdV := hmono.ae_differentiableWithinAt_of_mem
  have hdF := primitive_derivative f c hab hf
  have hnorm : (fun x => ‖f x‖) ≤ᵐ[volume.restrict (Icc a b)] deriv V := by
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hdF, hdV] with x hFx hVx hx
    exact norm_derivative_le_variation_derivative hBV hab.le hx (hFx hx)
      ((hVx (Ioo_subset_Icc_self hx)).differentiableAt (Icc_mem_nhds hx.1 hx.2))
  have hi := intervalIntegral.integral_mono_ae_restrict hab.le
    (intervalIntegrable_of_integrableOn hab.le hf).norm hm.intervalIntegrable_deriv hnorm
  have hupper := hm.intervalIntegral_deriv_mem_uIcc
  rw [uIcc_of_le (sub_nonneg.mpr (hmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le))] at hupper
  have hVends : V b - V a = (D11.Ch12.variation F a b).toReal := by
    simp only [V, variationOnFromTo.self, sub_zero,
      variationOnFromTo.eq_of_le F (Icc a b) hab.le,
      inter_self, ← D11.Ch12.variation_eq_eVariationOn]
  apply le_antisymm hu
  have hfin : D11.Ch12.variation F a b ≠ ∞ :=
    (lt_of_le_of_lt hu ENNReal.ofReal_lt_top).ne
  change ENNReal.ofReal (∫ t in a..b, ‖f t‖) ≤ D11.Ch12.variation F a b
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  exact hi.trans (hVends ▸ hupper.2)

end D11.Ch12.AcPrimitive
