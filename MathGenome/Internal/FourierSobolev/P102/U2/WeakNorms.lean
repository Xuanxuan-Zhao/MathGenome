import MathGenome.Internal.FourierSobolev.Specs.P102.U2.WeakNorms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.WeakLpBanach

open MeasureTheory Set
open scoped ENNReal

namespace P102.U2

noncomputable def distributionFunction : WeakNormsSpec.DistributionType := @distribution
noncomputable def weakNorm : WeakNormsSpec.WeakSizeType := @weakSize
noncomputable def weakNormInfinity : WeakNormsSpec.WeakSizeInfinityType := @weakSizeInfinity

/-- Layer cake on an arbitrary measure space, without a finiteness assumption. -/
theorem layerCake : WeakNormsSpec.LayerCake := by
  intro α F _ _ μ h hh q hq
  have hc := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ (fun x => norm_nonneg (h x))) hh hq
  rw [hc, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [ENNReal.ofReal_mul hq.le]
  unfold distribution
  ac_rfl

/-- Raising the modulus to δ changes a weak-L1 bound into a weak-L(1/δ) bound.
This lemma is universe-polymorphic and needs no measurability. -/
lemma weakSize_norm_rpow_le {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    (μ : Measure α) (h : α → F) (δ : ℝ) (hδ : 0 < δ) :
    ExpandedFA.PartIV.weakLpQ μ (1 / δ) (fun x => ‖h x‖ ^ δ) ≤ weakSize μ 1 h ^ δ := by
  refine iSup_le fun t => iSup_le fun ht => ?_
  let s : ℝ := t ^ (1 / δ)
  have hs : 0 < s := Real.rpow_pos_of_pos ht _
  have hst : s ^ δ = t := by
    dsimp [s]
    rw [one_div, Real.rpow_inv_rpow ht.le hδ.ne']
  have hd : ExpandedFA.PartIV.DistributionFunctionsSpec.DistributionValue μ
      (fun x => ‖h x‖ ^ δ) t = distribution μ h s := by
    apply congrArg μ
    ext x
    simp only [mem_ofPred_eq, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← hst]
    exact Real.rpow_lt_rpow_iff hs.le (norm_nonneg _) hδ
  change ENNReal.ofReal t *
    ExpandedFA.PartIV.DistributionFunctionsSpec.DistributionValue μ
      (fun x => ‖h x‖ ^ δ) t ^ (1 / (1 / δ)) ≤ _
  rw [hd]
  calc
    _ = (ENNReal.ofReal s * distribution μ h s) ^ δ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hδ.le,
        ENNReal.ofReal_rpow_of_nonneg hs.le hδ.le, hst]
      simp
    _ ≤ _ := ENNReal.rpow_le_rpow
      (by simpa [weakSize] using
        (le_iSup_of_le s (le_iSup_of_le hs le_rfl) :
          ENNReal.ofReal s * distribution μ h s ^ (1 / (1 : ℝ)) ≤ weakSize μ 1 h)) hδ.le

lemma weakSize_mono_measure {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ ν : Measure α} (hμν : μ ≤ ν) (q : ℝ) (hq : 0 < q) (h : α → F) :
    weakSize μ q h ≤ weakSize ν q h := by
  apply iSup_mono
  intro t
  apply iSup_mono
  intro ht
  apply mul_le_mul' le_rfl
  exact ENNReal.rpow_le_rpow (hμν _) (by positivity)

/-- The unnormalized δ-moment estimate. -/
lemma localMoment_le {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    (μ : Measure α) (h : α → F) (hh : AEMeasurable (fun x => ‖h x‖) μ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (E : Set α) (hEfin : μ E < ∞) :
    (∫⁻ x in E, ENNReal.ofReal (‖h x‖ ^ δ) ∂μ) ≤
      (μ E) ^ (1 - δ) * (ENNReal.ofReal (1 / (1 - δ)) * weakSize μ 1 h ^ δ) := by
  have : IsFiniteMeasure (μ.restrict E) := isFiniteMeasure_restrict.mpr hEfin.ne
  let g : α → ℝ := fun x => ‖h x‖ ^ δ
  have hg : AEStronglyMeasurable g (μ.restrict E) :=
    (hh.restrict.pow_const δ).aestronglyMeasurable
  have hp : 1 < 1 / δ := (one_lt_div hδ).mpr hδ1
  have hm := ExpandedFA.PartIV.lintegral_enorm_le_weakLpN (μ.restrict E) (1 / δ) g
  have hn := ExpandedFA.PartIV.weakLpN_le_conj_mul_weakLpQ (μ.restrict E) (1 / δ) hp g hg
  have hQ := (weakSize_norm_rpow_le (μ.restrict E) h δ hδ).trans
    (ENNReal.rpow_le_rpow (weakSize_mono_measure Measure.restrict_le_self 1 zero_lt_one h) hδ.le)
  have hleft : (∫⁻ x, ‖g x‖ₑ ∂μ.restrict E) =
      ∫⁻ x in E, ENNReal.ofReal (‖h x‖ ^ δ) ∂μ := by
    apply lintegral_congr
    intro x
    simp [g, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [hleft, Measure.restrict_apply_univ, one_div_one_div] at hm
  have he : (1 / δ) / (1 / δ - 1) = 1 / (1 - δ) := by field_simp
  rw [he] at hn
  exact hm.trans (mul_le_mul' le_rfl (hn.trans (mul_le_mul' le_rfl hQ)))

/-- Extended-valued algebra for normalizing the moment and taking its δ-root. -/
lemma normalizedMoment_bound (m W : ℝ≥0∞) (hm0 : m ≠ 0) (hmfin : m ≠ ∞)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((m ^ (1 - δ) * (ENNReal.ofReal (1 / (1 - δ)) * W ^ δ)) / m) ^ (1 / δ) =
      ENNReal.ofReal ((1 - δ) ^ (-1 / δ)) * (W / m) := by
  have hroot : 0 ≤ 1 / δ := by positivity
  have hmroot : m ^ (1 / δ) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hm0) hmfin).ne'
  rw [ENNReal.div_rpow_of_nonneg _ _ hroot,
    ENNReal.mul_rpow_of_nonneg _ _ hroot,
    ENNReal.mul_rpow_of_nonneg _ _ hroot,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    show δ * (1 / δ) = 1 by field_simp,
    ENNReal.rpow_one]
  have he : (1 - δ) * (1 / δ) = 1 / δ - 1 := by field_simp
  rw [he, ENNReal.rpow_sub _ _ hm0 hmfin, ENNReal.rpow_one]
  have hc : ENNReal.ofReal (1 / (1 - δ)) ^ (1 / δ) =
      ENNReal.ofReal ((1 - δ) ^ (-1 / δ)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hroot,
      one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    congr 2
    ring
  rw [hc]
  calc
    _ = (ENNReal.ofReal ((1 - δ) ^ (-1 / δ)) * (W / m)) *
        (m ^ (1 / δ) / m ^ (1 / δ)) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = _ := by rw [ENNReal.div_self hmroot (ENNReal.rpow_ne_top_of_nonneg hroot hmfin), mul_one]

/-- The local weak-L1 estimate, also valid when the weak size is zero or infinite. -/
theorem weakL1_localEstimate : WeakNormsSpec.LocalEstimate := by
  intro α F _ _ μ h hh δ hδ hδ1 E hE hE0 hEfin
  exact (ENNReal.rpow_le_rpow
    (ENNReal.div_le_div_right (localMoment_le μ h hh δ hδ hδ1 E hEfin) (μ E))
    (by positivity)).trans_eq (normalizedMoment_bound (μ E) (weakSize μ 1 h)
      hE0.ne' hEfin.ne δ hδ hδ1)

end P102.U2
