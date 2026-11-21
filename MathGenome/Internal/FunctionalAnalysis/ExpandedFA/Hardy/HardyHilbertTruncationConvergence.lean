import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardyHilbertTruncationConvergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.AtomicHardySpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.HilbertTransform
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace ExpandedFA.Hardy.HardyHilbertTruncationConvergence
open AtomicHardySpaceSpec HardyHilbertTruncationConvergenceSpec
open SingularIntegrals.HilbertTransform
open _root_.Specs.ExpandedFA.SingularIntegrals.HilbertTransform

/-- The cutoff kernel is bounded on its integration domain. -/
lemma truncated_kernel_bound {𝕜 : Type} [RCLike 𝕜] {ε t : ℝ}
    (hε : 0 < ε) (ht : ε < |t|) :
    ‖((Real.pi * t : ℝ) : 𝕜)⁻¹‖ ≤ (Real.pi * ε)⁻¹ := by
  rw [norm_inv, RCLike.norm_ofReal, abs_mul, abs_of_pos Real.pi_pos]
  exact inv_le_inv₀ (mul_pos Real.pi_pos (lt_trans hε ht)) (mul_pos Real.pi_pos hε)
    |>.mpr (mul_le_mul_of_nonneg_left ht.le Real.pi_pos.le)

/-- Absolute existence uses only L¹, and holds at every output point. -/
theorem truncated_l1_existence : TruncatedL1Existence := by
  intro 𝕜 _ ε hε f x
  have hf : Integrable (fun t : ℝ => f (x - t)) :=
    (volume.measurePreserving_sub_left x).integrable_comp_of_integrable
      (MeasureTheory.L1.integrable_coeFn f)
  have hm : AEStronglyMeasurable
      (fun t : ℝ => ((Real.pi * t : ℝ) : 𝕜)⁻¹ * f (x - t)) volume := by
    apply AEStronglyMeasurable.mul _ hf.aestronglyMeasurable
    exact (by fun_prop : Measurable (fun t : ℝ => ((Real.pi * t : ℝ) : 𝕜)⁻¹)).aestronglyMeasurable
  apply (hf.norm.const_mul (Real.pi * ε)⁻¹).integrableOn.mono' hm.restrict
  filter_upwards [ae_restrict_mem (isOpen_lt continuous_const continuous_abs).measurableSet]
    with t ht
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (truncated_kernel_bound hε ht) (norm_nonneg _)

lemma softHilbert_norm_le (ε : ℝ) (f : ComplexL2) :
    ‖softHilbert ε f‖ ≤ ‖f‖ := by
  rw [softHilbert, lineFourier.symm.norm_map, ← lineFourier.norm_map f]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [softFrequencyAction_coe ε (lineFourier f)] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (normalized_dampedSign_norm_le _ (le_max_right _ _) ξ)

/-- The upstream hard/soft difference is L¹ and has zero integral. This gives
an L² bound independent of the cutoff, without an oscillatory multiplier
estimate for the hard truncation. -/
lemma complex_truncated_l2_bound {ε : ℝ} (hε : 0 < ε) (f : ComplexL2) :
    eLpNorm (truncated ε f) 2 volume ≤
      ENNReal.ofReal ((1 + 2 * (∫ t : ℝ, |hardSoftDifference t|)) * ‖f‖) := by
  let D : ℝ := ∫ t : ℝ, |hardSoftDifference t|
  have hD : 0 ≤ D := integral_nonneg (fun _ => abs_nonneg _)
  have hcorr := (hardSoftDifference_pointwise_bound f ε).2
  have hcorr' : eLpNorm
      (fun x : ℝ => ∫ t : ℝ, (hardSoftDifference t : ℂ) * f (x-ε*t)) 2 volume ≤
        ENNReal.ofReal (2 * D * ‖f‖) := by
    simp only [Complex.real_smul] at hcorr
    apply hcorr.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ∫ t : ℝ, |hardSoftDifference t| * (2 * ‖f‖) := by
        apply integral_mono (correction_norm_integrable f ε)
          (hardSoftDifference_integrable.norm.mul_const _)
        intro t
        exact mul_le_mul_of_nonneg_left
          (translation_difference_norm_bound f (ε*t)) (abs_nonneg _)
      _ = 2 * D * ‖f‖ := by rw [integral_mul_const]; dsimp [D]; ring
  have hs : eLpNorm (softHilbert ε f : ℝ → ℂ) 2 volume ≤ ENNReal.ofReal ‖f‖ := by
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (softHilbert_norm_le ε f)
  calc
    _ = eLpNorm
        (fun x : ℝ => (∫ t : ℝ, (hardSoftDifference t : ℂ) * f (x-ε*t)) + softHilbert ε f x)
        2 volume := eLpNorm_congr_ae (truncated_eq_soft_add_correction hε f)
    _ ≤ _ + _ := eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ ENNReal.ofReal (2 * D * ‖f‖) + ENNReal.ofReal ‖f‖ := add_le_add hcorr' hs
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]; congr 1; ring

/-- The same uniform constant applies to the real restriction. -/
theorem uniform_l2_bounds : UniformL2Bounds := by
  let C := 1 + 2 * (∫ t : ℝ, |hardSoftDifference t|)
  refine ⟨C, by dsimp [C]; positivity, fun ε hε f => complex_truncated_l2_bound hε f, ?_⟩
  intro ε hε f
  have he : (fun x : ℝ => ((truncated ε f x : ℝ) : ℂ)) =
      truncated ε (complexify 2 f) := by
    funext x
    exact (truncated_complexify ε f x).symm
  have hn : eLpNorm (fun x : ℝ => ((truncated ε f x : ℝ) : ℂ)) 2 volume =
      eLpNorm (truncated ε f) 2 volume := by
    apply eLpNorm_congr_norm_ae
      (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
        ((real_truncation_convergence.1 ε hε f).2.aestronglyMeasurable))
      ((real_truncation_convergence.1 ε hε f).2.aestronglyMeasurable)
    exact .of_forall fun x => by simp
  rw [← hn, he]
  simpa only [complexify_norm] using complex_truncated_l2_bound hε (complexify 2 f)

/-- Reverse triangle inequality in the form needed for a translated atom. -/
lemma distance_norm_difference (x c y : ℝ) :
    |(|x-y| - |x-c|)| ≤ |y-c| := by
  have h := abs_abs_sub_abs_le_abs_sub (x-y) (x-c)
  calc
    _ ≤ |(x-y) - (x-c)| := h
    _ = |y-c| := by rw [show (x-y) - (x-c) = -(y-c) by ring, abs_neg]

/-- A cutoff change across an atom interval is confined to a shell of width
at most its radius. This is the partial-interval term in the source proof. -/
lemma cutoff_change_in_shell {x c y ε R : ℝ} (hy : |y-c| ≤ R)
    (hcut : (ε < |x-y|) ≠ (ε < |x-c|)) :
    |(|x-c| - ε)| ≤ R := by
  have hd := distance_norm_difference x c y
  by_cases ha : ε < |x-y|
  · have hb : ¬ ε < |x-c| := fun hb => hcut (propext ⟨fun _ => hb, fun _ => ha⟩)
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt hb))]
    have := (abs_le.mp hd).2
    linarith
  · have hb : ε < |x-c| := by
      by_contra hb
      apply hcut
      exact propext ⟨fun h => (ha h).elim, fun h => (hb h).elim⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hb.le)]
    have := (abs_le.mp hd).1
    have ha' := le_of_not_gt ha
    linarith

/-- Once the cutoff is smaller than an atom radius, every point outside the
doubled supporting interval sees the entire atom, so the shell disappears. -/
lemma cutoff_full_outside {x c y ε R : ℝ}
    (hx : 2 * R < |x-c|) (hy : |y-c| ≤ R) (hε : ε ≤ R) :
    ε < |x-y| := by
  have hd := (abs_le.mp (distance_norm_difference x c y)).1
  linarith

/-- A quantitative pointwise bound, with no Hardy assumption. The dependence
on ε is harmless for identifying the limit of an atomic series at fixed ε. -/
lemma truncated_l1_pointwise_bound {𝕜 : Type} [RCLike 𝕜] {ε : ℝ}
    (hε : 0 < ε) (f : LineLp 𝕜 1) (x : ℝ) :
    ‖truncated ε f x‖ ≤ (Real.pi * ε)⁻¹ * ‖f‖ := by
  have hf : Integrable (fun t : ℝ => ‖f (x - t)‖) :=
    (volume.measurePreserving_sub_left x).integrable_comp_of_integrable
      (MeasureTheory.L1.integrable_coeFn f).norm
  calc
    _ ≤ ∫ t in {t : ℝ | ε < |t|}, (Real.pi * ε)⁻¹ * ‖f (x-t)‖ := by
      apply norm_integral_le_of_norm_le (hf.const_mul _).integrableOn
      filter_upwards [ae_restrict_mem (isOpen_lt continuous_const continuous_abs).measurableSet]
        with t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (truncated_kernel_bound hε ht) (norm_nonneg _)
    _ ≤ ∫ t : ℝ, (Real.pi * ε)⁻¹ * ‖f (x-t)‖ :=
      setIntegral_le_integral (hf.const_mul _) (.of_forall fun t => by positivity)
    _ = _ := by
      rw [integral_const_mul, integral_sub_left_eq_self (fun t : ℝ => ‖f t‖) volume x,
        ← MeasureTheory.L1.norm_eq_integral_norm]

/-- Fixed-cutoff evaluation is a bounded scalar-linear functional on L¹.
In particular, it preserves convergence of the original atomic synthesis. -/
def truncatedEvaluation {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    LineLp 𝕜 1 →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    ({ toFun := fun f => truncated ε f x
       map_add' := by
         intro f g
         have he : (fun t : ℝ => ((Real.pi*t : ℝ) : 𝕜)⁻¹ * (f+g) (x-t)) =ᵐ[volume]
             (fun t => ((Real.pi*t : ℝ) : 𝕜)⁻¹ * f (x-t) +
               ((Real.pi*t : ℝ) : 𝕜)⁻¹ * g (x-t)) := by
           filter_upwards [(volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae
             (Lp.coeFn_add f g)] with t ht
           rw [ht]
           exact mul_add _ _ _
         change (∫ t in {t : ℝ | ε < |t|}, _) = _
         rw [setIntegral_congr_ae (isOpen_lt continuous_const continuous_abs).measurableSet
           (he.mono fun _ h _ => h)]
         exact integral_add (truncated_l1_existence 𝕜 ε hε f x)
           (truncated_l1_existence 𝕜 ε hε g x)
       map_smul' := by
         intro k f
         have he : (fun t : ℝ => ((Real.pi*t : ℝ) : 𝕜)⁻¹ * (k • f) (x-t)) =ᵐ[volume]
             (fun t => k • (((Real.pi*t : ℝ) : 𝕜)⁻¹ * f (x-t))) := by
           filter_upwards [(volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae
             (Lp.coeFn_smul k f)] with t ht
           rw [ht]
           simp only [Pi.smul_apply, smul_eq_mul]
           ring
         change (∫ t in {t : ℝ | ε < |t|}, _) = _
         rw [setIntegral_congr_ae (isOpen_lt continuous_const continuous_abs).measurableSet
           (he.mono fun _ h _ => h), integral_smul]
         rfl } : LineLp 𝕜 1 →ₗ[𝕜] 𝕜)
    (Real.pi * ε)⁻¹ (fun f => truncated_l1_pointwise_bound hε f x)

/-- The ordinary kernel difference has the expected quadratic decay, uniformly
on the supporting atom interval, including real and complex scalars. -/
lemma hilbert_kernel_difference_bound {𝕜 : Type} [RCLike 𝕜]
    {x c y R : ℝ} (hR : 0 < R) (hx : 2 * R < |x-c|) (hy : |y-c| ≤ R) :
    ‖((Real.pi * (x-y) : ℝ) : 𝕜)⁻¹ - ((Real.pi * (x-c) : ℝ) : 𝕜)⁻¹‖ ≤
      2 * R / (Real.pi * |x-c| ^ 2) := by
  have hu : 0 < |x-c| := by linarith
  have hv : |x-c| / 2 ≤ |x-y| := by
    have h := (abs_le.mp (distance_norm_difference x c y)).1
    linarith
  have hvp : 0 < |x-y| := lt_of_lt_of_le (by linarith) hv
  have hx0 : x-c ≠ 0 := abs_pos.mp hu
  have hy0 : x-y ≠ 0 := abs_pos.mp hvp
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have heq : (Real.pi*(x-y))⁻¹ - (Real.pi*(x-c))⁻¹ =
      (y-c) / (Real.pi * (x-y) * (x-c)) := by
    field_simp
    ring
  have heq' : ((Real.pi*(x-y) : ℝ) : 𝕜)⁻¹ - ((Real.pi*(x-c) : ℝ) : 𝕜)⁻¹ =
      (((Real.pi*(x-y))⁻¹ - (Real.pi*(x-c))⁻¹ : ℝ) : 𝕜) := by
    simp only [RCLike.ofReal_sub, RCLike.ofReal_inv]
  rw [heq', RCLike.norm_ofReal, heq, abs_div, abs_mul, abs_mul,
    abs_of_pos Real.pi_pos]
  have hden : 0 < Real.pi * |x-y| * |x-c| := by positivity
  have hd : 0 < Real.pi * |x-c| ^ 2 := by positivity
  apply (div_le_div_iff₀ hden hd).mpr
  calc
    |y-c| * (Real.pi * |x-c| ^ 2) ≤ R * (Real.pi * |x-c| ^ 2) :=
      mul_le_mul_of_nonneg_right hy hd.le
    _ ≤ (2 * R) * (Real.pi * |x-y| * |x-c|) := by
      nlinarith [mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * R * Real.pi * |x-c|)]

/-- The hard-cutoff error includes the partial-interval contribution. The
second summand cannot be discarded when the cutoff intersects the atom. -/
lemma cutKernel_difference_bound {𝕜 : Type} [RCLike 𝕜]
    {x c y ε R : ℝ} (hR : 0 < R) (hx : 2 * R < |x-c|) (hy : |y-c| ≤ R) :
    ‖cutKernel 𝕜 ε (x-y) - cutKernel 𝕜 ε (x-c)‖ ≤
      2 * R / (Real.pi * |x-c| ^ 2) +
        (if |(|x-c| - ε)| ≤ R then (Real.pi * |x-c|)⁻¹ else 0) := by
  let D := 2 * R / (Real.pi * |x-c| ^ 2)
  let b : 𝕜 := ((Real.pi * (x-c) : ℝ) : 𝕜)⁻¹
  let a : 𝕜 := ((Real.pi * (x-y) : ℝ) : 𝕜)⁻¹
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb : ‖b‖ = (Real.pi * |x-c|)⁻¹ := by
    simp only [b, norm_inv, RCLike.norm_ofReal, abs_mul, abs_of_pos Real.pi_pos]
  have hd : ‖a-b‖ ≤ D := hilbert_kernel_difference_bound hR hx hy
  have ha : ‖a‖ ≤ D + ‖b‖ := by
    calc
      ‖a‖ = ‖(a-b)+b‖ := by congr 1; ring
      _ ≤ ‖a-b‖ + ‖b‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hd le_rfl
  by_cases hs : |(|x-c| - ε)| ≤ R
  · rw [ite_eq_left hs, ← hb]
    by_cases hya : ε < |x-y| <;> by_cases hca : ε < |x-c|
    · have h : ‖cutKernel 𝕜 ε (x-y) - cutKernel 𝕜 ε (x-c)‖ ≤ D := by
        simpa only [cutKernel, ite_eq_left hya, ite_eq_left hca] using hd
      exact h.trans (le_add_of_nonneg_right (norm_nonneg b))
    · simpa only [cutKernel, ite_eq_left hya, ite_eq_right hca, sub_zero] using ha
    · simpa only [cutKernel, ite_eq_right hya, ite_eq_left hca, zero_sub, norm_neg] using
        (le_add_of_nonneg_left hD : ‖b‖ ≤ D + ‖b‖)
    · simp only [cutKernel, ite_eq_right hya, ite_eq_right hca, sub_self, norm_zero]
      positivity
  · rw [ite_eq_right hs, add_zero]
    have he : (ε < |x-y|) = (ε < |x-c|) := by
      by_contra h
      exact hs (cutoff_change_in_shell hy h)
    by_cases hya : ε < |x-y|
    · have hca : ε < |x-c| := he ▸ hya
      simpa only [cutKernel, ite_eq_left hya, ite_eq_left hca] using hd
    · have hca : ¬ ε < |x-c| := he ▸ hya
      simpa only [cutKernel, ite_eq_right hya, ite_eq_right hca, sub_self, norm_zero] using hD

/-- Even when the two component intervals overlap, the cutoff shell has
length at most four atom radii. This yields a uniform integral bound for the
partial-interval term outside the doubled supporting interval. -/
lemma cutoff_shell_measure {c R ε : ℝ} (hR : 0 < R) :
    volume {x : ℝ | |(|x-c| - ε)| ≤ R} ≤ ENNReal.ofReal (4 * R) := by
  have hsub : {x : ℝ | |(|x-c| - ε)| ≤ R} ⊆
      Icc (c+ε-R) (c+ε+R) ∪ Icc (c-ε-R) (c-ε+R) := by
    intro x hx
    change |(|x-c| - ε)| ≤ R at hx
    have h := abs_le.mp hx
    by_cases hx : 0 ≤ x-c
    · left
      rw [abs_of_nonneg hx] at h
      constructor <;> linarith [h.1, h.2]
    · right
      rw [abs_of_neg (lt_of_not_ge hx)] at h
      constructor <;> linarith [h.1, h.2]
  calc
    _ ≤ volume (Icc (c+ε-R) (c+ε+R) ∪ Icc (c-ε-R) (c-ε+R)) := measure_mono hsub
    _ ≤ volume (Icc (c+ε-R) (c+ε+R)) + volume (Icc (c-ε-R) (c-ε+R)) :=
      measure_union_le _ _
    _ = ENNReal.ofReal (4 * R) := by
      simp only [Real.volume_Icc]
      rw [show c+ε+R-(c+ε-R) = 2*R by ring,
        show c-ε+R-(c-ε-R) = 2*R by ring,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The partial-interval term is integrable with a constant independent of
both atom radius and cutoff. Using the far-field lower bound on |x-c| and
the shell length suffices; no false full-interval cancellation is used. -/
lemma partial_cutoff_integral_bound {c R ε : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : ℝ => (Real.pi * |x-c|)⁻¹)
      {x : ℝ | 2*R < |x-c| ∧ |(|x-c| - ε)| ≤ R} ∧
    (∫ x in {x : ℝ | 2*R < |x-c| ∧ |(|x-c| - ε)| ≤ R},
      (Real.pi * |x-c|)⁻¹) ≤ 2 / Real.pi := by
  let S := {x : ℝ | 2*R < |x-c| ∧ |(|x-c| - ε)| ≤ R}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hm : volume S ≤ ENNReal.ofReal (4*R) :=
    (measure_mono (fun _ hx => hx.2)).trans (cutoff_shell_measure hR)
  have hmt : volume S ≠ ∞ := (hm.trans_lt ENNReal.ofReal_lt_top).ne
  have hreal : volume.real S ≤ 4*R := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*R)] using this
  have hbound (x : ℝ) (hx : x ∈ S) :
      (Real.pi * |x-c|)⁻¹ ≤ (Real.pi * (2*R))⁻¹ := by
    have hx' : 2*R < |x-c| := hx.1
    have hxc : 0 < |x-c| := by linarith
    exact (inv_le_inv₀ (by positivity : 0 < Real.pi * |x-c|)
      (by positivity : 0 < Real.pi * (2*R))).mpr
      (mul_le_mul_of_nonneg_left hx.1.le Real.pi_pos.le)
  have hm' : AEStronglyMeasurable (fun x : ℝ => (Real.pi * |x-c|)⁻¹) volume := by
    exact (by fun_prop : Measurable (fun x : ℝ => (Real.pi * |x-c|)⁻¹)).aestronglyMeasurable
  have hc : IntegrableOn (fun _ : ℝ => (Real.pi * (2*R))⁻¹) S :=
    integrableOn_const hmt
  have hi : IntegrableOn (fun x : ℝ => (Real.pi * |x-c|)⁻¹) S := by
    apply hc.mono' hm'.restrict
    filter_upwards [ae_restrict_mem hS] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact hbound x hx
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ _ in S, (Real.pi * (2*R))⁻¹ := by
      apply integral_mono_ae hi hc
      filter_upwards [ae_restrict_mem hS] with x hx
      exact hbound x hx
    _ = (Real.pi * (2*R))⁻¹ * volume.real S := by simp [mul_comm]
    _ ≤ (Real.pi * (2*R))⁻¹ * (4*R) :=
      mul_le_mul_of_nonneg_left hreal (by positivity)
    _ = 2 / Real.pi := by field_simp; ring

/-- The atom energy estimate on the manuscript's ordinary real line. -/
lemma line_atom_energy {𝕜 : Type} [RCLike 𝕜] (a : LineAtom 𝕜) :
    ∃ c R : ℝ, 0 < R ∧
      (∀ᵐ y, (R < |y-c| → a.val y = 0) ∧ ‖a.val y‖ ≤ (2*R)⁻¹) ∧
      MemLp (a.val : ℝ → 𝕜) 2 volume ∧
      (∫ y : ℝ, ‖a.val y‖ ^ 2) ≤ (2*R)⁻¹ := by
  obtain ⟨c, R, hR, hzero, htop, hb⟩ := a.property.2
  have hvol : volume.real (Metric.ball c R) = 2*R := by
    rw [Real.ball_eq_Ioo, measureReal_def, Real.volume_Ioo,
      show c+R-(c-R) = 2*R by ring, ENNReal.toReal_ofReal (by positivity)]
  have ha := MeasureTheory.L1.integrable_coeFn a.val
  have hp : ∀ᵐ y, ‖a.val y‖ ^ 2 ≤ (2*R)⁻¹ * ‖a.val y‖ := by
    filter_upwards [hb] with y hy
    rw [hvol] at hy
    nlinarith [mul_le_mul_of_nonneg_right hy.2 (norm_nonneg (a.val y))]
  have hi : Integrable (fun y : ℝ => ‖a.val y‖ ^ 2) :=
    (ha.norm.const_mul (2*R)⁻¹).mono' ((Lp.aestronglyMeasurable a.val).norm.pow 2)
      (by simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hp)
  refine ⟨c, R, hR, ?_, (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable a.val)).mpr hi, ?_⟩
  · filter_upwards [hb] with y hy
    refine ⟨fun h => hy.1 ?_, ?_⟩
    · simpa only [Metric.mem_ball, Real.dist_eq, not_lt] using h.le
    · simpa only [hvol] using hy.2
  · calc
      _ ≤ ∫ y : ℝ, (2*R)⁻¹ * ‖a.val y‖ :=
        integral_mono_ae hi (ha.norm.const_mul _) hp
      _ = (2*R)⁻¹ * ‖a.val‖ := by
        rw [integral_const_mul, MeasureTheory.L1.norm_eq_integral_norm]
      _ ≤ _ := mul_le_of_le_one_right (by positivity)
        (AtomicHardySpace.atom_norm_le volume a)

/-- Radial integration in dimension one, without identifying the line with
an unverified Euclidean coordinate model. -/
lemma quadratic_tail_integral {c R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : ℝ => 2*R / (Real.pi * |x-c| ^ 2))
      {x : ℝ | 2*R < |x-c|} ∧
    (∫ x in {x : ℝ | 2*R < |x-c|}, 2*R / (Real.pi * |x-c| ^ 2)) = 2/Real.pi := by
  let w : ℝ → ℝ := fun x => (Ioi (2*R)).indicator (fun r : ℝ => 1/r^2) ‖x‖
  have heq (r : ℝ) (hr : 0 < r) :
      r ^ (Module.finrank ℝ ℝ - 1) *
          (Ioi (2*R)).indicator (fun r : ℝ => 1/r^2) r =
        (Ioi (2*R)).indicator (fun r : ℝ => r ^ (-2 : ℝ)) r := by
    by_cases h : 2*R < r
    · simp [h, Real.rpow_neg hr.le, Real.rpow_two, one_div]
    · simp [h]
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (by positivity : 0 < 2*R)
  have hrad : IntegrableOn (fun r : ℝ => r ^ (Module.finrank ℝ ℝ - 1) *
      (Ioi (2*R)).indicator (fun r : ℝ => 1/r^2) r) (Ioi 0) :=
    (hi.integrable_indicator measurableSet_Ioi).integrableOn.congr_fun
      (fun r hr => (heq r hr).symm) measurableSet_Ioi
  have hwi : Integrable w := by
    rw [integrable_fun_norm_addHaar volume]
    simpa [w, smul_eq_mul] using hrad
  have hwe : (∫ x : ℝ, w x) = 1/R := by
    rw [show w = (fun x : ℝ =>
      (Ioi (2*R)).indicator (fun r : ℝ => 1/r^2) ‖x‖) from rfl,
      integral_fun_norm_addHaar volume]
    simp only [smul_eq_mul, nsmul_eq_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi (by positivity : 0 ≤ 2*R)),
      integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by positivity : 0 < 2*R)]
    norm_num [Real.ball_eq_Ioo, measureReal_def]
    simp only [Real.rpow_neg_one, mul_inv_rev]
    field_simp
  have hS : MeasurableSet {x : ℝ | 2*R < |x-c|} := by measurability
  have he (x : ℝ) :
      {x : ℝ | 2*R < |x-c|}.indicator
          (fun x : ℝ => 2*R/(Real.pi*|x-c|^2)) x = (2*R/Real.pi)*w (x-c) := by
    by_cases hx : 2*R < |x-c|
    · rw [indicator_of_mem (show x ∈ {x : ℝ | 2*R < |x-c|} from hx)]
      dsimp [w]
      rw [indicator_of_mem (show |x-c| ∈ Ioi (2*R) from hx)]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    · simp [w, Real.norm_eq_abs, hx]
  have hfull : Integrable
      ({x : ℝ | 2*R < |x-c|}.indicator (fun x : ℝ => 2*R/(Real.pi*|x-c|^2))) := by
    rw [show ({x : ℝ | 2*R < |x-c|}.indicator
      (fun x : ℝ => 2*R/(Real.pi*|x-c|^2))) =
      (fun x : ℝ => (2*R/Real.pi)*w (x-c)) from funext he]
    exact (hwi.comp_sub_right c).const_mul (2*R/Real.pi)
  refine ⟨(integrable_indicator_iff hS).mp hfull, ?_⟩
  rw [← integral_indicator hS]
  simp_rw [he]
  rw [integral_const_mul, integral_sub_right_eq_self, hwe]
  field_simp

lemma cutKernel_norm_bound {𝕜 : Type} [RCLike 𝕜] {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖cutKernel 𝕜 ε t‖ ≤ (Real.pi * ε)⁻¹ := by
  by_cases ht : ε < |t|
  · simpa only [cutKernel, if_pos ht] using truncated_kernel_bound (𝕜 := 𝕜) hε ht
  · simp only [cutKernel, if_neg ht, norm_zero]
    positivity

/-- Changing variables in the genuine integral gives convolution in the
atom variable; this identity also applies to L¹ representatives. -/
lemma truncated_eq_atom_integral {𝕜 : Type} [RCLike 𝕜]
    (ε : ℝ) (f : ℝ → 𝕜) (x : ℝ) :
    truncated ε f x = ∫ y : ℝ, cutKernel 𝕜 ε (x-y) * f y := by
  have h : truncated ε f x = ∫ t : ℝ, cutKernel 𝕜 ε t * f (x-t) := by
    rw [truncated, ← integral_indicator (isOpen_lt continuous_const continuous_abs).measurableSet]
    apply integral_congr_ae
    exact .of_forall fun t => by by_cases ht : ε < |t| <;> simp [cutKernel, ht]
  rw [h, ← integral_sub_left_eq_self
    (fun t : ℝ => cutKernel 𝕜 ε t * f (x-t)) volume x]
  simp only [sub_sub_cancel]

lemma cutKernel_mul_integrable {𝕜 : Type} [RCLike 𝕜] {ε : ℝ}
    (hε : 0 < ε) (f : LineLp 𝕜 1) (x : ℝ) :
    Integrable (fun y : ℝ => cutKernel 𝕜 ε (x-y) * f y) := by
  apply ((MeasureTheory.L1.integrable_coeFn f).norm.const_mul (Real.pi*ε)⁻¹).mono'
    (((cutKernel_measurable 𝕜 ε).comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f))
  exact .of_forall fun y => by
    change ‖cutKernel 𝕜 ε (x-y) * f y‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (cutKernel_norm_bound hε _) (norm_nonneg _)

/-- Cancellation with the hard kernel is valid even if the cutoff crosses
only part of the supporting interval. -/
lemma truncated_atom_cancellation {𝕜 : Type} [RCLike 𝕜] {ε : ℝ}
    (hε : 0 < ε) (a : LineAtom 𝕜) (c x : ℝ) :
    truncated ε a.val x =
      ∫ y : ℝ, (cutKernel 𝕜 ε (x-y) - cutKernel 𝕜 ε (x-c)) * a.val y := by
  rw [truncated_eq_atom_integral]
  simp_rw [sub_mul]
  rw [integral_sub (cutKernel_mul_integrable hε a.val x)
    ((MeasureTheory.L1.integrable_coeFn a.val).const_mul _), integral_const_mul,
    a.property.1, mul_zero, sub_zero]

/-- Both far-field contributions survive cancellation: the quadratic kernel
term and the shell term from a partial cutoff. -/
lemma truncated_atom_far_bound {𝕜 : Type} [RCLike 𝕜]
    {c R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (a : LineAtom 𝕜)
    (hs : ∀ᵐ y, R < |y-c| → a.val y = 0) {x : ℝ} (hx : 2*R < |x-c|) :
    ‖truncated ε a.val x‖ ≤ 2*R/(Real.pi*|x-c|^2) +
      (if |(|x-c|-ε)| ≤ R then (Real.pi*|x-c|)⁻¹ else 0) := by
  let D := 2*R/(Real.pi*|x-c|^2) +
    (if |(|x-c|-ε)| ≤ R then (Real.pi*|x-c|)⁻¹ else 0)
  have hD : 0 ≤ D := by dsimp [D]; split_ifs <;> positivity
  have hb : ∀ᵐ y, ‖(cutKernel 𝕜 ε (x-y)-cutKernel 𝕜 ε (x-c))*a.val y‖ ≤ D*‖a.val y‖ := by
    filter_upwards [hs] with y hy
    by_cases h : |y-c| ≤ R
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (cutKernel_difference_bound hR hx h) (norm_nonneg _)
    · simp [hy (lt_of_not_ge h)]
  have hi : Integrable (fun y : ℝ =>
      (cutKernel 𝕜 ε (x-y)-cutKernel 𝕜 ε (x-c))*a.val y) := by
    simp_rw [sub_mul]
    exact (cutKernel_mul_integrable hε a.val x).sub
      ((MeasureTheory.L1.integrable_coeFn a.val).const_mul _)
  rw [truncated_atom_cancellation hε a c x]
  calc
    _ ≤ ∫ y : ℝ, D*‖a.val y‖ :=
      norm_integral_le_of_norm_le ((MeasureTheory.L1.integrable_coeFn a.val).norm.const_mul D) hb
    _ = D*‖a.val‖ := by rw [integral_const_mul, MeasureTheory.L1.norm_eq_integral_norm]
    _ ≤ D := mul_le_of_le_one_right hD (AtomicHardySpace.atom_norm_le volume a)

/-- Absolute integrals define a measurable truncation. -/
lemma truncated_aestronglyMeasurable {𝕜 : Type} [RCLike 𝕜]
    (ε : ℝ) (f : LineLp 𝕜 1) : AEStronglyMeasurable (truncated ε f) volume := by
  have he : truncated ε f = MeasureTheory.convolution (cutKernel 𝕜 ε) f
      (ContinuousLinearMap.mul 𝕜 𝕜) volume := by
    funext x
    rw [truncated, ← integral_indicator (isOpen_lt continuous_const continuous_abs).measurableSet]
    apply integral_congr_ae
    exact .of_forall fun t => by
      by_cases ht : ε < |t| <;> simp [MeasureTheory.convolution_def, cutKernel, ht]
  rw [he]
  exact (cutKernel_measurable 𝕜 ε).aestronglyMeasurable.convolution
    (ContinuousLinearMap.mul 𝕜 𝕜) (Lp.aestronglyMeasurable f)

/-- Integrating the two far-field terms gives the uniform bound needed for
hard truncations; the shell term is included in its entirety. -/
lemma truncated_atom_far_integral {𝕜 : Type} [RCLike 𝕜]
    {c R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (a : LineAtom 𝕜)
    (hs : ∀ᵐ y, R < |y-c| → a.val y = 0) :
    IntegrableOn (fun x : ℝ => ‖truncated ε a.val x‖) {x : ℝ | 2*R < |x-c|} ∧
      (∫ x in {x : ℝ | 2*R < |x-c|}, ‖truncated ε a.val x‖) ≤ 4/Real.pi := by
  let F := {x : ℝ | 2*R < |x-c|}
  let S := {x : ℝ | |(|x-c|-ε)| ≤ R}
  have hF : MeasurableSet F := by dsimp [F]; measurability
  have hS : MeasurableSet S := by dsimp [S]; measurability
  obtain ⟨hqi, hq⟩ := quadratic_tail_integral (c := c) hR
  obtain ⟨hsi, hsb⟩ := partial_cutoff_integral_bound (c := c) (ε := ε) hR
  have hSF : S ∩ F = {x : ℝ | 2*R < |x-c| ∧ |(|x-c|-ε)| ≤ R} := by
    ext x
    exact and_comm
  have hsi' : IntegrableOn (S.indicator (fun x : ℝ => (Real.pi*|x-c|)⁻¹)) F := by
    rw [integrableOn_indicator_iff hS.nullMeasurableSet]
    rw [hSF]; exact hsi
  have hsint : (∫ x in F, S.indicator (fun x : ℝ => (Real.pi*|x-c|)⁻¹) x) ≤ 2/Real.pi := by
    rw [integral_indicator hS, Measure.restrict_restrict hS]
    rw [hSF]; exact hsb
  have hb : ∀ᵐ x ∂volume.restrict F, ‖truncated ε a.val x‖ ≤
      2*R/(Real.pi*|x-c|^2) + S.indicator (fun x : ℝ => (Real.pi*|x-c|)⁻¹) x := by
    filter_upwards [ae_restrict_mem hF] with x hx
    simpa only [S, indicator, mem_setOf_eq] using truncated_atom_far_bound hR hε a hs hx
  have hi : IntegrableOn (fun x : ℝ => ‖truncated ε a.val x‖) F :=
    (hqi.add hsi').mono' (truncated_aestronglyMeasurable ε a.val).norm.restrict
      (by simpa only [norm_norm, Pi.add_apply, F] using hb)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x in F, 2*R/(Real.pi*|x-c|^2) +
        S.indicator (fun x : ℝ => (Real.pi*|x-c|)⁻¹) x :=
      integral_mono_ae hi (hqi.fun_add hsi') hb
    _ = (∫ x in F, 2*R/(Real.pi*|x-c|^2)) +
        ∫ x in F, S.indicator (fun x : ℝ => (Real.pi*|x-c|)⁻¹) x := integral_add hqi hsi'
    _ ≤ 2/Real.pi + 2/Real.pi := add_le_add hq.le hsint
    _ = _ := by ring

lemma line_l2_energy {𝕜 : Type} [RCLike 𝕜] (v : LineLp 𝕜 2) :
    ‖v‖ ^ 2 = ∫ x : ℝ, ‖v x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

/-- The L² estimate controls the local part of each atom uniformly in its
radius. The entire conclusion is derived from the original atom conditions. -/
lemma uniform_atom_bounds_of_l2_bound {𝕜 : Type} [RCLike 𝕜]
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ (ε : ℝ), 0 < ε → ∀ f : LineLp 𝕜 2,
      eLpNorm (truncated ε f) 2 volume ≤ ENNReal.ofReal (K*‖f‖)) :
    UniformAtomBounds 𝕜 := by
  refine ⟨K^2+2+4/Real.pi, by positivity, ?_⟩
  intro ε hε a
  obtain ⟨c, R, hR, hs, h2, henergy⟩ := line_atom_energy a
  let V : ℝ := 2*R
  have hV : 0 < V := by dsimp [V]; positivity
  let v : LineLp 𝕜 2 := h2.toLp a.val
  have heq : truncated ε a.val = truncated ε v := by
    funext x
    exact truncated_congr_ae h2.coeFn_toLp.symm ε x
  have hm : MemLp (truncated ε a.val) 2 volume :=
    by rw [memLp_iff, heq]; exact (hbound ε hε v).trans_lt ENNReal.ofReal_lt_top
  let w : LineLp 𝕜 2 := hm.toLp (truncated ε a.val)
  have hw : ‖w‖ ≤ K*‖v‖ := by
    rw [Lp.norm_toLp]
    apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hK (norm_nonneg _)))
    rw [heq]
    exact hbound ε hε v
  have hv : ‖v‖ ^ 2 ≤ V⁻¹ := by
    rw [line_l2_energy]
    exact (integral_congr_ae (h2.coeFn_toLp.mono fun x hx => by
      change ‖v x‖^2 = ‖a.val x‖^2; rw [hx])).le.trans henergy
  have hi2 : Integrable (fun x : ℝ => ‖truncated ε a.val x‖^2) :=
    hm.integrable_norm_pow (by norm_num)
  have hw2 : (∫ x : ℝ, ‖truncated ε a.val x‖^2) ≤ K^2*V⁻¹ := by
    calc
      _ = ‖w‖^2 := by
        rw [line_l2_energy]
        exact integral_congr_ae (hm.coeFn_toLp.mono fun x hx => by rw [hx]) |>.symm
      _ ≤ (K*‖v‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
      _ = K^2*‖v‖^2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hv (sq_nonneg _)
  let B := {x : ℝ | |x-c| ≤ 2*R}
  have hB : MeasurableSet B := by dsimp [B]; measurability
  have hball : B = Metric.closedBall c (2*R) := by
    ext x
    simp only [B, mem_setOf_eq, Metric.mem_closedBall, Real.dist_eq]
  have hvol : volume.real B = 2*V := by
    rw [hball, Real.closedBall_eq_Icc, measureReal_def, Real.volume_Icc]
    rw [show c+2*R-(c-2*R) = 2*V by dsimp [V]; ring,
      ENNReal.toReal_ofReal (by positivity)]
  have hc : IntegrableOn (fun _ : ℝ => V⁻¹) B := by
    rw [hball]
    exact integrableOn_const measure_closedBall_lt_top.ne
  have hp (x : ℝ) : ‖truncated ε a.val x‖ ≤ V*‖truncated ε a.val x‖^2+V⁻¹ := by
    have hsq := sq_nonneg (V*‖truncated ε a.val x‖-1)
    have hI : V*V⁻¹ = 1 := mul_inv_cancel₀ hV.ne'
    nlinarith [norm_nonneg (truncated ε a.val x)]
  have hi : IntegrableOn (fun x : ℝ => ‖truncated ε a.val x‖) B :=
    ((hi2.const_mul V).integrableOn.add hc).mono'
      (truncated_aestronglyMeasurable ε a.val).norm.restrict
      (.of_forall fun x => by simpa only [norm_norm, Pi.add_apply] using hp x)
  have hlocal : (∫ x in B, ‖truncated ε a.val x‖) ≤ K^2+2 := by
    calc
      _ ≤ ∫ x in B, V*‖truncated ε a.val x‖^2+V⁻¹ :=
        integral_mono_ae hi ((hi2.const_mul V).integrableOn.fun_add hc) (.of_forall hp)
      _ = V*(∫ x in B, ‖truncated ε a.val x‖^2)+V⁻¹*volume.real B := by
        rw [integral_add (hi2.const_mul V).integrableOn hc, integral_const_mul,
          integral_const]; simp [smul_eq_mul, mul_comm]
      _ ≤ V*(∫ x : ℝ, ‖truncated ε a.val x‖^2)+V⁻¹*volume.real B := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hi2 (.of_forall fun x => sq_nonneg _)) hV.le) le_rfl
      _ ≤ V*(K^2*V⁻¹)+V⁻¹*(2*V) := by rw [hvol]; gcongr
      _ = _ := by field_simp
  obtain ⟨hout, hfar⟩ := truncated_atom_far_integral hR hε a (hs.mono fun _ hx => hx.1)
  have hcompl : Bᶜ = {x : ℝ | 2*R < |x-c|} := by ext x; simp [B]
  rw [← hcompl] at hout hfar
  have hfull : Integrable (fun x : ℝ => ‖truncated ε a.val x‖) := by
    simpa only [union_compl_self, integrableOn_univ] using hi.union hout
  refine ⟨(integrable_norm_iff (truncated_aestronglyMeasurable ε a.val)).mp hfull, ?_⟩
  rw [← integral_add_compl hB hfull]
  exact add_le_add hlocal hfar

/-- Uniform atom bounds for the two original scalar fields. -/
theorem uniform_atom_bounds : UniformAtomBounds ℂ ∧ UniformAtomBounds ℝ := by
  obtain ⟨K, hK, hcomplex, hreal⟩ := uniform_l2_bounds
  exact ⟨uniform_atom_bounds_of_l2_bound hK hcomplex,
    uniform_atom_bounds_of_l2_bound hK hreal⟩

/-- For cutoffs below the atom radius, the entire supporting interval remains
inside the far-field integral, so the far-field truncation is independent of
its cutoff. -/
lemma truncated_atom_far_stable {𝕜 : Type} [RCLike 𝕜]
    {c R ε δ : ℝ} (a : LineAtom 𝕜)
    (hs : ∀ᵐ y, R < |y-c| → a.val y = 0)
    (hε : ε ≤ R) (hδ : δ ≤ R) {x : ℝ} (hx : 2*R < |x-c|) :
    truncated ε a.val x = truncated δ a.val x := by
  rw [truncated_eq_atom_integral, truncated_eq_atom_integral]
  apply integral_congr_ae
  filter_upwards [hs] with y hy
  by_cases h : |y-c| ≤ R
  · simp only [cutKernel, ite_eq_left (cutoff_full_outside hx h hε),
      ite_eq_left (cutoff_full_outside hx h hδ)]
  · simp [hy (lt_of_not_ge h)]

/-- The actual L² truncation theorem and the proved atom estimates imply
strong L¹ convergence of each atom to its actual Hilbert image. -/
lemma atom_limits_of_truncation_convergence {𝕜 : Type} [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) (hT : TruncationConvergence 𝕜 A)
    (hU : UniformAtomBounds 𝕜) : AtomLimits 𝕜 A := by
  intro a
  obtain ⟨c, R, hR, hs, h2, _⟩ := line_atom_energy a
  let v : LineLp 𝕜 2 := h2.toLp a.val
  have heq (ε : ℝ) : truncated ε a.val = truncated ε v := by
    funext x
    exact truncated_congr_ae h2.coeFn_toLp.symm ε x
  have hconv : Tendsto (fun ε : ℝ => eLpNorm
      (fun x => truncated ε a.val x - A v x) 2 volume) (𝓝[>] 0) (𝓝 0) := by
    simpa only [heq] using hT.2 v
  have hIM : TendstoInMeasure volume (fun ε : ℝ => truncated ε a.val) (𝓝[>] 0) (A v) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hconv
  obtain ⟨ns, hns, hna⟩ := hIM.exists_seq_tendsto_ae'
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ R := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds hR)]
      with ε hε hεR
    exact ⟨hε, hεR.le⟩
  have htail : ∀ᵐ x : ℝ, 2*R < |x-c| → A v x = truncated R a.val x := by
    filter_upwards [hna] with x hx hfar
    have hevent : (fun n => truncated (ns n) a.val x) =ᶠ[atTop]
        (fun _ => truncated R a.val x) := by
      filter_upwards [hns.eventually hsmall] with n hn
      exact truncated_atom_far_stable a (hs.mono fun _ h => h.1) hn.2 le_rfl hfar
    exact tendsto_nhds_unique hx (tendsto_const_nhds.congr' hevent.symm)
  let B := {x : ℝ | |x-c| ≤ 2*R}
  have hB : MeasurableSet B := by dsimp [B]; measurability
  have hball : B = Metric.closedBall c (2*R) := by
    ext x
    simp only [B, mem_ofPred_eq, Metric.mem_closedBall, Real.dist_eq]
  have hBfinite : volume B ≠ ∞ := by rw [hball]; exact measure_closedBall_lt_top.ne
  haveI : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hBfinite.lt_top⟩
  have hlocal : IntegrableOn (fun x : ℝ => A v x) B :=
    ((Lp.memLp (A v)).restrict B).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  obtain ⟨_, _, hu⟩ := hU
  have hfar : IntegrableOn (fun x : ℝ => A v x) Bᶜ := by
    apply ((hu R hR a).1.integrableOn).congr
    filter_upwards [ae_restrict_of_ae htail, ae_restrict_mem hB.compl] with x hx hxB
    exact (hx (by simpa [B] using hxB)).symm
  have hi : Integrable (fun x : ℝ => A v x) := by
    simpa only [union_compl_self, integrableOn_univ] using hlocal.union hfar
  let g : LineLp 𝕜 1 := hi.toL1 (fun x : ℝ => A v x)
  have hg : (g : ℝ → 𝕜) =ᵐ[volume] (A v : ℝ → 𝕜) := hi.coeFn_toL1
  refine ⟨h2, g, hg, ?_⟩
  have hfactor : (volume.restrict B Set.univ) ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    exact measure_ne_top _ _
  have hmajor : Tendsto (fun ε : ℝ =>
      eLpNorm (fun x => truncated ε a.val x - A v x) 2 volume *
        (volume.restrict B Set.univ) ^
          (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hconv (Or.inr hfactor)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · exact .of_forall fun _ => bot_le
  · filter_upwards [hsmall] with ε hε
    have he : (fun x => truncated ε a.val x - g x) =ᵐ[volume]
        B.indicator (fun x => truncated ε a.val x - A v x) := by
      filter_upwards [hg, htail] with x hx hxT
      by_cases hxB : x ∈ B
      · rw [indicator_of_mem hxB, hx]
      · rw [indicator_of_notMem hxB, hx]
        have hfar : 2*R < |x-c| := by simpa [B] using hxB
        rw [truncated_atom_far_stable a (hs.mono fun _ h => h.1) hε.2 le_rfl hfar,
          hxT hfar, sub_self]
    rw [eLpNorm_congr_ae he, eLpNorm_indicator_eq_eLpNorm_restrict hB.nullMeasurableSet]
    exact (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((truncated_aestronglyMeasurable ε a.val).sub (Lp.aestronglyMeasurable (A v))).restrict).trans
      (mul_le_mul_of_nonneg_right (eLpNorm_restrict_le _ _ _ _) (by positivity))


lemma atom_limit_norm_bound {𝕜 : Type} [RCLike 𝕜] {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (ε : ℝ), 0 < ε → ∀ a : LineAtom 𝕜,
      Integrable (truncated ε a.val) volume ∧
        (∫ x : ℝ, ‖truncated ε a.val x‖) ≤ C)
    (a : LineAtom 𝕜) (g : LineLp 𝕜 1)
    (hg : Tendsto (fun ε : ℝ => eLpNorm
      (fun x => truncated ε a.val x - g x) 1 volume) (𝓝[>] 0) (𝓝 0)) :
    ‖g‖ ≤ C := by
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal C + eLpNorm
      (fun x => truncated ε a.val x - g x) 1 volume)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal C)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hg
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ENNReal.ofReal ‖g‖ ≤ ENNReal.ofReal C + eLpNorm
        (fun x => truncated ε a.val x - g x) 1 volume := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hi := (hb ε hε a).1
    have hcut : eLpNorm (truncated ε a.val) 1 volume ≤ ENNReal.ofReal C := by
      let v : LineLp 𝕜 1 := hi.toL1 (truncated ε a.val)
      calc
        _ = eLpNorm (v : ℝ → 𝕜) 1 volume := eLpNorm_congr_ae hi.coeFn_toL1.symm
        _ = ENNReal.ofReal ‖v‖ := by rw [← Lp.enorm_def, ← ofReal_norm]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by
          rw [MeasureTheory.L1.norm_eq_integral_norm]
          exact (integral_congr_ae (hi.coeFn_toL1.mono fun x hx => congrArg norm hx)).le.trans
            (hb ε hε a).2)
    have htri := eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞))
      (f := truncated ε a.val) (g := fun x => g x - truncated ε a.val x) le_rfl
    have hsum : (fun x => truncated ε a.val x + (g x - truncated ε a.val x)) = g := by
      funext x; abel
    change eLpNorm (fun x => truncated ε a.val x + (g x - truncated ε a.val x))
      1 volume ≤ _ at htri
    rw [hsum, ← Lp.enorm_def, ← ofReal_norm] at htri
    exact htri.trans (add_le_add hcut (le_of_eq (eLpNorm_sub_comm _ _ _ _)))
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (ge_of_tendsto ht he)

lemma weak_atom_limit_bound {𝕜 : Type} [RCLike 𝕜]
    {A : LineLp 𝕜 2 → LineLp 𝕜 2} (S : Extensions 𝕜 A)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (ε : ℝ), 0 < ε → ∀ a : LineAtom 𝕜,
      Integrable (truncated ε a.val) volume ∧
        (∫ x : ℝ, ‖truncated ε a.val x‖) ≤ C)
    (hl : AtomLimits 𝕜 A) (a : LineAtom 𝕜) :
    ∃ g : LineLp 𝕜 1,
      (g : ℝ → 𝕜) =ᵐ[volume] (S.weak a.val : ℝ → 𝕜) ∧ ‖g‖ ≤ C := by
  obtain ⟨h2, g, he, hg⟩ := hl a
  have hs := S.weak_agrees a.val (Lp.memLp a.val) h2
  rw [Lp.toLp_coeFn] at hs
  exact ⟨g, he.trans hs.symm, atom_limit_norm_bound hC hb a g hg⟩

lemma weak_limit_series {𝕜 : Type} [RCLike 𝕜]
    {A : LineLp 𝕜 2 → LineLp 𝕜 2} (S : Extensions 𝕜 A)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a : LineAtom 𝕜, ∃ g : LineLp 𝕜 1,
      (g : ℝ → 𝕜) =ᵐ[volume] (S.weak a.val : ℝ → 𝕜) ∧ ‖g‖ ≤ C)
    (hcontinuous : ∀ (u : ℕ → LineLp 𝕜 1) (f : LineLp 𝕜 1),
      Tendsto u atTop (𝓝 f) →
        TendstoInMeasure volume (fun n => (S.weak (u n) : ℝ → 𝕜)) atTop (S.weak f))
    (a : ℕ → LineAtom 𝕜) (b : ℕ → 𝕜) (hbn : Summable (fun j => ‖b j‖))
    (f : LineLp 𝕜 1) (hf : HasSum (fun j => b j • (a j).val) f) :
    ∃ g : LineLp 𝕜 1,
      (g : ℝ → 𝕜) =ᵐ[volume] (S.weak f : ℝ → 𝕜) ∧
      ‖g‖ ≤ C * ∑' j, ‖b j‖ := by
  choose g hg hgn using fun j => hb (a j)
  have hbound (j : ℕ) : ‖b j • g j‖ ≤ C * ‖b j‖ := by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgn j) (norm_nonneg _)
  have hs : Summable (fun j => b j • g j) :=
    (hbn.mul_left C).of_norm_bounded hbound
  let G : LineLp 𝕜 1 := ∑' j, b j • g j
  let u : ℕ → LineLp 𝕜 1 := fun n => ∑ j ∈ Finset.range n, b j • (a j).val
  let v : ℕ → LineLp 𝕜 1 := fun n => ∑ j ∈ Finset.range n, b j • g j
  have heq (n : ℕ) : (v n : ℝ → 𝕜) =ᵐ[volume] (S.weak (u n) : ℝ → 𝕜) := by
    have hterm (j : ℕ) : ((b j • g j : LineLp 𝕜 1) : ℝ → 𝕜) =ᵐ[volume]
        (S.weak (b j • (a j).val) : ℝ → 𝕜) := by
      rw [map_smul]
      exact (Lp.coeFn_smul _ _).trans
        (((hg j).const_smul (b j)).trans (AEEqFun.coeFn_smul _ _).symm)
    dsimp [u, v]
    rw [map_sum]
    exact (Lp.coeFn_finsetSum _ _).trans
      ((eventuallyEq_sum fun j _ => hterm j).trans (AEEqFun.coeFn_finsetSum _ _).symm)
  have hv : TendstoInMeasure volume (fun n => (v n : ℝ → 𝕜)) atTop G :=
    tendstoInMeasure_of_tendsto_Lp hs.hasSum.tendsto_sum_nat
  have hu : TendstoInMeasure volume (fun n => (S.weak (u n) : ℝ → 𝕜)) atTop (S.weak f) :=
    hcontinuous u f hf.tendsto_sum_nat
  refine ⟨G, tendstoInMeasure_ae_unique hv (hu.congr_left fun n => (heq n).symm), ?_⟩
  exact hs.hasSum.norm_le_of_bounded
    (by simpa only [tsum_mul_left] using (hbn.mul_left C).hasSum) hbound

lemma weak_limit_synthesis {𝕜 : Type} [RCLike 𝕜]
    {A : LineLp 𝕜 2 → LineLp 𝕜 2} (S : Extensions 𝕜 A)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a : LineAtom 𝕜, ∃ g : LineLp 𝕜 1,
      (g : ℝ → 𝕜) =ᵐ[volume] (S.weak a.val : ℝ → 𝕜) ∧ ‖g‖ ≤ C)
    (hcontinuous : ∀ (u : ℕ → LineLp 𝕜 1) (f : LineLp 𝕜 1),
      Tendsto u atTop (𝓝 f) →
        TendstoInMeasure volume (fun n => (S.weak (u n) : ℝ → 𝕜)) atTop (S.weak f))
    (c : CoefficientsValue (𝕜 := 𝕜) (volume : Measure ℝ)) :
    ∃ g : LineLp 𝕜 1,
      (g : ℝ → 𝕜) =ᵐ[volume] (S.weak (SynthesisValue volume c) : ℝ → 𝕜) ∧
      ‖g‖ ≤ C * ‖c‖ := by
  have : Nonempty (LineAtom 𝕜) := by
    obtain ⟨a, _⟩ := AtomicHardySpace.raw_atom_realization (volume : Measure ℝ)
      (fun _ => (0 : 𝕜)) aestronglyMeasurable_zero (by simp)
      ⟨0, 1, zero_lt_one, (Metric.measure_ball_pos volume 0 zero_lt_one).ne',
        measure_ball_ne_top, Filter.Eventually.of_forall (fun x => by
          simp only [norm_zero, implies_true, true_and]
          positivity)⟩
    exact ⟨a⟩
  obtain ⟨a, b, hbn, hf⟩ := AtomicHardySpace.coefficient_sequence volume c
  obtain ⟨g, hg, hn⟩ := weak_limit_series S hC hb hcontinuous a b hbn.summable _ hf
  exact ⟨g, hg, hbn.tsum_eq ▸ hn⟩

lemma weak_limit_hardy {𝕜 : Type} [RCLike 𝕜]
    {A : LineLp 𝕜 2 → LineLp 𝕜 2} (S : Extensions 𝕜 A)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a : LineAtom 𝕜, ∃ g : LineLp 𝕜 1,
      (g : ℝ → 𝕜) =ᵐ[volume] (S.weak a.val : ℝ → 𝕜) ∧ ‖g‖ ≤ C)
    (hcontinuous : ∀ (u : ℕ → LineLp 𝕜 1) (f : LineLp 𝕜 1),
      Tendsto u atTop (𝓝 f) →
        TendstoInMeasure volume (fun n => (S.weak (u n) : ℝ → 𝕜)) atTop (S.weak f))
    (h : LineHardy 𝕜) :
    ∃ g : LineLp 𝕜 1,
      (g : ℝ → 𝕜) =ᵐ[volume] (S.weak (EmbeddingValue volume h) : ℝ → 𝕜) ∧
      ‖g‖ ≤ C * ‖h‖ := by
  obtain ⟨c₀, hc₀⟩ := (KernelValue (𝕜 := 𝕜) (volume : Measure ℝ)).mkQ_surjective h
  obtain ⟨g, hg, _⟩ := weak_limit_synthesis S hC hb hcontinuous c₀
  have he₀ : SynthesisValue volume c₀ = EmbeddingValue volume h :=
    congrArg (EmbeddingValue volume) hc₀
  rw [he₀] at hg
  refine ⟨g, hg, le_of_forall_pos_le_add fun ε hε => ?_⟩
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  obtain ⟨c, hc, hcn⟩ := Submodule.Quotient.norm_mk_lt h hδ
  obtain ⟨g', hg', hgn⟩ := weak_limit_synthesis S hC hb hcontinuous c
  have he : SynthesisValue volume c = EmbeddingValue volume h :=
    congrArg (EmbeddingValue volume) hc
  rw [he] at hg'
  have hgg : g = g' := Lp.ext (hg.trans hg'.symm)
  rw [hgg]
  calc
    ‖g'‖ ≤ C * ‖c‖ := hgn
    _ ≤ C * (‖h‖ + ε / (C + 1)) := mul_le_mul_of_nonneg_left hcn.le hC
    _ ≤ C * ‖h‖ + ε := by
      have hsmall : C * (ε / (C + 1)) ≤ ε := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by linarith : 0 < C + 1)).mpr
        nlinarith
      nlinarith

/-- The atomic L1 limits give a bounded realization of every compatible weak
extension on the manuscript's original quotient-norm Hardy space. -/
lemma bounded_limit_map {𝕜 : Type} [RCLike 𝕜]
    {A : LineLp 𝕜 2 → LineLp 𝕜 2} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (ε : ℝ), 0 < ε → ∀ a : LineAtom 𝕜,
      Integrable (truncated ε a.val) volume ∧
        (∫ x : ℝ, ‖truncated ε a.val x‖) ≤ C)
    (hl : AtomLimits 𝕜 A) (S : Extensions 𝕜 A) :
    ∃ E : LineHardy 𝕜 →L[𝕜] LineLp 𝕜 1, ‖E‖ ≤ C ∧
      ∀ h : LineHardy 𝕜, (E h : ℝ → 𝕜) =ᵐ[volume]
        (S.weak (EmbeddingValue volume h) : ℝ → 𝕜) := by
  have ha := weak_atom_limit_bound S hC hb hl
  choose g hg hgn using fun h : LineHardy 𝕜 => weak_limit_hardy S hC ha
    (extensions_weak_tendstoInMeasure 𝕜 A S) h
  let L : LineHardy 𝕜 →ₗ[𝕜] LineLp 𝕜 1 := {
    toFun := g
    map_add' x y := by
      apply Lp.ext
      have he : (S.weak (EmbeddingValue volume (x + y)) : ℝ → 𝕜) =ᵐ[volume]
          (fun z => S.weak (EmbeddingValue volume x) z + S.weak (EmbeddingValue volume y) z) := by
        rw [map_add, map_add]
        exact AEEqFun.coeFn_add _ _
      exact (hg (x + y)).trans (he.trans
        (((Lp.coeFn_add _ _).trans ((hg x).add (hg y))).symm))
    map_smul' k x := by
      change g (k • x) = k • g x
      apply Lp.ext
      have he : (S.weak (EmbeddingValue volume (k • x)) : ℝ → 𝕜) =ᵐ[volume]
          (fun z => k • S.weak (EmbeddingValue volume x) z) := by
        rw [map_smul, map_smul]
        exact AEEqFun.coeFn_smul _ _
      exact (hg (k • x)).trans (he.trans
        (((Lp.coeFn_smul _ _).trans ((hg x).const_smul k)).symm)) }
  let E : LineHardy 𝕜 →L[𝕜] LineLp 𝕜 1 := L.mkContinuous C hgn
  exact ⟨E, E.opNorm_le_bound hC hgn, hg⟩

lemma truncated_series {𝕜 : Type} [RCLike 𝕜] {C ε : ℝ} (hε : 0 < ε)
    (hB : ∀ a : LineAtom 𝕜, Integrable (truncated ε a.val) volume ∧
      (∫ x : ℝ, ‖truncated ε a.val x‖) ≤ C)
    (a : ℕ → LineAtom 𝕜) (b : ℕ → 𝕜) (hb : Summable (fun j => ‖b j‖))
    (f : LineLp 𝕜 1) (hf : HasSum (fun j => b j • (a j).val) f) :
    ∃ g : LineLp 𝕜 1,
      (g : ℝ → 𝕜) =ᵐ[volume] truncated ε f ∧
      ‖g‖ ≤ C * ∑' j, ‖b j‖ := by
  let g : ℕ → LineLp 𝕜 1 := fun j => (hB (a j)).1.toL1 _
  have hg (j : ℕ) : (g j : ℝ → 𝕜) =ᵐ[volume] truncated ε (a j).val :=
    (hB (a j)).1.coeFn_toL1
  have hgn (j : ℕ) : ‖g j‖ ≤ C := by
    rw [MeasureTheory.L1.norm_eq_integral_norm]
    exact (integral_congr_ae ((hg j).mono fun x hx => congrArg norm hx)).le.trans (hB (a j)).2
  have hbound (j : ℕ) : ‖b j • g j‖ ≤ C * ‖b j‖ := by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgn j) (norm_nonneg _)
  have hs : Summable (fun j => b j • g j) :=
    (hb.mul_left C).of_norm_bounded hbound
  let G : LineLp 𝕜 1 := ∑' j, b j • g j
  let u : ℕ → LineLp 𝕜 1 := fun n => ∑ j ∈ Finset.range n, b j • (a j).val
  let v : ℕ → LineLp 𝕜 1 := fun n => ∑ j ∈ Finset.range n, b j • g j
  have heq (n : ℕ) : (v n : ℝ → 𝕜) =ᵐ[volume] truncated ε (u n) := by
    have hterm (j : ℕ) : ((b j • g j : LineLp 𝕜 1) : ℝ → 𝕜) =ᵐ[volume]
        fun x => b j • truncated ε (a j).val x := by
      exact (Lp.coeFn_smul _ _).trans ((hg j).const_smul (b j))
    have he (x : ℝ) : truncated ε (u n) x =
        ∑ j ∈ Finset.range n, b j • truncated ε (a j).val x := by
      exact map_sum (truncatedEvaluation ε hε x) _ _ |>.trans
        (Finset.sum_congr rfl fun j _ => map_smul (truncatedEvaluation ε hε x) _ _)
    exact (Lp.coeFn_finsetSum _ _).trans
      ((eventuallyEq_sum fun j _ => hterm j).trans (Eventually.of_forall fun x => by simpa only [Finset.sum_apply] using (he x).symm))
  have hv : TendstoInMeasure volume (fun n => (v n : ℝ → 𝕜)) atTop G :=
    tendstoInMeasure_of_tendsto_Lp hs.hasSum.tendsto_sum_nat
  obtain ⟨ns, hns, hvns⟩ := hv.exists_seq_tendsto_ae
  have h_all : ∀ᵐ x : ℝ ∂volume, ∀ n, (v n : ℝ → 𝕜) x = truncated ε (u n) x :=
    ae_all_iff.mpr heq
  refine ⟨G, ?_, ?_⟩
  · filter_upwards [hvns, h_all] with x hx he
    have hf' : Tendsto (fun n => truncated ε (u n) x) atTop (𝓝 (truncated ε f x)) :=
      ((truncatedEvaluation ε hε x).continuous.tendsto f).comp hf.tendsto_sum_nat
    have hfns := hf'.comp hns.tendsto_atTop
    exact tendsto_nhds_unique hx (hfns.congr fun n => (he (ns n)).symm)
  · exact hs.hasSum.norm_le_of_bounded
      (by simpa only [tsum_mul_left] using (hb.mul_left C).hasSum) hbound

lemma truncated_synthesis {𝕜 : Type} [RCLike 𝕜] {C ε : ℝ} (hε : 0 < ε)
    (hB : ∀ a : LineAtom 𝕜, Integrable (truncated ε a.val) volume ∧
      (∫ x : ℝ, ‖truncated ε a.val x‖) ≤ C)
    (c : CoefficientsValue (𝕜 := 𝕜) (volume : Measure ℝ)) :
    ∃ g : LineLp 𝕜 1,
      (g : ℝ → 𝕜) =ᵐ[volume] truncated ε (SynthesisValue volume c) ∧
      ‖g‖ ≤ C * ‖c‖ := by
  have : Nonempty (LineAtom 𝕜) := by
    obtain ⟨a, ha⟩ := AtomicHardySpace.raw_atom_realization volume (fun _ : ℝ => (0 : 𝕜))
      aestronglyMeasurable_zero (by simp)
      ⟨0, 1, zero_lt_one, by simp, by simp, .of_forall fun x => by simp⟩
    exact ⟨a⟩
  obtain ⟨a, b, hb, hf⟩ := AtomicHardySpace.coefficient_sequence volume c
  obtain ⟨g, hg, hn⟩ := truncated_series hε hB a b hb.summable _ hf
  exact ⟨g, hg, hb.tsum_eq ▸ hn⟩

lemma truncated_hardy {𝕜 : Type} [RCLike 𝕜] {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hB : ∀ a : LineAtom 𝕜, Integrable (truncated ε a.val) volume ∧
      (∫ x : ℝ, ‖truncated ε a.val x‖) ≤ C)
    (h : LineHardy 𝕜) :
    ∃ g : LineLp 𝕜 1,
      (g : ℝ → 𝕜) =ᵐ[volume] truncated ε (EmbeddingValue volume h) ∧
      ‖g‖ ≤ C * ‖h‖ := by
  obtain ⟨c₀, hc₀⟩ := (KernelValue (𝕜 := 𝕜) (volume : Measure ℝ)).mkQ_surjective h
  obtain ⟨g, hg, _⟩ := truncated_synthesis hε hB c₀
  have he₀ : SynthesisValue volume c₀ = EmbeddingValue volume h :=
    congrArg (EmbeddingValue volume) hc₀
  rw [he₀] at hg
  refine ⟨g, hg, le_of_forall_pos_le_add fun δ hδ => ?_⟩
  have hη : 0 < δ / (C + 1) := div_pos hδ (by linarith)
  obtain ⟨c, hc, hcn⟩ := Submodule.Quotient.norm_mk_lt h hη
  obtain ⟨g', hg', hgn⟩ := truncated_synthesis hε hB c
  have he : SynthesisValue volume c = EmbeddingValue volume h :=
    congrArg (EmbeddingValue volume) hc
  rw [he] at hg'
  have hgg : g = g' := Lp.ext (hg.trans hg'.symm)
  rw [hgg]
  calc
    ‖g'‖ ≤ C * ‖c‖ := hgn
    _ ≤ C * (‖h‖ + δ / (C + 1)) := mul_le_mul_of_nonneg_left hcn.le hC
    _ ≤ C * ‖h‖ + δ := by
      have hsmall : C * (δ / (C + 1)) ≤ δ := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by linarith : 0 < C + 1)).mpr
        nlinarith
      nlinarith

lemma truncated_hardy_map {𝕜 : Type} [RCLike 𝕜] {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ (ε : ℝ), 0 < ε → ∀ a : LineAtom 𝕜,
      Integrable (truncated ε a.val) volume ∧ (∫ x : ℝ, ‖truncated ε a.val x‖) ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : LineHardy 𝕜 →L[𝕜] LineLp 𝕜 1, ‖U‖ ≤ C ∧
      ∀ h : LineHardy 𝕜, Integrable (truncated ε (EmbeddingValue volume h)) volume ∧
      (U h : ℝ → 𝕜) =ᵐ[volume] truncated ε (EmbeddingValue volume h) := by
  choose g hg hgn using fun h : LineHardy 𝕜 => truncated_hardy hC hε (hB ε hε) h
  let L : LineHardy 𝕜 →ₗ[𝕜] LineLp 𝕜 1 := {
    toFun := g
    map_add' x y := by
      apply Lp.ext
      have he : truncated ε (EmbeddingValue volume (x+y)) =ᵐ[volume]
          (fun z => truncated ε (EmbeddingValue volume x) z + truncated ε (EmbeddingValue volume y) z) := by
        apply Eventually.of_forall
        intro z
        rw [map_add]
        exact map_add (truncatedEvaluation ε hε z) _ _
      exact (hg (x+y)).trans (he.trans
        (((Lp.coeFn_add _ _).trans ((hg x).add (hg y))).symm))
    map_smul' k x := by
      change g (k • x) = k • g x
      apply Lp.ext
      have he : truncated ε (EmbeddingValue volume (k • x)) =ᵐ[volume]
          (fun z => k • truncated ε (EmbeddingValue volume x) z) := by
        apply Eventually.of_forall
        intro z
        rw [map_smul]
        exact map_smul (truncatedEvaluation ε hε z) _ _
      exact (hg (k • x)).trans (he.trans
        (((Lp.coeFn_smul _ _).trans ((hg x).const_smul k)).symm)) }
  let U : LineHardy 𝕜 →L[𝕜] LineLp 𝕜 1 := L.mkContinuous C hgn
  refine ⟨U, U.opNorm_le_bound hC hgn, fun h => ?_⟩
  exact ⟨(MeasureTheory.L1.integrable_coeFn (g h)).congr (hg h), hg h⟩

lemma hardy_atomic_hasSum {𝕜 : Type} [RCLike 𝕜]
    (c : CoefficientsValue (𝕜 := 𝕜) (volume : Measure ℝ)) :
    HasSum (fun a : LineAtom 𝕜 => c a • AtomicHardySpace.atomElement volume a)
      ((KernelValue volume).mkQ c) := by
  classical
  have hs := (KernelValue (𝕜 := 𝕜) (volume : Measure ℝ)).mkQL.hasSum
    (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) c)
  convert hs using 1
  funext a
  change c a • (KernelValue volume).mkQ (lp.single 1 a (1 : 𝕜)) =
    (KernelValue volume).mkQ (lp.single 1 a (c a))
  rw [← map_smul, ← lp.single_smul, smul_eq_mul, mul_one]
  rfl

lemma hardy_uniform_convergence {𝕜 : Type} [RCLike 𝕜]
    (E : LineHardy 𝕜 →L[𝕜] LineLp 𝕜 1)
    (U : ℝ → LineHardy 𝕜 →L[𝕜] LineLp 𝕜 1)
    {C : ℝ} (hC : 0 ≤ C) (hU : ∀ ε, ‖U ε‖ ≤ C)
    (ha : ∀ a : LineAtom 𝕜, Tendsto (fun ε => U ε (AtomicHardySpace.atomElement volume a))
      (𝓝[>] 0) (𝓝 (E (AtomicHardySpace.atomElement volume a)))) :
    ∀ h : LineHardy 𝕜, Tendsto (fun ε => U ε h) (𝓝[>] 0) (𝓝 (E h)) := by
  intro h
  obtain ⟨c, rfl⟩ := (KernelValue (𝕜 := 𝕜) (volume : Measure ℝ)).mkQ_surjective h
  have hs := hardy_atomic_hasSum c
  have hb : Summable (fun a : LineAtom 𝕜 => C * ‖c a‖) :=
    by simpa using ((lp.memℓp c).summable (by simp)).mul_left C
  have ht := tendsto_tsum_of_dominated_convergence hb
    (fun a : LineAtom 𝕜 => (ha a).const_smul (c a))
    (Eventually.of_forall fun ε a => ?_)
  · simp_rw [← map_smul] at ht
    simpa only [← ContinuousLinearMap.map_tsum _ hs.summable, hs.tsum_eq] using ht
  · rw [norm_smul]
    calc
      ‖c a‖ * ‖U ε (AtomicHardySpace.atomElement volume a)‖ ≤
          ‖c a‖ * (C * ‖AtomicHardySpace.atomElement volume a‖) := by
        gcongr
        exact ((U ε).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hU ε) (norm_nonneg _))
      _ ≤ ‖c a‖ * C := by
        gcongr
        exact mul_le_of_le_one_right hC (AtomicHardySpace.atomElement_norm volume a)
      _ = _ := mul_comm _ _

lemma hardy_cutoff_convergence {𝕜 : Type} [RCLike 𝕜]
    {A : LineLp 𝕜 2 → LineLp 𝕜 2} (S : Extensions 𝕜 A)
    (hAtom : AtomLimits 𝕜 A)
    (E : LineHardy 𝕜 →L[𝕜] LineLp 𝕜 1)
    (hE : ∀ h : LineHardy 𝕜, (E h : ℝ → 𝕜) =ᵐ[volume]
      (S.weak (EmbeddingValue volume h) : ℝ → 𝕜))
    (U : ∀ ε : ℝ, 0 < ε → LineHardy 𝕜 →L[𝕜] LineLp 𝕜 1)
    {C : ℝ} (hC : 0 ≤ C) (hU : ∀ ε hε, ‖U ε hε‖ ≤ C)
    (hUi : ∀ ε hε (h : LineHardy 𝕜),
      (U ε hε h : ℝ → 𝕜) =ᵐ[volume] truncated ε (EmbeddingValue volume h)) :
    ∀ h : LineHardy 𝕜, Tendsto (fun ε : ℝ => eLpNorm
      (fun x => truncated ε (EmbeddingValue volume h) x - E h x) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  classical
  let U' : ℝ → LineHardy 𝕜 →L[𝕜] LineLp 𝕜 1 := fun ε =>
    if hε : 0 < ε then U ε hε else 0
  have hb : ∀ ε, ‖U' ε‖ ≤ C := by
    intro ε
    dsimp [U']
    split_ifs with hε
    · exact hU ε hε
    · rw [show ‖(0 : LineHardy 𝕜 →L[𝕜] LineLp 𝕜 1)‖ = 0 from ContinuousLinearMap.opNorm_zero]
      exact hC
  have ha (a : LineAtom 𝕜) : Tendsto (fun ε => U' ε (AtomicHardySpace.atomElement volume a))
      (𝓝[>] 0) (𝓝 (E (AtomicHardySpace.atomElement volume a))) := by
    obtain ⟨h2, g, hg, ht⟩ := hAtom a
    have he : E (AtomicHardySpace.atomElement volume a) = g := by
      apply Lp.ext
      have hw := S.weak_agrees a.val (Lp.memLp a.val) h2
      rw [Lp.toLp_coeFn] at hw
      have hEa := hE (AtomicHardySpace.atomElement volume a)
      rw [AtomicHardySpace.embedding_atomElement] at hEa
      exact hEa.trans (hw.trans hg.symm)
    rw [he, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    apply eLpNorm_congr_ae
    have heq := hUi ε hε (AtomicHardySpace.atomElement volume a)
    simp only [AtomicHardySpace.embedding_atomElement] at heq
    simp only [U', dite_eq_left hε]
    filter_upwards [heq] with x hx
    exact congrArg (fun z => z - g x) hx.symm
  intro h
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun ε => U' ε h) (E h)).mp
    (hardy_uniform_convergence E U' hC hb ha h)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  apply eLpNorm_congr_ae
  simp only [U', dite_eq_left hε]
  filter_upwards [hUi ε hε h] with x hx
  exact congrArg (fun z => z - E h x) hx

/-- The atom estimates and their actual Hilbert limits give the full endpoint,
with one constant chosen before any compatible weak realization. -/
lemma endpoint_of_atom_limits {𝕜 : Type} [RCLike 𝕜]
    {A : LineLp 𝕜 2 → LineLp 𝕜 2}
    (hB : UniformAtomBounds 𝕜) (hL : AtomLimits 𝕜 A) :
    HardyHilbertTruncationConvergenceSpec.Endpoint 𝕜 A := by
  obtain ⟨C, hC, hb⟩ := hB
  refine ⟨C, hC, ?_⟩
  intro S
  obtain ⟨E, hEn, hE⟩ := bounded_limit_map hC hb hL S
  choose U hUn hUi using truncated_hardy_map hC hb
  refine ⟨E, U, hEn, hE, ?_, ?_⟩
  · intro ε hε
    exact ⟨hUn ε hε, hUi ε hε⟩
  · exact hardy_cutoff_convergence S hL E hE U hC hUn
      (fun ε hε h => (hUi ε hε h).2)

/-- The original complex Fourier multiplier is the strong L¹ limit. -/
theorem complex_endpoint :
    HardyHilbertTruncationConvergenceSpec.Endpoint ℂ complexHilbert :=
  endpoint_of_atom_limits uniform_atom_bounds.1
    (atom_limits_of_truncation_convergence complexHilbert
      complex_truncation_convergence uniform_atom_bounds.1)

/-- The real endpoint uses the fixed restriction of that same multiplier. -/
theorem real_endpoint :
    HardyHilbertTruncationConvergenceSpec.Endpoint ℝ realOperator :=
  endpoint_of_atom_limits uniform_atom_bounds.2
    (atom_limits_of_truncation_convergence realOperator
      real_truncation_convergence uniform_atom_bounds.2)

/-- Symmetric Hilbert truncations have uniformly bounded H¹→L¹ norms and
converge strongly on every element of the completed atomic space, over both
original scalar fields and compatibly with the previously defined transform. -/
theorem full_theorem : HardyHilbertTruncationConvergenceSpec.FullTheorem :=
  ⟨truncated_l1_existence, complex_endpoint,
    realOperator, real_restriction, real_endpoint⟩

end ExpandedFA.Hardy.HardyHilbertTruncationConvergence
