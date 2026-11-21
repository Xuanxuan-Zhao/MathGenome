import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.SequenceSpaceInclusion
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Counting measure inclusions for arbitrary index types, including empty
and uncountable types. The infinity endpoint, the ordinary a.e. quotient,
countable finite-power support, and the finite-subsum meaning of sums are
all retained. The shared source norms are used in the public statements. -/

open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch10.SequenceSpaceInclusion
open Specs.D11.Ch10.QuotientConstruction

/-- Each coordinate is bounded by the p-norm. Integrating the resulting
power inequality proves the estimate, including zero norms. This lemma
also allows infinite norms; no normalization or division by a norm occurs. -/
theorem eLpNorm_count_antitone {I E : Type*} [MeasurableSpace I]
    [MeasurableSingletonClass I] [NormedAddCommGroup E]
    {f : I → E} {p q : ℝ≥0∞} (hp : 0 < p) (hpq : p ≤ q)
    (hf : AEStronglyMeasurable f Measure.count) :
    eLpNorm f q Measure.count ≤ eLpNorm f p Measure.count := by
  by_cases hpt : p = ∞
  · have hqt : q = ∞ := top_le_iff.mp (hpt ▸ hpq)
    simp [hpt, hqt]
  by_cases hqt : q = ∞
  · rw [hqt, eLpNorm_exponent_top hf, eLpNormEssSup_count]
    exact iSup_le fun i => enorm_le_eLpNorm_count f i hp.ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp.ne' hpt
  have hqr : 0 < q.toReal := ENNReal.toReal_pos (hp.trans_le hpq).ne' hqt
  have hpqr : p.toReal ≤ q.toReal := ENNReal.toReal_mono hqt hpq
  let N := eLpNorm f p Measure.count
  have hint : (∫⁻ i, ‖f i‖ₑ ^ p.toReal ∂Measure.count) = N ^ p.toReal := by
    dsimp [N]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp.ne' hpt hf, one_div,
      ENNReal.rpow_inv_rpow hpr.ne']
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hp.trans_le hpq).ne' hqt hf,
    one_div, ENNReal.rpow_inv_le_iff hqr]
  calc
    (∫⁻ i, ‖f i‖ₑ ^ q.toReal ∂Measure.count) =
        ∫⁻ i, ‖f i‖ₑ ^ (q.toReal - p.toReal) * ‖f i‖ₑ ^ p.toReal ∂Measure.count := by
      congr 1
      funext i
      rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hpqr) hpr.le]
      congr 1
      ring
    _ ≤ ∫⁻ i, N ^ (q.toReal - p.toReal) * ‖f i‖ₑ ^ p.toReal ∂Measure.count := by
      apply lintegral_mono
      intro i
      dsimp only
      exact mul_le_mul (ENNReal.rpow_le_rpow
        (enorm_le_eLpNorm_count f i hp.ne') (sub_nonneg.mpr hpqr))
        le_rfl zero_le zero_le
    _ = N ^ (q.toReal - p.toReal) * N ^ p.toReal := by
      rw [lintegral_const_mul'' _ (hf.enorm.pow_const _), hint]
    _ = N ^ q.toReal := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hpqr) hpr.le]
      congr 1
      ring

theorem counting_integral : Specs.D11.Ch10.SequenceSpaceInclusion.counting_integral := by
  intro I f
  let : MeasurableSpace I := ⊤
  change D11.Ch05.NonnegativeIntegral.nonnegativeIntegral Measure.count f = _
  rw [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral]
  exact lintegral_count f

theorem counting_sum : Specs.D11.Ch10.SequenceSpaceInclusion.counting_sum := by
  intro I f
  exact ENNReal.tsum_eq_iSup_sum

theorem counting_relation : Specs.D11.Ch10.SequenceSpaceInclusion.counting_relation := by
  intro I 𝕜 _ _ _
  let : MeasurableSpace I := ⊤
  intro p f g
  rw [QuotientConstruction.nullRelation_iff_native]
  exact Measure.ae_count_iff.trans funext_iff.symm

theorem raw_inclusion : Specs.D11.Ch10.SequenceSpaceInclusion.raw_inclusion := by
  intro I 𝕜 _ _ _
  let : MeasurableSpace I := ⊤
  intro p q hp hpq f hf
  have hle := eLpNorm_count_antitone (zero_lt_one.trans_le hp) hpq.le hf.2.aestronglyMeasurable
  have hfq : f ∈ rawSpace Measure.count q :=
    ⟨hf.1, hle.trans_lt hf.2.eLpNorm_lt_top⟩
  refine ⟨hfq, ?_⟩
  rw [QuotientConstruction.sourceNorm_bridge Measure.count q (hp.trans hpq.le) ⟨f, hfq⟩,
    QuotientConstruction.sourceNorm_bridge Measure.count p hp ⟨f, hf⟩]
  exact hle

theorem countable_support : Specs.D11.Ch10.SequenceSpaceInclusion.countable_support := by
  intro I 𝕜 _ _ _
  let : MeasurableSpace I := ⊤
  intro p hp hpt f
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hint : (∫⁻ i, ‖f.val i‖ₑ ^ p.toReal ∂Measure.count) < ∞ := by
    have h := f.property.2.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt f.property.2.aestronglyMeasurable] at h
    exact (ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.mpr hpr)).mp h
  rw [lintegral_count] at hint
  have hc := Summable.countable_support_ennreal hint.ne
  apply hc.mono
  intro i hi
  change ‖f.val i‖ₑ ^ p.toReal ≠ 0
  intro hz
  exact hi (enorm_eq_zero.mp ((ENNReal.rpow_eq_zero_iff_of_pos hpr).mp hz))

/-- The inclusion of raw spaces induces an inclusion of their ordinary
null quotients. Both quotients have exactly the same pointwise relation. -/
theorem quotient_inclusion : Specs.D11.Ch10.SequenceSpaceInclusion.quotient_inclusion := by
  intro I 𝕜 _ _ _
  let : MeasurableSpace I := ⊤
  intro p q hp hpq
  let inc : Raw (X := I) (𝕜 := 𝕜) Measure.count p →
      Raw (X := I) (𝕜 := 𝕜) Measure.count q :=
    fun f => ⟨f.val, (raw_inclusion p q hp hpq f.val f.property).1⟩
  let F : QuotientLp (X := I) (𝕜 := 𝕜) Measure.count p →
      QuotientLp (X := I) (𝕜 := 𝕜) Measure.count q :=
    Quotient.map inc (fun _ _ h => h)
  have hF : Function.Injective F := by
    intro a b h
    induction a using Quotient.inductionOn with
    | _ a =>
      induction b using Quotient.inductionOn with
      | _ b =>
        have hh : classOf (inc a) = classOf (inc b) := h
        have hab : nullRelation Measure.count q (inc a) (inc b) := Quotient.exact hh
        exact Quotient.sound hab
  refine ⟨⟨F, hF⟩, fun f => ?_⟩
  exact ⟨(raw_inclusion p q hp hpq f.val f.property).1, rfl,
    (raw_inclusion p q hp hpq f.val f.property).2⟩

end D11.Ch10.SequenceSpaceInclusion
