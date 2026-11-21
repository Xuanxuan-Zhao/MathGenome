import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinNonunique
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinEven
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinNonuniqueFourier
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinNonuniqueCoshSeries

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace ExpandedFA.PartIV.KreinNonunique
open KreinSolutions.Specs

/-- Dominated convergence on a neighborhood suffices even for unbounded p. -/
theorem represented_regular {p : ℝ → ℝ} {ν : Measure ℝ}
    (h : KreinEven.Spec.Represents p ν) : Continuous p ∧ Function.Even p := by
  constructor
  · rw [continuous_iff_continuousAt]
    intro s
    obtain ⟨g, hg, hbound⟩ := KreinEven.compact_domination p ν h (|s| + 1) (by positivity)
    have hloc : ∀ᶠ t in 𝓝 s, |t| ≤ |s| + 1 := by
      filter_upwards [Metric.ball_mem_nhds s (by norm_num : (0 : ℝ) < 1)] with t ht
      have hd : |t - s| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using ht
      calc
        |t| ≤ |t - s| + |s| := by simpa using abs_add_le (t-s) s
        _ ≤ |s| + 1 := by linarith
    have hc : ContinuousAt (fun t => ∫ ξ, CValue ξ t ∂ν) s := by
      apply continuousAt_of_dominated
        (Eventually.of_forall fun t => (h.2.2.1 t).1.aestronglyMeasurable)
        (hloc.mono fun t ht => Eventually.of_forall fun ξ => ?_) hg
        (Eventually.of_forall fun ξ => ?_)
      · simpa only [Real.norm_eq_abs] using hbound ξ t ht
      · exact (KreinSolutions.firstDerivatives ξ s).1.continuousAt
    exact hc.congr (Eventually.of_forall fun t => (h.2.2.1 t).2.symm)
  · intro s
    rw [(h.2.2.1 (-s)).2, (h.2.2.1 s).2]
    apply integral_congr_ae
    exact Eventually.of_forall fun ξ => (KreinSolutions.parity ξ).1 s

theorem mixture_regular : Spec.MixtureRegularity := by
  intro p α β h
  obtain ⟨ν, hν⟩ := KreinEven.representation_of_mixture h
  exact represented_regular hν

theorem mixture_scaling : Spec.MixtureScaling := by
  intro p α β c hc h
  let := h.1
  let := h.2.1
  have hct : (ENNReal.ofReal c).toReal = c := ENNReal.toReal_ofReal hc
  refine ⟨α.smul_finite ENNReal.ofReal_ne_top, β.smul_finite ENNReal.ofReal_ne_top,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [Measure.smul_apply, h.2.2.1]
  · simp [Measure.smul_apply, h.2.2.2.1]
  · simp only [measureReal_ennreal_smul_apply, hct]
    rw [← mul_add, h.2.2.2.2.1]
  · intro s
    obtain ⟨ha, hb, heq⟩ := h.2.2.2.2.2.1 s
    refine ⟨ha.smul_measure ENNReal.ofReal_ne_top,
      hb.smul_measure ENNReal.ofReal_ne_top, ?_⟩
    simp only [integral_smul_measure, hct, smul_eq_mul]
    rw [← mul_add, heq]
  · intro R hR
    exact (h.2.2.2.2.2.2 R hR).smul_measure ENNReal.ofReal_ne_top

theorem normalize_counterexample : Spec.NormalizeCounterexample := by
  intro p α₁ β₁ α₂ β₂ h₁ h₂ hp hb₁ hb₂
  let c : ℝ := (p 0)⁻¹
  have hc : 0 < c := inv_pos.mpr hp
  have h₁' := mixture_scaling p α₁ β₁ c hc.le h₁
  have h₂' := mixture_scaling p α₂ β₂ c hc.le h₂
  obtain ⟨hcont, heven⟩ := mixture_regular _ _ _ h₁'
  have htest : KreinEven.Spec.EvenTestPositive (fun s => c * p s) := by
    apply (KreinEven.representation _ hcont heven).mpr
    exact KreinEven.representation_of_mixture h₁'
  refine ⟨(fun s => c * p s), ENNReal.ofReal c • α₁, ENNReal.ofReal c • β₁,
    ENNReal.ofReal c • α₂, ENNReal.ofReal c • β₂, hcont, heven, ?_, htest,
    h₁', h₂', ?_, ?_⟩
  · exact inv_mul_cancel₀ hp.ne'
  · simpa only [Measure.smul_apply, smul_eq_mul] using
      (pos_iff_ne_zero.mpr (mul_ne_zero
        (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) hb₁.ne'))
  · simp [Measure.smul_apply, hb₂]

/-- Pure measure algebra: the atom witnessing nonuniqueness survives every
support convention and a strictly positive common normalization. -/
theorem assemble_counterexample : Spec.AssembleCounterexample := by
  intro h αp αm γ βp βm hc hh
  rcases hc with ⟨hap, ham, hsap, hsam, hcos⟩
  rcases hh with ⟨hg, hbp, hbm, hsg, hsbp, hsbm, hhyp, hmom, hatomm, hatomp⟩
  let := hap
  let := ham
  let := hg
  let := hbp
  let := hbm
  let p : ℝ → ℝ := fun s => (∫ a, Real.cos (a*s) ∂αp) +
    ∫ b, Real.cosh (b*s) ∂βm
  have heq (s : ℝ) : p s = (∫ a, Real.cos (a*s) ∂(αm + γ)) +
      ∫ b, Real.cosh (b*s) ∂βp := by
    rw [integral_add_measure (hcos s).2.1 (hhyp s).1]
    have h₁ := (hcos s).2.2
    have h₂ := (hhyp s).2.2.2
    dsimp [p]
    linarith
  have hleft : KreinEven.Spec.Mixture p αp βm := by
    refine ⟨hap, hbm, hsap, hsbm, ?_, ?_, ?_⟩
    · simp [p, integral_const]
    · intro s
      exact ⟨(hcos s).1, (hhyp s).2.2.1, rfl⟩
    · intro R hR
      exact (hmom R hR).2
  have hright : KreinEven.Spec.Mixture p (αm + γ) βp := by
    refine ⟨inferInstance, hbp, ?_, hsbp, ?_, ?_, ?_⟩
    · simp [Measure.add_apply, hsam, hsg]
    · simpa only [mul_zero, Real.cos_zero, Real.cosh_zero, integral_const,
        smul_eq_mul, mul_one] using (heq 0).symm
    · intro s
      exact ⟨integrable_add_measure.mpr ⟨(hcos s).2.1, (hhyp s).1⟩,
        (hhyp s).2.1, heq s⟩
    · intro R hR
      exact (hmom R hR).1
  have hmass : 0 < βm.real univ :=
    ENNReal.toReal_pos (ne_of_gt (hatomm.trans_le (measure_mono (subset_univ _))))
      (by finiteness)
  have hp : 0 < p 0 := by
    rw [← hleft.2.2.2.2.1]
    exact add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hmass
  exact normalize_counterexample p αp βm (αm + γ) βp hleft hright hp hatomm hatomp

/-- The signed cosine and cosh transforms of `exp (-cosh s)` give two
distinct positive representations, with the zero atom only in the cosine
part. Their common positive mass supplies the normalization at zero. -/
theorem nonunique : Spec.Nonunique := by
  obtain ⟨αp, αm, hc⟩ := KreinNonuniqueFourier.signed_cosine_representation
  obtain ⟨γ, βp, βm, hh⟩ := KreinNonuniqueCoshSeries.discrete_decomposition
  exact assemble_counterexample (fun s => Real.exp (-Real.cosh s))
    αp αm γ βp βm hc hh

end ExpandedFA.PartIV.KreinNonunique
