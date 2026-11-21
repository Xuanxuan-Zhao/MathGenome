import MathGenome.Internal.RealAnalysis.Specs.D11.Ch16.LebesgueNotRiemann
import MathGenome.Internal.RealAnalysis.D11.Ch16.RiemannCriterion
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Dirichlet

noncomputable section
open Set MeasureTheory
namespace D11.Ch16.LebesgueNotRiemann

abbrev dirichlet : ℝ → ℝ := Specs.D11.Ch16.LebesgueNotRiemann.dirichlet_value

theorem exact_values : Specs.D11.Ch16.LebesgueNotRiemann.exact_values := by
  intro x
  rfl

private lemma rational_interval_countable :
    {x : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ ∃ q : ℚ, (q : ℝ) = x}.Countable :=
  (countable_range (fun q : ℚ => (q : ℝ))).mono (fun _ h => h.2)

private lemma measurable_dirichlet : Measurable dirichlet := by
  classical
  have h := (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator
    rational_interval_countable.measurableSet
  convert h using 1
  funext x
  simp only [dirichlet, Specs.D11.Ch16.LebesgueNotRiemann.dirichlet_value,
    Specs.SingleVariableAnalysis.Ch08.Dirichlet.dirichletValue,
    Set.indicator_apply, Set.mem_ofPred_eq]

theorem borel_measurable : Specs.D11.Ch16.LebesgueNotRiemann.borel_measurable := by
  exact ⟨measurable_dirichlet, measurable_dirichlet.comp measurable_subtype_coe⟩

private lemma ae_zero : dirichlet =ᵐ[volume] (fun _ => 0) := by
  have hnull := rational_interval_countable.measure_zero (μ := (volume : Measure ℝ))
  have houtside : ∀ᵐ x ∂(volume : Measure ℝ),
      ¬ (x ∈ Icc (0 : ℝ) 1 ∧ ∃ q : ℚ, (q : ℝ) = x) := by
    simpa only [ae_iff, not_not] using hnull
  filter_upwards [houtside] with x hx
  classical
  change (if x ∈ Icc (0 : ℝ) 1 ∧ ∃ q : ℚ, (q : ℝ) = x then (1 : ℝ) else 0) = 0
  exact ite_eq_right hx

theorem lebesgue_properties : Specs.D11.Ch16.LebesgueNotRiemann.lebesgue_properties := by
  let μ := Specs.D11.Ch02.Completion.completedMeasure_value (volume : Measure ℝ)
  have hm : @Measurable ℝ ℝ
      (Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure ℝ))
      (borel ℝ) dirichlet :=
    measurable_dirichlet.mono le_eventuallyMeasurableSpace le_rfl
  have ha : dirichlet =ᵐ[μ] (fun _ => 0) := ae_zero
  have har : dirichlet =ᵐ[μ.restrict (Icc (0 : ℝ) 1)] (fun _ => 0) :=
    ae_restrict_of_ae ha
  have hi : Integrable dirichlet (μ.restrict (Icc (0 : ℝ) 1)) :=
    (integrable_zero _ _ _).congr har.symm
  refine ⟨hm, har, hi, ?_⟩
  simpa using integral_congr_ae har

theorem discontinuous_everywhere :
    Specs.D11.Ch16.LebesgueNotRiemann.discontinuous_everywhere :=
  SingleVariableAnalysis.Riemann.dirichlet_discontinuous_everywhere

theorem not_riemann_integrable :
    Specs.D11.Ch16.LebesgueNotRiemann.not_riemann_integrable := by
  intro hi
  have hnull := (D11.Ch16.RiemannCriterion.riemann_criterion dirichlet 0 1
    (by norm_num) SingleVariableAnalysis.Riemann.dirichlet_bounded).mp hi
  have heq : {x | x ∈ Icc (0 : ℝ) 1 ∧ ¬ ContinuousWithinAt dirichlet (Icc 0 1) x} =
      Icc (0 : ℝ) 1 := by
    ext x
    exact ⟨And.left, fun hx => ⟨hx, discontinuous_everywhere x hx⟩⟩
  rw [heq] at hnull
  change (volume : Measure ℝ) (Icc (0 : ℝ) 1) = 0 at hnull
  rw [Real.volume_Icc] at hnull
  norm_num at hnull

theorem representative_failure :
    Specs.D11.Ch16.LebesgueNotRiemann.representative_failure := by
  refine ⟨ae_restrict_of_ae ae_zero, ?_,
    not_riemann_integrable⟩
  apply (D11.Ch16.RiemannCriterion.riemann_criterion (fun _ => 0) 0 1
    (by norm_num) ?_).mpr
  · have heq : {x : ℝ | x ∈ Icc (0 : ℝ) 1 ∧
        ¬ ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Icc 0 1) x} = ∅ := by
      ext x
      simp [continuousWithinAt_const]
    rw [heq]
    exact measure_empty
  · constructor <;> refine ⟨0, ?_⟩ <;> rintro _ ⟨x, hx, rfl⟩ <;> exact le_rfl

end D11.Ch16.LebesgueNotRiemann
