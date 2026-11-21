import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.NonsigmaFiniteTonelliFailure
import MathGenome.Internal.RealAnalysis.D11.Ch05.NonnegativeIntegral
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! The diagonal counterexample, paper.tex:2846–2863. All sigma-algebras
are ordinary Borel/subtype/product structures, with no completion. -/

open Set MeasureTheory
open scoped ENNReal unitInterval

noncomputable section

namespace D11.Ch08.NonsigmaFiniteTonelliFailure

local notation "I₊" => Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value

private theorem integral_eq_lintegral (μ : Measure Interval) (f : Interval → ℝ≥0∞) :
    I₊ μ f = ∫⁻ x, f x ∂μ :=
  D11.Ch05.NonnegativeIntegral.integral_eq_lintegral μ f

theorem borel_structures : Specs.D11.Ch08.NonsigmaFiniteTonelliFailure.borel_structures := by
  exact ⟨BorelSpace.measurable_eq, BorelSpace.measurable_eq⟩

theorem lebesgue_values : Specs.D11.Ch08.NonsigmaFiniteTonelliFailure.lebesgue_values := by
  exact ⟨fun _ _ => unitInterval.volume_apply, measure_univ, fun _ => measure_singleton _⟩

theorem diagonal_closed : Specs.D11.Ch08.NonsigmaFiniteTonelliFailure.diagonal_closed := by
  exact isClosed_eq continuous_fst continuous_snd

theorem indicator_measurable :
    Specs.D11.Ch08.NonsigmaFiniteTonelliFailure.indicator_measurable := by
  exact measurable_const.indicator diagonal_closed.measurableSet

theorem section_masses : Specs.D11.Ch08.NonsigmaFiniteTonelliFailure.section_masses := by
  constructor
  · intro x
    have h : {y : Interval | (x, y) ∈ intervalDiagonal} = {x} := by
      ext y
      simp [intervalDiagonal, eq_comm]
    exact ⟨h, h ▸ Measure.count_singleton x⟩
  · intro y
    have h : {x : Interval | (x, y) ∈ intervalDiagonal} = {y} := by
      ext x
      rfl
    exact ⟨h, h ▸ measure_singleton y⟩

theorem section_integrals :
    Specs.D11.Ch08.NonsigmaFiniteTonelliFailure.section_integrals := by
  classical
  constructor
  · intro x
    rw [integral_eq_lintegral]
    have h : (fun y => diagonalIndicator (x, y)) =
        ({x} : Set Interval).indicator (fun _ => (1 : ℝ≥0∞)) := by
      ext y
      by_cases hxy : x = y <;>
        simp [diagonalIndicator, intervalDiagonal, Set.indicator, hxy, eq_comm]
    rw [h]
    rw [lintegral_indicator_const (measurableSet_singleton x)]
    simp only [one_mul]
    exact Measure.count_singleton x
  · intro y
    rw [integral_eq_lintegral]
    have h : (fun x => diagonalIndicator (x, y)) =
        ({y} : Set Interval).indicator (fun _ => (1 : ℝ≥0∞)) := by
      ext x
      by_cases hxy : x = y <;>
        simp [diagonalIndicator, intervalDiagonal, Set.indicator, hxy]
    rw [h]
    rw [lintegral_indicator_const (measurableSet_singleton y)]
    simp only [one_mul]
    exact measure_singleton y

theorem iterated_integrals :
    Specs.D11.Ch08.NonsigmaFiniteTonelliFailure.iterated_integrals := by
  constructor
  · simp_rw [section_integrals.1]
    rw [integral_eq_lintegral]
    simp [borelLebesgue]
  · simp_rw [section_integrals.2]
    rw [integral_eq_lintegral]
    simp

theorem finite_counting_iff :
    Specs.D11.Ch08.NonsigmaFiniteTonelliFailure.finite_counting_iff := by
  intro A _
  exact Measure.count_apply_lt_top

theorem not_sigmaFinite :
    Specs.D11.Ch08.NonsigmaFiniteTonelliFailure.not_sigmaFinite := by
  intro hc
  have : SigmaFinite counting := hc
  have hzero : ∀ n : ℕ, borelLebesgue (spanningSets counting n) = 0 := by
    intro n
    exact ((finite_counting_iff _ (measurableSet_spanningSets counting n)).mp
      (measure_spanningSets_lt_top counting n)).measure_zero borelLebesgue
  have h : borelLebesgue univ = 0 := by
    rw [← iUnion_spanningSets counting]
    exact measure_iUnion_null hzero
  exact one_ne_zero (lebesgue_values.2.1.symm.trans h)

theorem iterated_ne : Specs.D11.Ch08.NonsigmaFiniteTonelliFailure.iterated_ne := by
  unfold Specs.D11.Ch08.NonsigmaFiniteTonelliFailure.iterated_ne
  rw [iterated_integrals.1, iterated_integrals.2]
  exact one_ne_zero

end D11.Ch08.NonsigmaFiniteTonelliFailure
