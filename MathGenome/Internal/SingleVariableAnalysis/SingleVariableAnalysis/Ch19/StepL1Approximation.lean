import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.StepL1Approximation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.StepComparison
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order

/-! Integral approximation by finite scalar steps. Closed-cell oscillations
control the error on open cells; Step.open_bound_upperIntegral removes any
restriction on node values. Thus the proof applies to all Darboux integrable
functions, including functions which are not regulated. -/
namespace SingleVariableAnalysis.Riemann
open scoped BigOperators

/-- Subtraction preserves the existing proper Darboux integrability predicate. -/
theorem RealIntegrable.sub {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b) :
    RealIntegrable (fun x => f x - g x) a b := by
  obtain ⟨hn, _⟩ := real_mul_value hg (-1)
  obtain ⟨hs, _⟩ := real_add_value hf hn
  simpa only [neg_one_mul, ← sub_eq_add_neg] using hs

/-- The complex subtraction assertion is componentwise, with real inputs. -/
theorem ComplexIntegrable.sub {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (hg : ComplexIntegrable g a b) :
    ComplexIntegrable (fun x => f x - g x) a b :=
  ⟨RealIntegrable.sub hf.1 hg.1, RealIntegrable.sub hf.2 hg.2⟩

/-- An error measured from the infimum of a closed cell is bounded by that
cell's oscillation; the infimum need not be an attained value. -/
theorem abs_sub_cellInfimum_le (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (i : Fin P.n) {x : ℝ} (hx : x ∈ cell P i) :
    |f x - cellInfimum f P hf i| ≤
      cellSupremum f P hf i - cellInfimum f P hf i := by
  rw [abs_of_nonneg (sub_nonneg.mpr (cellInfimum_le f P hf i hx))]
  exact sub_le_sub_right (le_cellSupremum f P hf i hx) _

/-- The weighted oscillations are precisely the Darboux gap. -/
theorem sum_cell_oscillation (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) :
    (∑ i : Fin P.n, (cellSupremum f P hf i - cellInfimum f P hf i) *
      cellLength P i) = upperSum f P hf - lowerSum f P hf := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  rfl

/-- For a fixed partition, use its lower cell bounds as constants, and any
prescribed finite node values. The error integral is at most the gap. -/
theorem real_step_error_le_gap (f : ℝ → ℝ) {a b : ℝ}
    (hf : RealIntegrable f a b) (P : Partition a b) (v : Fin (P.n + 1) → ℝ) :
    let s : Step.StepData a b := ⟨P, cellInfimum f P hf.bounded, v⟩
    ∃ he : RealIntegrable (fun x => ‖f x - Step.value s x‖) a b,
      realIntegral _ he ≤ upperSum f P hf.bounded - lowerSum f P hf.bounded := by
  dsimp only
  let s : Step.StepData a b := ⟨P, cellInfimum f P hf.bounded, v⟩
  obtain ⟨hs, _⟩ := Step.step_integrable s hf.ordered
  have he := (hf.sub hs).norm
  refine ⟨he, ?_⟩
  change realIntegral (fun x => ‖f x - Step.value s x‖) he ≤ _
  apply ((realIntegral_common_value _ he hf.ordered he.bounded).2).trans_le
  apply (Step.open_bound_upperIntegral _ P hf.ordered he.bounded
    (fun i => cellSupremum f P hf.bounded i - cellInfimum f P hf.bounded i) ?_).trans_eq
    (sum_cell_oscillation f P hf.bounded)
  intro i x hx
  rw [Step.value_on_open s i x hx, Real.norm_eq_abs]
  exact abs_sub_cellInfimum_le f P hf.bounded i ⟨hx.1.le, hx.2.le⟩

/-- Real version, with arbitrary node choices after the approximating open-cell
constants have been fixed. The inclusive criterion handles a = b as well. -/
theorem real_step_l1_approximation :
    Specs.SingleVariableAnalysis.Ch19.StepL1Approximation.realStepL1Approximation := by
  intro f a b hf ε hε
  change RealIntegrable f a b at hf
  obtain ⟨P, hP⟩ := (realIntegrable_iff_small_gap f hf.ordered hf.bounded).mp hf ε hε
  refine ⟨P, cellInfimum f P hf.bounded, fun v => ?_⟩
  let s : Step.StepData a b := ⟨P, cellInfimum f P hf.bounded, v⟩
  obtain ⟨hs, _⟩ := Step.step_integrable s hf.ordered
  obtain ⟨he, hIe⟩ := real_step_error_le_gap f hf P v
  exact ⟨Step.value s, Step.value_on_open s, Step.value_on_node s, hs, he,
    hIe.trans_lt hP⟩

/-- Complex version: refine the two small-gap partitions together and add the
component oscillations. All nodes can be assigned arbitrary complex values. -/
theorem complex_step_l1_approximation :
    Specs.SingleVariableAnalysis.Ch19.StepL1Approximation.complexStepL1Approximation := by
  intro f a b hf ε hε
  have hab := RealIntegrable.ordered hf.1
  let fr : ℝ → ℝ := fun x => (f x).re
  let fi : ℝ → ℝ := fun x => (f x).im
  have hr : RealIntegrable fr a b := hf.1
  have hi : RealIntegrable fi a b := hf.2
  obtain ⟨P, hP⟩ := (realIntegrable_iff_small_gap fr hab hr.bounded).mp hr
    (ε / 2) (half_pos hε)
  obtain ⟨Q, hQ⟩ := (realIntegrable_iff_small_gap fi hab hi.bounded).mp hi
    (ε / 2) (half_pos hε)
  obtain ⟨R, _, hRP, hRQ⟩ := common_refinement P Q
  have hgap :
      (upperSum fr R hr.bounded - lowerSum fr R hr.bounded) +
      (upperSum fi R hi.bounded - lowerSum fi R hi.bounded) < ε := by
    have hru := upper_refinement fr P R hr.bounded hRP
    have hrl := lower_refinement fr P R hr.bounded hRP
    have hiu := upper_refinement fi Q R hi.bounded hRQ
    have hil := lower_refinement fi Q R hi.bounded hRQ
    linarith
  let cr := cellInfimum fr R hr.bounded
  let ci := cellInfimum fi R hi.bounded
  refine ⟨R, fun i => ⟨cr i, ci i⟩, fun v => ?_⟩
  let sr : Step.StepData a b := ⟨R, cr, fun j => (v j).re⟩
  let si : Step.StepData a b := ⟨R, ci, fun j => (v j).im⟩
  let s : ℝ → ℂ := fun x => ⟨Step.value sr x, Step.value si x⟩
  have hopen (i : Fin R.n) (x : ℝ)
      (hx : x ∈ Set.Ioo (R.point i.castSucc) (R.point i.succ)) :
      s x = ⟨cr i, ci i⟩ := by
    apply Complex.ext
    · exact Step.value_on_open sr i x hx
    · exact Step.value_on_open si i x hx
  have hnode (j : Fin (R.n + 1)) : s (R.point j) = v j := by
    apply Complex.ext
    · exact Step.value_on_node sr j
    · exact Step.value_on_node si j
  obtain ⟨hsr, _⟩ := Step.step_integrable sr hab
  obtain ⟨hsi, _⟩ := Step.step_integrable si hab
  have hs : ComplexIntegrable s a b := ⟨hsr, hsi⟩
  have he := (ComplexIntegrable.sub hf hs).norm
  refine ⟨s, hopen, hnode, hs, he, ?_⟩
  have herr : realIntegral _ he ≤
      (upperSum fr R hr.bounded - lowerSum fr R hr.bounded) +
      (upperSum fi R hi.bounded - lowerSum fi R hi.bounded) := by
    apply ((realIntegral_common_value _ he hab he.bounded).2).trans_le
    have hbound := Step.open_bound_upperIntegral _ R hab he.bounded
      (fun i => (cellSupremum fr R hr.bounded i - cellInfimum fr R hr.bounded i) +
        (cellSupremum fi R hi.bounded i - cellInfimum fi R hi.bounded i)) ?_
    · apply hbound.trans_eq
      simp only [add_mul, Finset.sum_add_distrib, sum_cell_oscillation]
    · intro i x hx
      calc
        ‖f x - s x‖ ≤ |fr x - cr i| + |fi x - ci i| := by
          simpa only [hopen i x hx, Complex.sub_re, Complex.sub_im] using
            Complex.norm_le_abs_re_add_abs_im (f x - s x)
        _ ≤ _ := add_le_add
          (abs_sub_cellInfimum_le fr R hr.bounded i ⟨hx.1.le, hx.2.le⟩)
          (abs_sub_cellInfimum_le fi R hi.bounded i ⟨hx.1.le, hx.2.le⟩)
  exact herr.trans_lt hgap

end SingleVariableAnalysis.Riemann
