import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.FatCantor
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Tactic.Ring

noncomputable section

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace D11.Ch03.FatCantor

/-- The coordinate unit interval is closed in the Euclidean real line. -/
theorem isClosed_unitBox :
    IsClosed (closedBox (fun _ : Fin 1 => 0) (fun _ => 1)) := by
  change IsClosed {x : Point 1 | ∀ j, 0 ≤ x j ∧ x j ≤ 1}
  simp only [ofPred_forall, ofPred_and]
  exact isClosed_iInter fun j =>
    (isClosed_le continuous_const (EuclideanSpace.proj j).continuous).inter
      (isClosed_le (EuclideanSpace.proj j).continuous continuous_const)

/-- Native volume of the coordinate unit interval is one, by the previously
proved agreement with the box-covering construction. -/
theorem volume_unitBox :
    volume (closedBox (fun _ : Fin 1 => 0) (fun _ => 1)) = 1 := by
  have h := OuterVolume.closedBox_volume 1 (fun _ => 0) (fun _ => 1)
  rw [← LebesgueMeasures.native_outer_agreement] at h
  simpa [boxContent] using h

/-- A small open neighborhood of a countable dense set leaves a closed
nowhere-dense part of the unit interval of mass greater than any α < 1. -/
theorem precursor_properties (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    let K := Specs.D11.Ch03.FatCantor.precursor α hα1
    K ⊆ closedBox (fun _ => 0) (fun _ => 1) ∧
      IsClosed K ∧ IsNowhereDense K ∧ ENNReal.ofReal α < volume K := by
  let D := Specs.D11.Ch03.FatCantor.denseSet
  have hDd : Dense D := (Classical.choose_spec
    (TopologicalSpace.exists_countable_dense (Point 1))).2
  let U := Specs.D11.Ch03.FatCantor.smallOpen α hα1
  obtain ⟨hDU, hUo, hUm⟩ := Classical.choose_spec
    (Specs.D11.Ch03.FatCantor.smallOpen_exists α hα1)
  let B : Set (Point 1) := closedBox (fun _ => 0) (fun _ => 1)
  let K := B \ U
  have hKc : IsClosed K := isClosed_unitBox.sdiff hUo
  have hKn : IsNowhereDense K :=
    ((isClosed_compl_and_isNowhereDense_compl.mpr ⟨hUo, hDd.mono hDU⟩).2).mono
      (sdiff_subset_compl B U)
  refine ⟨sdiff_subset, hKc, hKn, ?_⟩
  have hsum : volume K + volume (B ∩ U) = 1 := by
    exact (measure_sdiff_add_inter B hUo.measurableSet).trans volume_unitBox
  have hiU : volume (B ∩ U) < ENNReal.ofReal (1 - α) :=
    (measure_mono inter_subset_right).trans_lt hUm
  by_contra h
  have hKle : volume K ≤ ENNReal.ofReal α := le_of_not_gt h
  have hlt := ENNReal.add_lt_add_of_le_of_lt
    (lt_of_le_of_lt hKle ENNReal.ofReal_lt_top).ne hKle hiU
  rw [hsum, ← ENNReal.ofReal_add hα.le (sub_pos.mpr hα1).le] at hlt
  have heq : α + (1 - α) = 1 := by ring
  simp only [heq, ENNReal.ofReal_one, lt_self_iff_false] at hlt

/-- The prescribed-mass set, given by removing the chosen dense open
neighborhood and contracting the remainder toward zero. -/
def fatCantor : Specs.D11.Ch03.FatCantor.fatCantor_type := fun α _ hα1 =>
  (α / (volume (Specs.D11.Ch03.FatCantor.precursor α hα1)).toReal) •
    Specs.D11.Ch03.FatCantor.precursor α hα1

/-- Prescribed positive mass in a closed nowhere-dense subset of [0,1].
The final rescaling is by a positive number smaller than one. -/
theorem fatCantor_properties : Specs.D11.Ch03.FatCantor.fatCantor_properties := by
  intro α hα hα1
  let K := Specs.D11.Ch03.FatCantor.precursor α hα1
  obtain ⟨hKB, hKc, hKn, hKm⟩ := precursor_properties α hα hα1
  have hKfin : volume K ≠ ∞ :=
    (lt_of_le_of_lt ((measure_mono hKB).trans_eq volume_unitBox) (by simp)).ne
  have hKpos : volume K ≠ 0 :=
    ((ENNReal.ofReal_pos.mpr hα).trans hKm).ne'
  let m := (volume K).toReal
  have hm : 0 < m := ENNReal.toReal_pos hKpos hKfin
  have hαm : α < m := (ENNReal.ofReal_lt_iff_lt_toReal hα.le hKfin).mp hKm
  let r := α / m
  have hr : 0 < r := div_pos hα hm
  have hr1 : r ≤ 1 := (div_le_one hm).mpr hαm.le
  have hCc : IsClosed (r • K) := hKc.smul_of_ne_zero hr.ne'
  have hCn : IsNowhereDense (r • K) := by
    unfold IsNowhereDense at *
    rw [closure_smul₀' hr.ne', interior_smul₀ hr.ne', hKn, smul_set_empty]
  have hCB : r • K ⊆ closedBox (fun _ => 0) (fun _ => 1) := by
    rintro y ⟨x, hx, rfl⟩ j
    have hj := hKB hx j
    change 0 ≤ x j ∧ x j ≤ 1 at hj
    change 0 ≤ r * x j ∧ r * x j ≤ 1
    exact ⟨mul_nonneg hr.le hj.1,
      (mul_le_mul_of_nonneg_left hj.2 hr.le).trans (by simpa using hr1)⟩
  have hCv : volume (r • K) = ENNReal.ofReal α := by
    rw [Measure.addHaar_smul_of_nonneg volume hr.le]
    simp only [Point, finrank_euclideanSpace_fin, pow_one]
    rw [ENNReal.ofReal_div_of_pos hm, ENNReal.ofReal_toReal hKfin]
    exact ENNReal.div_mul_cancel hKpos hKfin
  have hCm : MeasurableSet[LebesgueMeasures.lebesgueSpace 1] (r • K) :=
    LebesgueMeasures.native_borel_le 1 _ hCc.measurableSet
  refine ⟨hCB, hCc, hCn, hCm, ?_⟩
  exact (LebesgueMeasures.lebesgue_apply 1 _ hCm).trans
    ((LebesgueMeasures.native_outer_agreement 1 _).symm.trans hCv)

theorem exists_fatCantor : Specs.D11.Ch03.FatCantor.exists_fatCantor := by
  intro α hα hα1
  exact ⟨fatCantor α hα hα1, fatCantor_properties α hα hα1⟩

end D11.Ch03.FatCantor
