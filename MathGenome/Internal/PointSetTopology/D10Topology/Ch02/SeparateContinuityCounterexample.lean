import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.SeparateContinuityCounterexample
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The separately continuous function of paper.tex, d10:02:cautions. -/

namespace D10Topology.Ch02

noncomputable def separateContinuityMap : ℝ × ℝ → ℝ :=
  Specs.D10Topology.Ch02.SeparateContinuityCounterexample.exampleMap

/-- Totalized field division already gives the prescribed value at the origin. -/
theorem separateContinuityMap_eq_quotient (p : ℝ × ℝ) :
    separateContinuityMap p = p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2) := by
  unfold separateContinuityMap
    Specs.D10Topology.Ch02.SeparateContinuityCounterexample.exampleMap
  split_ifs with hp
  · subst p; norm_num
  · rfl

theorem separateContinuityMap_at_origin : separateContinuityMap (0, 0) = 0 := by
  simp [separateContinuityMap_eq_quotient]

theorem separateContinuityMap_off_origin (p : ℝ × ℝ) (_hp : p ≠ (0, 0)) :
    separateContinuityMap p = p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2) :=
  separateContinuityMap_eq_quotient p

theorem separateContinuityMap_horizontal_zero (x : ℝ) :
    separateContinuityMap (x, 0) = 0 := by
  simp [separateContinuityMap_eq_quotient]

theorem separateContinuityMap_vertical_zero (y : ℝ) :
    separateContinuityMap (0, y) = 0 := by
  simp [separateContinuityMap_eq_quotient]

theorem separateContinuityMap_horizontal_continuous (y : ℝ) :
    Continuous (fun x : ℝ => separateContinuityMap (x, y)) := by
  by_cases hy : y = 0
  · subst y
    simpa only [separateContinuityMap_horizontal_zero] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  · simp only [separateContinuityMap_eq_quotient]
    apply (continuous_id.mul continuous_const).div
      ((continuous_id.pow 2).add continuous_const)
    intro x
    exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hy))

theorem separateContinuityMap_vertical_continuous (x : ℝ) :
    Continuous (fun y : ℝ => separateContinuityMap (x, y)) := by
  by_cases hx : x = 0
  · subst x
    simpa only [separateContinuityMap_vertical_zero] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  · simp only [separateContinuityMap_eq_quotient]
    apply (continuous_const.mul continuous_id).div
      (continuous_const.add (continuous_id.pow 2))
    intro y
    exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y))

theorem separateContinuityMap_diagonal_value (t : ℝ) (ht : t ≠ 0) :
    separateContinuityMap (t, t) = 1 / 2 := by
  rw [separateContinuityMap_eq_quotient]
  dsimp
  have hd : t ^ 2 + t ^ 2 ≠ 0 := ne_of_gt (add_pos (sq_pos_of_ne_zero ht)
    (sq_pos_of_ne_zero ht))
  field_simp
  nlinarith

/-- A hypothetical continuous map would have continuous diagonal restriction.
The epsilon 1/4 test contradicts its constant value 1/2 off the origin. -/
theorem separateContinuityMap_not_continuousAt_origin :
    ¬ ContinuousAt separateContinuityMap (0, 0) := by
  intro hc
  have hg : ContinuousAt (fun t : ℝ => separateContinuityMap (t, t)) 0 :=
    hc.comp (f := fun t : ℝ => (t, t)) (continuousAt_id.prodMk continuousAt_id)
  obtain ⟨δ, hδ, hbound⟩ := (Metric.continuousAt_iff.mp hg) (1 / 4) (by norm_num)
  have ht : δ / 2 ≠ 0 := ne_of_gt (half_pos hδ)
  have hdist : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith
  have hb := hbound hdist
  rw [separateContinuityMap_diagonal_value _ ht,
    separateContinuityMap_at_origin, Real.dist_eq] at hb
  norm_num at hb

theorem separateContinuityMap_not_continuous : ¬ Continuous separateContinuityMap := by
  intro hc
  exact separateContinuityMap_not_continuousAt_origin hc.continuousAt

end D10Topology.Ch02
