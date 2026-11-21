import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.LogisticTent
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring

noncomputable section
namespace D13Unified.Ch15.LogisticTent

abbrev tentMap : Specs.D13Unified.Ch15.LogisticTent.tentMapType :=
  Specs.D13Unified.Ch15.LogisticTent.tentMap

abbrev coordinate : Specs.D13Unified.Ch15.LogisticTent.coordinateType :=
  Specs.D13Unified.Ch15.LogisticTent.coordinate

abbrev logisticFour : Specs.D13Unified.Ch15.LogisticTent.logisticFourType :=
  Specs.D13Unified.Ch15.LogisticTent.logisticFour

theorem tentBranches : Specs.D13Unified.Ch15.LogisticTent.tentBranches := by
  constructor
  · intro t ht
    exact ite_eq_left ht
  · intro t ht
    change (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) = _
    split_ifs with h <;> linarith

theorem tentContinuous : Specs.D13Unified.Ch15.LogisticTent.tentContinuous := by
  apply Continuous.subtype_mk
  exact (continuous_const.mul continuous_subtype_val).if_le
    (continuous_const.sub (continuous_const.mul continuous_subtype_val))
    continuous_subtype_val continuous_const (by
      intro t ht
      change 2 * (t : ℝ) = 2 - 2 * (t : ℝ)
      linarith)

lemma coordinate_continuous : Continuous coordinate := by
  apply Continuous.subtype_mk
  exact (Real.continuous_sin.comp
    ((continuous_const.mul continuous_subtype_val).div_const 2)).pow 2

theorem coordinateIncreasing : Specs.D13Unified.Ch15.LogisticTent.coordinateIncreasing := by
  intro x y hxy
  change Real.sin (Real.pi * (x : ℝ) / 2) ^ 2 < Real.sin (Real.pi * (y : ℝ) / 2) ^ 2
  have hx0 : 0 ≤ Real.pi * (x : ℝ) / 2 :=
    div_nonneg (mul_nonneg Real.pi_pos.le x.property.1) (by norm_num)
  have hy0 : 0 ≤ Real.pi * (y : ℝ) / 2 :=
    div_nonneg (mul_nonneg Real.pi_pos.le y.property.1) (by norm_num)
  have hx1 : Real.pi * (x : ℝ) / 2 ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos, x.property.2]
  have hy1 : Real.pi * (y : ℝ) / 2 ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos, y.property.2]
  have hs := Real.strictMonoOn_sin
    ⟨by linarith [Real.pi_pos], hx1⟩ ⟨by linarith [Real.pi_pos], hy1⟩
    (show Real.pi * (x : ℝ) / 2 < Real.pi * (y : ℝ) / 2 by
      exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hxy Real.pi_pos) (by norm_num))
  have hn := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos])
  nlinarith

lemma coordinate_surjective : Function.Surjective coordinate := by
  intro y
  let H : ℝ → ℝ := fun t => Real.sin (Real.pi * t / 2) ^ 2
  have hc : Continuous H :=
    (Real.continuous_sin.comp ((continuous_const.mul continuous_id).div_const 2)).pow 2
  have hzero : H 0 = 0 := by simp [H]
  have hone : H 1 = 1 := by simp [H, Real.sin_pi_div_two]
  have hmem : (y : ℝ) ∈ Set.Icc (H 0) (H 1) := by
    simpa only [hzero, hone] using y.property
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    hc.continuousOn hmem
  exact ⟨⟨t, ht⟩, Subtype.ext heq⟩

/-- Compactness turns the explicit continuous bijection into a homeomorphism. -/
def coordinateHomeomorph : Interval ≃ₜ Interval :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective coordinate ⟨coordinateIncreasing.injective, coordinate_surjective⟩)
    coordinate_continuous

lemma logistic_coordinate (t : ℝ) :
    4 * Real.sin (Real.pi * t / 2) ^ 2 * (1 - Real.sin (Real.pi * t / 2) ^ 2) =
      Real.sin (Real.pi * t) ^ 2 := by
  have harg : Real.pi * t = 2 * (Real.pi * t / 2) := by ring
  conv_rhs => rw [harg, Real.sin_two_mul]
  rw [show 1 - Real.sin (Real.pi * t / 2) ^ 2 = Real.cos (Real.pi * t / 2) ^ 2 by
    linarith [Real.sin_sq_add_cos_sq (Real.pi * t / 2)]]
  ring

lemma coordinate_semiconj : Function.Semiconj coordinate tentMap logisticFour := by
  intro t
  apply Subtype.ext
  change Real.sin (Real.pi * (tentMap t : ℝ) / 2) ^ 2 =
    4 * Real.sin (Real.pi * (t : ℝ) / 2) ^ 2 * (1 - Real.sin (Real.pi * (t : ℝ) / 2) ^ 2)
  rw [logistic_coordinate]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [tentBranches.1 t ht]
    congr 2
    ring
  · rw [tentBranches.2 t (by linarith)]
    rw [show Real.pi * (2 - 2 * (t : ℝ)) / 2 = Real.pi - Real.pi * (t : ℝ) by ring,
      Real.sin_pi_sub]

theorem conjugacy : Specs.D13Unified.Ch15.LogisticTent.conjugacy := by
  refine ⟨coordinateHomeomorph, fun _ => rfl, coordinateIncreasing, coordinate_semiconj⟩

end D13Unified.Ch15.LogisticTent
