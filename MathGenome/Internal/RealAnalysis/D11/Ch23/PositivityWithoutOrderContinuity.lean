import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.PositivityWithoutOrderContinuity
import MathGenome.Internal.RealAnalysis.D11.Ch23.OrderContinuityNecessary
import Mathlib.Tactic.Linarith

open Filter Topology MeasureTheory
open scoped NNReal

noncomputable section

namespace D11.Ch23.PositivityWithoutOrderContinuity

open _root_.Specs.D11.Ch23.PositivityWithoutOrderContinuity

lemma tendsto_limitValue (f : limitSpace) :
    Tendsto (f : ℝ≥0 → ℝ) atTop (𝓝 (limitValue f)) :=
  Classical.choose_spec f.property.2

lemma limitValue_eq (f : limitSpace) {a : ℝ}
    (ha : Tendsto (f : ℝ≥0 → ℝ) atTop (𝓝 a)) : limitValue f = a :=
  tendsto_nhds_unique (tendsto_limitValue f) ha

theorem lattice_stone : _root_.Specs.D11.Ch23.PositivityWithoutOrderContinuity.lattice_stone := by
  constructor
  · constructor
    · rintro f ⟨hf, a, ha⟩ g ⟨hg, b, hb⟩
      exact ⟨hf.min hg, min a b, ha.min hb⟩
    · rintro f ⟨hf, a, ha⟩ g ⟨hg, b, hb⟩
      exact ⟨hf.max hg, max a b, ha.max hb⟩
  · rintro f ⟨hf, a, ha⟩
    exact ⟨hf.min continuous_const, min a 1, ha.min tendsto_const_nhds⟩

theorem positive_linear : _root_.Specs.D11.Ch23.PositivityWithoutOrderContinuity.positive_linear := by
  let L : limitSpace →ₗ[ℝ] ℝ :=
    { toFun := limitValue
      map_add' := fun f g => limitValue_eq (f + g)
        ((tendsto_limitValue f).add (tendsto_limitValue g))
      map_smul' := fun c f => limitValue_eq (c • f)
        (tendsto_const_nhds.mul (tendsto_limitValue f)) }
  refine ⟨L, fun _ => rfl, tendsto_limitValue, ?_⟩
  intro f hf
  exact ge_of_tendsto (tendsto_limitValue f) (Eventually.of_forall hf)

theorem ramp_zero (n : ℕ) (x : ℝ≥0) (h : (x : ℝ) ≤ n) : ramp n x = 0 := by
  simp [ramp, max_eq_right (sub_nonpos.mpr h)]

theorem ramp_middle (n : ℕ) (x : ℝ≥0)
    (h : (n : ℝ) ≤ x) (h' : (x : ℝ) ≤ n + 1) : ramp n x = (x : ℝ) - n := by
  rw [ramp, max_eq_left (sub_nonneg.mpr h), min_eq_left (by linarith)]

theorem ramp_one (n : ℕ) (x : ℝ≥0) (h : (n : ℝ) + 1 ≤ x) : ramp n x = 1 := by
  rw [ramp, min_eq_right]
  exact le_trans (by linarith : (1 : ℝ) ≤ (x : ℝ) - n) (le_max_left _ _)

lemma ramp_at_infinity (n : ℕ) : Tendsto (ramp n) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ((n : ℝ≥0) + 1)] with x hx
  exact (ramp_one n x (by exact_mod_cast hx)).symm

theorem ramp_mem : _root_.Specs.D11.Ch23.PositivityWithoutOrderContinuity.ramp_mem := by
  intro n
  exact ⟨((NNReal.continuous_coe.sub continuous_const).max continuous_const).min
    continuous_const, 1, ramp_at_infinity n⟩

theorem ramp_properties : _root_.Specs.D11.Ch23.PositivityWithoutOrderContinuity.ramp_properties := by
  refine ⟨fun n x => ⟨ramp_zero n x, ramp_middle n x, ramp_one n x⟩, ?_, ?_,
    ramp_at_infinity⟩
  · intro x n m hnm
    exact min_le_min (max_le_max (sub_le_sub_left
      (show (n : ℝ) ≤ m by exact_mod_cast hnm) (x : ℝ)) le_rfl) le_rfl
  · intro x
    obtain ⟨N, hN⟩ := exists_nat_ge (x : ℝ)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (ramp_zero n x (hN.trans (by exact_mod_cast hn))).symm

theorem failure_of_order_continuity :
    _root_.Specs.D11.Ch23.PositivityWithoutOrderContinuity.failure_of_order_continuity := by
  intro L hL
  let f : ℕ → limitSpace := fun n => ⟨ramp n, ramp_mem n⟩
  have hval (n : ℕ) : L (f n) = 1 := by
    rw [hL]
    exact limitValue_eq (f n) (ramp_at_infinity n)
  have hnot : ¬ Tendsto (fun n => L (f n)) atTop (𝓝 0) := by
    intro h
    have hc : Tendsto (fun n => L (f n)) atTop (𝓝 1) := by
      simpa only [hval] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    exact one_ne_zero (tendsto_nhds_unique hc h)
  refine ⟨⟨f, fun _ => rfl, ramp_properties.2.1, ramp_properties.2.2.1, hval, hnot⟩, ?_⟩
  intro h
  exact hnot (h.2 f ramp_properties.2.1 ramp_properties.2.2.1)

theorem no_representation :
    _root_.Specs.D11.Ch23.PositivityWithoutOrderContinuity.no_representation := by
  intro m ⟨μ, hint, hrep⟩
  let : MeasurableSpace ℝ≥0 := m
  obtain ⟨A, hA, hElementary⟩ :=
    OrderContinuityNecessary.order_continuity_necessary limitSpace lattice_stone.1 μ
      limitValue hint hrep
  exact (failure_of_order_continuity A hA).2 hElementary

end D11.Ch23.PositivityWithoutOrderContinuity
