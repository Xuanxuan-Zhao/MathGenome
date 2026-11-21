import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.DiscreteDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.IntervalFixedPoint
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-! Fixed points and geometric convergence for self-maps of a closed real interval. -/

namespace D13Unified.Ch15.IntervalFixedPoint

open Filter Set
open scoped Topology
open D13Unified.Ch15.DiscreteDefinitions

/-- Apply the intermediate value theorem to the map and the identity on the interval. -/
theorem exists_fixedPoint (a b : ℝ) (hab : a < b)
    (F : Icc a b → Icc a b) (hF : Continuous F) :
    ∃ p : Icc a b, F p = p := by
  let : PreconnectedSpace (Icc a b) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  let left : Icc a b := ⟨a, le_rfl, hab.le⟩
  let right : Icc a b := ⟨b, hab.le, le_rfl⟩
  obtain ⟨p, hp⟩ := intermediate_value_univ₂
    (a := right) (b := left)
    (continuous_subtype_val.comp hF) continuous_subtype_val
    (F right).property.2 (F left).property.1
  exact ⟨p, Subtype.ext hp⟩

/-- Uniqueness and the sharp geometric estimate, with convergence for every initial point. -/
theorem contraction_fixedPoint (a b : ℝ) (hab : a < b)
    (F : Icc a b → Icc a b) (hF : Continuous F)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hLip : ∀ x y : Icc a b,
      |(F x : ℝ) - (F y : ℝ)| ≤ q * |(x : ℝ) - (y : ℝ)|) :
    ∃ p : Icc a b, F p = p ∧
      (∀ y : Icc a b, F y = y → y = p) ∧
      (∀ x : Icc a b, Tendsto (forwardOrbit F x) atTop (𝓝 p)) ∧
      (∀ (x : Icc a b) (n : ℕ),
        |((iterate F n x : Icc a b) : ℝ) - (p : ℝ)| ≤ q ^ n * |(x : ℝ) - (p : ℝ)|) := by
  obtain ⟨p, hp⟩ := exists_fixedPoint a b hab F hF
  have hbound (x : Icc a b) (n : ℕ) :
      |((iterate F n x : Icc a b) : ℝ) - (p : ℝ)| ≤ q ^ n * |(x : ℝ) - (p : ℝ)| := by
    induction n with
    | zero => simp [iterate_zero]
    | succ n ih =>
      calc
        |((iterate F (n + 1) x : Icc a b) : ℝ) - (p : ℝ)| =
            |(F (iterate F n x) : ℝ) - (F p : ℝ)| := by
              rw [iterate_succ, Function.comp_apply, hp]
        _ ≤ q * |((iterate F n x : Icc a b) : ℝ) - (p : ℝ)| := hLip _ _
        _ ≤ q * (q ^ n * |(x : ℝ) - (p : ℝ)|) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * |(x : ℝ) - (p : ℝ)| := by
          simp only [pow_succ]
          ac_rfl
  refine ⟨p, hp, ?_, ?_, hbound⟩
  · intro y hy
    have h := hLip y p
    rw [hy, hp] at h
    have hz : |(y : ℝ) - (p : ℝ)| = 0 := by
      nlinarith [abs_nonneg ((y : ℝ) - (p : ℝ))]
    exact Subtype.ext (sub_eq_zero.mp (abs_eq_zero.mp hz))
  · intro x
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hlimit : Tendsto (fun n : ℕ => q ^ n * |(x : ℝ) - (p : ℝ)|)
        atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const
        |(x : ℝ) - (p : ℝ)|
    apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hlimit
    simpa only [Subtype.dist_eq, Real.dist_eq, forwardOrbit, iterate,
      Specs.D13Unified.Ch15.DiscreteDefinitions.forwardOrbit,
      Specs.D13Unified.Ch15.DiscreteDefinitions.iterate] using hbound x n

end D13Unified.Ch15.IntervalFixedPoint
