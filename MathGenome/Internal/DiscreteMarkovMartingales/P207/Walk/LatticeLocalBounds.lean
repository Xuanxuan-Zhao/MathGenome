import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.LatticeLocalBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open scoped BigOperators
open Set

namespace P207.Walk.LatticeLocalBounds

noncomputable section

theorem angle_cos_le_one (t : Real.Angle) : Real.Angle.cos t ≤ 1 := by
  rw [← Real.Angle.cos_toReal]
  exact Real.cos_le_one _

theorem neg_one_le_angle_cos (t : Real.Angle) : -1 ≤ Real.Angle.cos t := by
  rw [← Real.Angle.cos_toReal]
  exact Real.neg_one_le_cos _

theorem angle_cos_eq_one (t : Real.Angle) : Real.Angle.cos t = 1 ↔ t = 0 := by
  simpa using (Real.Angle.cos_eq_iff_eq_or_eq_neg (θ := t) (ψ := 0))

theorem angle_cos_eq_neg_one (t : Real.Angle) :
    Real.Angle.cos t = -1 ↔ t = (Real.pi : Real.Angle) := by
  simpa using (Real.Angle.cos_eq_iff_eq_or_eq_neg
    (θ := t) (ψ := (Real.pi : Real.Angle)))

theorem phi_zero (d : ℕ) [NeZero d] : phi (0 : Torus d) = 1 := by
  have hc : Real.Angle.cos (0 : AddCircle (2 * Real.pi)) = 1 := Real.Angle.cos_zero
  simp [phi, hc, NeZero.ne d]

theorem phi_pi (d : ℕ) [NeZero d] : phi (piPoint d) = -1 := by
  have hc : Real.Angle.cos (Real.pi : AddCircle (2 * Real.pi)) = -1 :=
    Real.Angle.cos_coe_pi
  simp [phi, piPoint, hc, NeZero.ne d]

theorem phi_eq_one_iff {d : ℕ} [NeZero d] (t : Torus d) :
    phi t = 1 ↔ t = 0 := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  constructor
  · intro h
    have hs : ∑ j : Fin d, (1 - Real.Angle.cos (t j)) = 0 := by
      simp only [phi] at h
      have hh : ∑ j : Fin d, Real.Angle.cos (t j) = d := by
        calc
          _ = (d : ℝ) * ((d : ℝ)⁻¹ * ∑ j : Fin d, Real.Angle.cos (t j)) := by
            field_simp
          _ = d := by rw [h, mul_one]
      simp [Finset.sum_sub_distrib, hh]
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) =>
        sub_nonneg.mpr (angle_cos_le_one (t j)))).mp hs
    funext j
    exact (angle_cos_eq_one _).mp (by linarith [hj j (Finset.mem_univ j)])
  · rintro rfl
    exact phi_zero d

theorem phi_eq_neg_one_iff {d : ℕ} [NeZero d] (t : Torus d) :
    phi t = -1 ↔ t = piPoint d := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  constructor
  · intro h
    have hs : ∑ j : Fin d, (Real.Angle.cos (t j) + 1) = 0 := by
      simp only [phi] at h
      have hh : ∑ j : Fin d, Real.Angle.cos (t j) = -(d : ℝ) := by
        calc
          _ = (d : ℝ) * ((d : ℝ)⁻¹ * ∑ j : Fin d, Real.Angle.cos (t j)) := by
            field_simp
          _ = -(d : ℝ) := by rw [h]; ring
      simp [Finset.sum_add_distrib, hh]
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) =>
        show 0 ≤ Real.Angle.cos (t j) + 1 by
          linarith [neg_one_le_angle_cos (t j)])).mp hs
    funext j
    exact (angle_cos_eq_neg_one _).mp (by linarith [hj j (Finset.mem_univ j)])
  · rintro rfl
    exact phi_pi d

theorem peaks : LatticeLocalBoundsSpec.peaks := by
  intro d _ t
  rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1), phi_eq_one_iff, phi_eq_neg_one_iff]

/-- Angular product chart, translated to the specified center. -/
def angularChart {d : ℕ} (center : Torus d) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin d)) (Torus d) :=
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  ((PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).transOpenPartialHomeomorph
    (OpenPartialHomeomorph.pi (fun _ : Fin d =>
      AddCircle.openPartialHomeomorphCoe (2 * Real.pi) (-Real.pi)))).transHomeomorph
    (Homeomorph.addLeft center)

theorem angularChart_apply {d : ℕ} (center : Torus d)
    (u : EuclideanSpace ℝ (Fin d)) : angularChart center u = angularLift center u := rfl

theorem angularChart_zero {d : ℕ} (center : Torus d) : angularChart center 0 = center := by
  ext j
  change center j + ((0 : ℝ) : AddCircle (2 * Real.pi)) = center j
  simp

theorem angularChart_mem_source {d : ℕ} (center : Torus d)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ < Real.pi) :
    u ∈ (angularChart center).source := by
  change ∀ j ∈ (Set.univ : Set (Fin d)), u j ∈ Set.Ioo (-Real.pi) (-Real.pi + 2 * Real.pi)
  intro j _
  have hj : |u j| < Real.pi := by
    exact (show |u j| ≤ ‖u‖ from PiLp.norm_apply_le u j).trans_lt hu
  have := abs_lt.mp hj
  constructor <;> linarith

theorem cos_angular_coe (s : ℝ) :
    Real.Angle.cos (s : AddCircle (2 * Real.pi)) = Real.cos s :=
  Real.Angle.cos_coe s

/-- Exact sum of the scalar cosine defects in Euclidean coordinates. -/
theorem defect_sum {d : ℕ} [NeZero d] (u : EuclideanSpace ℝ (Fin d)) :
    1 - phi (angularLift 0 u) =
      (d : ℝ)⁻¹ * ∑ j : Fin d, (1 - Real.cos (u j)) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simp only [phi, P207.Walk.angularLift, Pi.zero_apply, zero_add, cos_angular_coe,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, mul_sub]
  field_simp

theorem phi_pi_translate {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) :
    phi (angularLift (P207.Walk.piPoint d) u) = -phi (angularLift 0 u) := by
  have hc (s : ℝ) :
      Real.Angle.cos ((Real.pi : AddCircle (2 * Real.pi)) + (s : AddCircle (2 * Real.pi))) =
        -Real.cos s := by
    change Real.Angle.cos ((Real.pi : Real.Angle) + (s : Real.Angle)) = -Real.cos s
    rw [add_comm, Real.Angle.cos_add_pi, Real.Angle.cos_coe]
  simp only [phi, P207.Walk.angularLift, P207.Walk.piPoint, Pi.zero_apply, zero_add,
    hc, cos_angular_coe, Finset.sum_neg_distrib, mul_neg]


/-- Summing the scalar quadratic estimates gives the Euclidean squared norm. -/
theorem quadratic_defect {d : ℕ} [NeZero d] (u : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ ≤ Real.pi) :
    ((d : ℝ)⁻¹ * (2 / Real.pi ^ 2)) * ‖u‖ ^ 2 ≤ 1 - phi (angularLift 0 u) ∧
    1 - phi (angularLift 0 u) ≤ ((d : ℝ)⁻¹ * (1 / 2)) * ‖u‖ ^ 2 := by
  have hd : 0 ≤ (d : ℝ)⁻¹ := by positivity
  have hlo : ∑ j : Fin d, (2 / Real.pi ^ 2) * (u j) ^ 2 ≤
      ∑ j : Fin d, (1 - Real.cos (u j)) := by
    apply Finset.sum_le_sum
    intro j _
    have hj : |u j| ≤ Real.pi := (PiLp.norm_apply_le u j).trans hu
    linarith [Real.cos_le_one_sub_mul_cos_sq hj]
  have hhi : ∑ j : Fin d, (1 - Real.cos (u j)) ≤
      ∑ j : Fin d, (1 / 2 : ℝ) * (u j) ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    linarith [Real.one_sub_sq_div_two_le_cos (x := u j)]
  rw [defect_sum]
  constructor
  · calc
      _ = (d : ℝ)⁻¹ * ∑ j : Fin d, (2 / Real.pi ^ 2) * (u j) ^ 2 := by
        rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hd
  · calc
      _ ≤ (d : ℝ)⁻¹ * ∑ j : Fin d, (1 / 2 : ℝ) * (u j) ^ 2 :=
        mul_le_mul_of_nonneg_left hhi hd
      _ = _ := by
        rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
        ring

theorem phi_angular_nonneg {d : ℕ} (u : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ ≤ 1) : 0 ≤ phi (angularLift 0 u) := by
  apply mul_nonneg (by positivity : 0 ≤ (d : ℝ)⁻¹)
  apply Finset.sum_nonneg
  intro j _
  change 0 ≤ Real.Angle.cos ((0 : AddCircle (2 * Real.pi)) + (u j : AddCircle (2 * Real.pi)))
  rw [zero_add, cos_angular_coe]
  have hj : |u j| ≤ 1 := (PiLp.norm_apply_le u j).trans hu
  have hs : (u j) ^ 2 ≤ 1 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (u j)) hj 2
    simpa only [sq_abs, one_pow] using hh
  linarith [Real.one_sub_sq_div_two_le_cos (x := u j)]

theorem local_quadratic : LatticeLocalBoundsSpec.local_quadratic := by
  intro d _ center hcenter
  let η : ℝ := min 1 (Real.pi / 2)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηpi : η < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  refine ⟨angularChart center, (d : ℝ)⁻¹ * (2 / Real.pi ^ 2),
    (d : ℝ)⁻¹ * (1 / 2), η, by positivity, by positivity, hη,
    angularChart_apply center, angularChart_zero center, ?_, ?_⟩
  · intro u hu
    have hu' : ‖u‖ ≤ η := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
    exact angularChart_mem_source center u (hu'.trans_lt hηpi)
  · intro u hu
    have hb := quadratic_defect u (hu.trans hηpi.le)
    have hp : 0 ≤ phi (angularLift 0 u) := phi_angular_nonneg u (hu.trans (min_le_left _ _))
    rw [angularChart_apply]
    rcases hcenter with rfl | rfl
    · rwa [abs_of_nonneg hp]
    · rwa [phi_pi_translate, abs_neg, abs_of_nonneg hp]


abbrev piPoint : LatticeLocalBoundsSpec.piPointType := P207.Walk.piPoint
abbrev angularLift : LatticeLocalBoundsSpec.angularLiftType := @P207.Walk.angularLift

end
end P207.Walk.LatticeLocalBounds
