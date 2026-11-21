import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.PellUnits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace P203.Ch06.PellUnits
open P203Specs.Ch06.PellUnits

/-- The actual integer-pair ring, reusing the shared canonical definition. -/
abbrev IntegralOrder : IntegralOrderType := IntegralQuadratic

theorem coefficient_formulas : CoefficientFormulas := by
  intro D x y
  refine ⟨rfl, rfl, ?_⟩
  simp only [P203Specs.Ch06.PellUnits.norm, Zsqrtd.norm_def]
  ring

theorem real_model : RealModel := by
  intro D hD hns
  have hi : Function.Injective (realEmbedding D hD) :=
    Zsqrtd.lift_injective _ (fun n hn => hns ⟨n, hn⟩)
  refine ⟨hi, fun _ => rfl, ?_⟩
  ext r
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.re, z.im, rfl⟩
  · rintro ⟨x, y, rfl⟩
    exact ⟨⟨x, y⟩, rfl⟩

theorem norm_laws : NormLaws := by
  intro D hD z w
  refine ⟨?_, Zsqrtd.norm_mul _ _, ?_⟩
  · simp only [conjugate, star_mul, mul_comm]
  · have h := congrArg (realEmbedding D hD) (Zsqrtd.norm_eq_mul_conj z)
    simpa only [map_intCast, map_mul, realEmbedding, Zsqrtd.lift_apply_apply,
      realValue, conjugate, P203Specs.Ch06.PellUnits.norm] using h

theorem unit_criterion : UnitCriterion := by
  intro D z
  exact (Zsqrtd.isUnit_iff_norm_isUnit z).trans Int.isUnit_iff

theorem signed_inverse : SignedInverse := by
  intro D z ε hε hn
  have he : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have h : z * ((ε : IntegralQuadratic D) * conjugate z) = 1 := by
    calc
      _ = (ε : IntegralQuadratic D) * (z * star z) := by unfold conjugate; ring
      _ = (ε : IntegralQuadratic D) * (norm z : ℤ) := by
        rw [P203Specs.Ch06.PellUnits.norm, Zsqrtd.norm_eq_mul_conj]
      _ = 1 := by rw [hn, ← Int.cast_mul, he, Int.cast_one]
  exact ⟨h, by simpa only [mul_comm] using h⟩

theorem units_inverse : UnitsInverse := by
  intro D u
  have hsign := (unit_criterion D (u : IntegralQuadratic D)).mp u.isUnit
  have hinv := (signed_inverse D (u : IntegralQuadratic D) _ hsign rfl).1
  exact Units.inv_eq_of_mul_eq_one_right hinv

theorem unit_coordinates : UnitCoordinates := by
  intro D hD z ε hε hn
  have hs : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  have hp : realValue D z * realValue D (conjugate z) = (ε : ℝ) := by
    rw [← (norm_laws D hD z z).2.2, hn]
  have he : (ε : ℝ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hu : realValue D z ≠ 0 := by intro hz; rw [hz, zero_mul] at hp; exact he hp.symm
  have hv : (ε : ℝ) / realValue D z = realValue D (conjugate z) := by
    apply (div_eq_iff hu).mpr
    linarith [hp]
  refine ⟨hu, ?_, ?_⟩
  · rw [hv]
    simp only [realValue, conjugate, Zsqrtd.re_star, Zsqrtd.im_star, Int.cast_neg]
    ring
  · rw [hv]
    apply (eq_div_iff (ne_of_gt (mul_pos (by norm_num) hs))).mpr
    simp only [realValue, conjugate, Zsqrtd.re_star, Zsqrtd.im_star, Int.cast_neg]
    ring

theorem positive_coordinates : PositiveCoordinates := by
  intro D hD z hz
  have hn := (unit_criterion D z).mp hz
  have hs : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  have hp := (norm_laws D hD z z).2.2
  have hx : realValue D z + realValue D (conjugate z) = 2 * (z.re : ℝ) := by
    simp only [realValue, conjugate, Zsqrtd.re_star, Zsqrtd.im_star, Int.cast_neg]
    ring
  have hy : realValue D z - realValue D (conjugate z) = 2 * (z.im : ℝ) * Real.sqrt (D : ℝ) := by
    simp only [realValue, conjugate, Zsqrtd.re_star, Zsqrtd.im_star, Int.cast_neg]
    ring
  constructor
  · intro hu
    have hv : -1 < realValue D (conjugate z) ∧ realValue D (conjugate z) < 1 := by
      rcases hn with hn | hn <;> rw [hn] at hp <;> norm_num at hp
      · constructor <;> nlinarith
      · constructor <;> nlinarith
    have hxr : (0 : ℝ) < z.re := by linarith
    have hyr : (0 : ℝ) < z.im := by nlinarith [mul_pos hs (show (0 : ℝ) < 2 by norm_num)]
    exact ⟨by exact_mod_cast hxr, by exact_mod_cast hyr⟩
  · rintro ⟨hxz, hyz⟩
    have hx1 : (1 : ℝ) ≤ z.re := by exact_mod_cast hxz
    have hy1 : (0 : ℝ) < z.im := by exact_mod_cast hyz
    dsimp [realValue]
    nlinarith [mul_pos hy1 hs]

theorem pell_correspondence : PellCorrespondence := by
  intro D
  constructor
  · intro a
    exact Zsqrtd.norm_eq_one_iff_mem_unitary.mpr a.property
  · intro z hz
    refine ⟨⟨z, Zsqrtd.norm_eq_one_iff_mem_unitary.mp hz⟩, rfl, ?_⟩
    intro a ha
    exact Subtype.ext ha

theorem pell_multiplication : PellMultiplication := by
  intro D hD a b
  refine ⟨rfl, Pell.Solution₁.x_mul a b, Pell.Solution₁.y_mul a b, ?_⟩
  exact (realEmbedding D hD).map_mul _ _

end P203.Ch06.PellUnits
