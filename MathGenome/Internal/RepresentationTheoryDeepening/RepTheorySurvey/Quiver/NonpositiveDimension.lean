import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.Forms
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.NonpositiveDimension
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Algebra.Ring.Real

/-! The integral witness used in the dimension obstruction to finite representation type. -/

open scoped BigOperators Matrix

namespace RepTheorySurvey.Quiver.NonpositiveDimension

open Forms

universe u v

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)]

private theorem continuous_titsForm : Continuous (titsForm (Q := Q) (R := ℝ)) := by
  change Continuous (FormsSpec.titsForm (Q := Q) (R := ℝ))
  unfold FormsSpec.titsForm FormsSpec.eulerForm
  exact (continuous_finsetSum _ fun i _ =>
    (continuous_apply i).mul (continuous_apply i)).sub
    (continuous_finsetSum _ fun a _ =>
      (continuous_apply a.1).mul (continuous_apply a.2.1))

private theorem exists_rational_negative {x : Q → ℝ} (hx : titsForm x < 0) :
    ∃ y : Q → ℚ, y ≠ 0 ∧ titsForm (fun i => (y i : ℝ)) ≤ 0 := by
  have hdense : DenseRange (fun y : Q → ℚ => fun i => (y i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨y, hy⟩ := hdense.exists_mem_open
    (isOpen_lt continuous_titsForm continuous_const) ⟨x, hx⟩
  change titsForm (fun i => (y i : ℝ)) < 0 at hy
  refine ⟨y, ?_, hy.le⟩
  intro hyzero
  simp [hyzero, FormsSpec.titsForm, FormsSpec.eulerForm] at hy

omit [Fintype Q] [Fintype (RM03.Arrow Q)] in
private theorem rat_map_polarizationMatrix :
    (polarizationMatrix (Q := Q) ℚ).map (Rat.castHom ℝ) = polarizationMatrix ℝ := by
  classical
  ext i j
  by_cases hij : i = j <;> simp [FormsSpec.polarizationMatrix, hij]

private theorem exists_rational_null (hacyclic : ¬ RM03.HasOrientedCycle Q)
    (hnonneg : ∀ x : Q → ℝ, 0 ≤ titsForm x) {x : Q → ℝ}
    (hx : x ≠ 0) (hxq : titsForm x = 0) :
    ∃ y : Q → ℚ, y ≠ 0 ∧ titsForm (fun i => (y i : ℝ)) ≤ 0 := by
  classical
  have hpsd : (polarizationMatrix (Q := Q) ℝ).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · change (polarizationMatrix (Q := Q) ℝ)ᴴ = polarizationMatrix ℝ
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      exact polarizationMatrix_transpose ℝ
    · intro z
      rw [star_trivial, ← real_quadratic_matrix hacyclic z]
      exact mul_nonneg zero_le_two (hnonneg z)
  have hxker : polarizationMatrix ℝ *ᵥ x = 0 := by
    apply hpsd.dotProduct_mulVec_zero_iff.mp
    change FormsSpec.titsForm x = 0 at hxq
    rw [star_trivial, ← real_quadratic_matrix hacyclic x, hxq, mul_zero]
  have hdet : (polarizationMatrix (Q := Q) ℝ).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hxker⟩
  -- The determinant vanishes over ℚ because its image in ℝ vanishes.
  have hdet_rat : (polarizationMatrix (Q := Q) ℚ).det = 0 := by
    apply (Rat.castHom ℝ).injective
    rw [RingHom.map_det]
    change ((polarizationMatrix (Q := Q) ℚ).map (Rat.castHom ℝ)).det = (Rat.castHom ℝ) 0
    rw [rat_map_polarizationMatrix, hdet, map_zero]
  obtain ⟨y, hy, hyker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet_rat
  have hyker_real : polarizationMatrix ℝ *ᵥ (fun i => (y i : ℝ)) = 0 := by
    funext i
    rw [← rat_map_polarizationMatrix]
    change ((polarizationMatrix (Q := Q) ℚ).map (Rat.castHom ℝ) *ᵥ
      ((Rat.castHom ℝ) ∘ y)) i = 0
    rw [← RingHom.map_mulVec, hyker, Pi.zero_apply, map_zero]
  refine ⟨y, hy, ?_⟩
  have hquad := real_quadratic_matrix hacyclic (fun i => (y i : ℝ))
  rw [hyker_real, dotProduct_zero] at hquad
  exact ((mul_eq_zero.mp hquad).resolve_left two_ne_zero).le

private theorem titsForm_scale (c : ℝ) (x : Q → ℝ) :
    titsForm (fun i => c * x i) = (c * c) * titsForm x := by
  simp only [FormsSpec.titsForm, FormsSpec.eulerForm]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem exists_integral_nonpositive {y : Q → ℚ} (hy : y ≠ 0)
    (hyq : titsForm (fun i => (y i : ℝ)) ≤ 0) :
    ∃ d : DimensionVector Q, d ≠ 0 ∧ titsForm d ≤ 0 := by
  -- A one-column matrix gives a common denominator for all coordinates.
  let column : Matrix Q Unit ℚ := Matrix.of (fun i _ => y i)
  let d : DimensionVector Q := fun i => column.num i ()
  have hden : (column.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr column.den_ne_zero
  have hscale (i : Q) : (d i : ℝ) = (column.den : ℝ) * (y i : ℝ) := by
    have h := column.num_div_den i ()
    change (d i : ℚ) / column.den = y i at h
    have hmul : (d i : ℚ) = (column.den : ℚ) * y i :=
      ((div_eq_iff (Nat.cast_ne_zero.mpr column.den_ne_zero)).mp h).trans (mul_comm _ _)
    exact_mod_cast hmul
  refine ⟨d, ?_, ?_⟩
  · intro hd
    apply hy
    funext i
    have h := hscale i
    rw [hd, Pi.zero_apply, Int.cast_zero] at h
    exact Rat.cast_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hden)
  · have hq : titsForm (fun i => (d i : ℝ)) ≤ 0 := by
      rw [funext hscale, titsForm_scale]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) hyq
    change FormsSpec.titsForm (fun i => (d i : ℝ)) ≤ 0 at hq
    rw [real_titsForm_intCast d] at hq
    exact_mod_cast hq

private theorem titsForm_abs_le (d : DimensionVector Q) :
    titsForm (fun i => |d i|) ≤ titsForm d := by
  simp only [FormsSpec.titsForm, FormsSpec.eulerForm, abs_mul_abs_self]
  apply sub_le_sub_left
  exact Finset.sum_le_sum fun a _ => by
    rw [← abs_mul]
    exact le_abs_self _

/-- A Tits form that fails real positive definiteness has a nonpositive value
on a nonzero nonnegative integral dimension vector. -/
theorem exists_nonpositive_dimension :
    NonpositiveDimensionSpec.ExistsNonpositiveDimension.{u, v} := by
  classical
  intro Q _ _ _ hacyclic hpositive
  have hrat : ∃ y : Q → ℚ, y ≠ 0 ∧ titsForm (fun i => (y i : ℝ)) ≤ 0 := by
    by_cases h : ∃ x : Q → ℝ, titsForm x < 0
    · obtain ⟨x, hx⟩ := h
      exact exists_rational_negative hx
    · have hnonneg (x : Q → ℝ) : 0 ≤ titsForm x := le_of_not_gt (fun hx => h ⟨x, hx⟩)
      change ¬ ∀ x : Q → ℝ, x ≠ 0 → 0 < titsForm x at hpositive
      push Not at hpositive
      obtain ⟨x, hx, hxq⟩ := hpositive
      exact exists_rational_null hacyclic hnonneg hx (le_antisymm hxq (hnonneg x))
  obtain ⟨y, hy, hyq⟩ := hrat
  obtain ⟨d, hd, hdq⟩ := exists_integral_nonpositive hy hyq
  refine ⟨fun i => |d i|, ?_, fun i => abs_nonneg _, (titsForm_abs_le d).trans hdq⟩
  intro habs
  apply hd
  funext i
  exact abs_eq_zero.mp (congrFun habs i)

end RepTheorySurvey.Quiver.NonpositiveDimension
