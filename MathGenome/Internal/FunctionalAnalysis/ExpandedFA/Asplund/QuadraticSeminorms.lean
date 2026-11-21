import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.QuadraticSeminorms
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

universe u

namespace ExpandedFA.Asplund

open QuadraticSeminormsSpec

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Convexity and quadratic homogeneity give the weighted sum estimate. -/
theorem quadratic_weighted_sum {q : E → ℝ} (hq : NonnegativeQuadraticConvex q)
    (x y : E) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    q (x + y) ≤ q x / t + q y / (1 - t) := by
  have hs : 0 < 1 - t := sub_pos.mpr ht1
  have h := hq.2.1.2 (Set.mem_univ (t⁻¹ • x))
    (Set.mem_univ ((1 - t)⁻¹ • y)) ht.le hs.le (by ring : t + (1 - t) = 1)
  rw [smul_inv_smul₀ ht.ne', smul_inv_smul₀ hs.ne'] at h
  simp only [hq.2.2, smul_eq_mul] at h
  convert h using 1
  field_simp

/-- Apply the sum estimate to `x+y` and `x-y`. -/
theorem quadratic_weighted_difference {q : E → ℝ} (hq : NonnegativeQuadraticConvex q)
    (x y : E) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    4 * q x ≤ q (x + y) / t + q (x - y) / (1 - t) := by
  have h := quadratic_weighted_sum hq (x + y) (x - y) ht ht1
  rw [show (x + y) + (x - y) = (2 : ℝ) • x by simp [two_smul],
    hq.2.2] at h
  norm_num at h
  exact h

/-- Positive upper bounds for the square roots yield an upper bound for the sum.
Using positive bounds avoids imposing nonvanishing on the values of `q`. -/
private theorem sqrt_add_le_of_bounds {q : E → ℝ} (hq : NonnegativeQuadraticConvex q)
    (x y : E) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hx : q x ≤ A ^ 2) (hy : q y ≤ B ^ 2) :
    Real.sqrt (q (x + y)) ≤ A + B := by
  have hAB : 0 < A + B := add_pos hA hB
  have ht : 0 < A / (A + B) := div_pos hA hAB
  have ht1 : A / (A + B) < 1 := (div_lt_one hAB).2 (by linarith)
  have hcomp : 1 - A / (A + B) = B / (A + B) := by
    field_simp
    ring
  have h := quadratic_weighted_sum hq x y ht ht1
  have hsum : q (x + y) ≤ A ^ 2 / (A / (A + B)) + B ^ 2 / (B / (A + B)) := by
    rw [hcomp] at h
    exact h.trans (add_le_add (div_le_div_of_nonneg_right hx ht.le)
      (div_le_div_of_nonneg_right hy (div_pos hB hAB).le))
  have heq : A ^ 2 / (A / (A + B)) + B ^ 2 / (B / (A + B)) = (A + B) ^ 2 := by
    field_simp
  exact Real.sqrt_le_iff.mpr ⟨hAB.le, heq ▸ hsum⟩

/-- The square root is subadditive even when one or both values vanish. -/
theorem quadratic_sqrt_add_le {q : E → ℝ} (hq : NonnegativeQuadraticConvex q)
    (x y : E) : Real.sqrt (q (x + y)) ≤ Real.sqrt (q x) + Real.sqrt (q y) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hx := Real.sq_sqrt (hq.1 x)
  have hy := Real.sq_sqrt (hq.1 y)
  have hx0 := Real.sqrt_nonneg (q x)
  have hy0 := Real.sqrt_nonneg (q y)
  have hA : 0 < Real.sqrt (q x) + ε / 2 := by positivity
  have hB : 0 < Real.sqrt (q y) + ε / 2 := by positivity
  have hxA : q x ≤ (Real.sqrt (q x) + ε / 2) ^ 2 := by nlinarith
  have hyB : q y ≤ (Real.sqrt (q y) + ε / 2) ^ 2 := by nlinarith
  have h := sqrt_add_le_of_bounds hq x y hA hB hxA hyB
  linarith

/-- Absolute homogeneity follows by taking square roots. -/
theorem quadratic_sqrt_smul {q : E → ℝ} (hq : NonnegativeQuadraticConvex q)
    (a : ℝ) (x : E) : Real.sqrt (q (a • x)) = ‖a‖ * Real.sqrt (q x) := by
  rw [hq.2.2, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

/-- The seminorm whose square is `q` is its pointwise nonnegative square root. -/
def quadraticSqrtSeminorm {q : E → ℝ} (hq : NonnegativeQuadraticConvex q) : Seminorm ℝ E :=
  Seminorm.of (fun x => Real.sqrt (q x)) (quadratic_sqrt_add_le hq) (quadratic_sqrt_smul hq)

/-- Every square of a seminorm has precisely the required properties. -/
theorem seminorm_square_properties (p : Seminorm ℝ E) :
    NonnegativeQuadraticConvex (fun x => (p x) ^ 2) := by
  refine ⟨fun x => sq_nonneg _, ?_, ?_⟩
  · exact p.convexOn.pow (fun x _ => apply_nonneg p x) 2
  · intro a x
    dsimp only
    rw [map_smul_eq_mul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Squares of seminorms are exactly the finite nonnegative convex
quadratically homogeneous functions. -/
theorem square_seminorm_characterization : SquareSeminormCharacterization.{u} := by
  intro E _ _ q
  constructor
  · intro hq
    exact ⟨quadraticSqrtSeminorm hq, fun x => (Real.sq_sqrt (hq.1 x)).symm⟩
  · rintro ⟨p, hp⟩
    have heq : q = fun x => (p x) ^ 2 := funext hp
    rw [heq]
    exact seminorm_square_properties p

theorem weighted_sum_estimate : WeightedSumEstimate.{u} := by
  intro E _ _ q hq x y t ht ht1
  exact quadratic_weighted_sum hq x y ht ht1

theorem weighted_difference_estimate : WeightedDifferenceEstimate.{u} := by
  intro E _ _ q hq x y t ht ht1
  exact quadratic_weighted_difference hq x y ht ht1

section StrictConvexity

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The sphere midpoint condition supplies the standard strict-convex-space
instance; the library implication also holds on the zero space. -/
private theorem strictConvexSpace_of_unitSphere (h : UnitSphereStrictConvex (E := F)) :
    StrictConvexSpace ℝ F := by
  apply StrictConvexSpace.of_norm_combo_lt_one
  intro x y hx hy hxy
  refine ⟨1 / 2, 1 / 2, by norm_num, ?_⟩
  simpa only [← smul_add] using h x y hx hy hxy

/-- The scalar square Jensen gap, with both coefficients retained. -/
private theorem square_jensen_gap (r s a b : ℝ) (hab : a + b = 1) :
    a * r ^ 2 + b * s ^ 2 - (a * r + b * s) ^ 2 = a * b * (r - s) ^ 2 := by
  have hb : b = 1 - a := by linarith
  rw [hb]
  ring

/-- Rotundity implies strict convexity of the squared norm. -/
theorem strictConvexOn_sq_norm_of_unitSphere
    (h : UnitSphereStrictConvex (E := F)) :
    StrictConvexOn ℝ Set.univ (fun x : F => ‖x‖ ^ 2) := by
  let : StrictConvexSpace ℝ F := strictConvexSpace_of_unitSphere h
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  simp only [smul_eq_mul]
  have hnorm : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc
      _ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, norm_smul, Real.norm_of_nonneg ha.le,
        Real.norm_of_nonneg hb.le]
  have hrhs : 0 ≤ a * ‖x‖ + b * ‖y‖ := by positivity
  by_cases heq : ‖x‖ = ‖y‖
  · have hlt : ‖a • x + b • y‖ < ‖x‖ :=
      norm_combo_lt_of_ne le_rfl heq.ge hxy ha hb hab
    have hsq : ‖a • x + b • y‖ ^ 2 < ‖x‖ ^ 2 := by
      nlinarith [norm_nonneg (a • x + b • y)]
    have heq' : a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← heq, ← add_mul, hab, one_mul]
    linarith
  · have hsq : ‖a • x + b • y‖ ^ 2 ≤ (a * ‖x‖ + b * ‖y‖) ^ 2 := by
      nlinarith [norm_nonneg (a • x + b • y)]
    have hgap : 0 < a * b * (‖x‖ - ‖y‖) ^ 2 :=
      mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr heq))
    have hident := square_jensen_gap ‖x‖ ‖y‖ a b hab
    linarith

/-- Restrict strict convexity of the squared norm to distinct unit vectors. -/
theorem unitSphere_of_strictConvexOn_sq_norm
    (h : StrictConvexOn ℝ Set.univ (fun x : F => ‖x‖ ^ 2)) :
    UnitSphereStrictConvex (E := F) := by
  intro x y hx hy hxy
  have hlt := h.2 (Set.mem_univ x) (Set.mem_univ y) hxy
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [← smul_add] at hlt
  simp only [hx, hy, one_pow, smul_eq_mul] at hlt
  nlinarith [norm_nonneg ((1 / 2 : ℝ) • (x + y))]

end StrictConvexity

/-- Strict convexity in the paper's unit-sphere sense is equivalent to
strict convexity of the squared norm, including the zero space. -/
theorem strict_convex_square_equivalence : StrictConvexSquareEquivalence.{u} := by
  intro E _ _
  exact ⟨strictConvexOn_sq_norm_of_unitSphere, unitSphere_of_strictConvexOn_sq_norm⟩

end ExpandedFA.Asplund
