import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.HilbertBallIntersection
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Finite ball intersection for Kirszbraun–Valentine (paper.tex:13007–13026).

For weights w in the finite simplex, maximize
  F(w) = ∑ i, w i (‖y i‖² - r i²) - ‖∑ i, w i • y i‖².
The variance identity and the pairwise contraction bound give F(w) ≤ 0.
At a maximizer, the one-sided variation toward each simplex vertex gives
  ‖p - y i‖² - r i² ≤ F(w),  p = ∑ i, w i • y i.
Thus p belongs to every ball. Compactness is needed only for the simplex,
so the real helper even applies to incomplete inner-product spaces.
Real restriction preserves the given norms and proves the complex case.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
open Finset
namespace ExpandedFA.Geometry.HilbertBallIntersection
universe u v w z t

/-- The weighted variance identity for a finite family. -/
lemma weighted_variance {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : ι → ℝ) (v : ι → E) (hw : ∑ i, w i = 1) :
    (∑ i, ∑ j, w i * w j * ‖v i - v j‖ ^ 2) =
      2 * ((∑ i, w i * ‖v i‖ ^ 2) - ‖∑ i, w i • v i‖ ^ 2) := by
  have hi : ‖∑ i, w i • v i‖ ^ 2 =
      ∑ i, ∑ j, w i * w j * ⟪v i, v j⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    congr 1; funext i; congr 1; funext j; ring
  rw [hi]
  simp_rw [norm_sub_sq_real]
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h₁ : (∑ i, ∑ j, w i * w j * ‖v i‖ ^ 2) = ∑ i, w i * ‖v i‖ ^ 2 := by
    simp_rw [mul_right_comm (w _) (w _) (‖v _‖ ^ 2), ← Finset.mul_sum, hw, mul_one]
  have h₂ : (∑ i, ∑ j, w i * w j * ‖v j‖ ^ 2) = ∑ i, w i * ‖v i‖ ^ 2 := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [← Finset.sum_mul, hw, one_mul]
  have h₃ : (∑ i, ∑ j, w i * w j * (2 * ⟪v i, v j⟫_ℝ)) =
      2 * ∑ i, ∑ j, w i * w j * ⟪v i, v j⟫_ℝ := by
    simp_rw [show ∀ i j, w i * w j * (2 * ⟪v i, v j⟫_ℝ) =
      2 * (w i * w j * ⟪v i, v j⟫_ℝ) by intros; ring, ← Finset.mul_sum]
  rw [h₁, h₂, h₃]
  ring

/-- A quadratic with a maximum at the left endpoint has nonpositive
right derivative. This elementary form avoids any differentiability hypothesis. -/
lemma quadratic_coefficient_nonpos {A B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * A ≤ t ^ 2 * B) : A ≤ 0 := by
  by_contra hn
  have hA : 0 < A := lt_of_not_ge hn
  let t := min 1 (A / (2 * (B + 1)))
  have ht : 0 < t := lt_min zero_lt_one (div_pos hA (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htB : t * (2 * (B + 1)) ≤ A :=
    (le_div_iff₀ (by positivity : 0 < 2 * (B + 1))).mp (min_le_right _ _)
  have hh := h t ht.le ht1
  have hh' : A ≤ t * B := by nlinarith
  nlinarith

/-- Maximizing the dual quadratic on the simplex produces a center.
The hypothesis is precisely the weighted variance obstruction. -/
lemma exists_center_of_weighted_bound {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (r : ι → ℝ)
    (hbound : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
      (∑ i, w i * (‖v i‖ ^ 2 - r i ^ 2)) - ‖∑ i, w i • v i‖ ^ 2 ≤ 0) :
    ∃ p : E, ∀ i, ‖p - v i‖ ^ 2 ≤ r i ^ 2 := by
  classical
  let a : ι → ℝ := fun i => ‖v i‖ ^ 2 - r i ^ 2
  let F : (ι → ℝ) → ℝ := fun w =>
    (∑ i, w i * a i) - ‖∑ i, w i • v i‖ ^ 2
  have hc : Continuous F := by unfold F; fun_prop
  obtain ⟨w, hw, hmax⟩ := (isCompact_stdSimplex ℝ ι).exists_isMaxOn
    ⟨Pi.single (Classical.arbitrary ι) 1, single_mem_stdSimplex ℝ _⟩ hc.continuousOn
  let p : E := ∑ j, w j • v j
  let A : ℝ := ∑ j, w j * a j
  have hF : F w ≤ 0 := hbound w hw.1 hw.2
  refine ⟨p, fun i => ?_⟩
  let e : ι → ℝ := Pi.single i 1
  have he : e ∈ stdSimplex ℝ ι := single_mem_stdSimplex ℝ i
  have heA : (∑ j, e j * a j) = a i := by simp [e, Pi.single_apply, ite_mul]
  have hep : (∑ j, e j • v j) = v i := by simp [e]
  have hlin : ∀ t : ℝ,
      (∑ j, ((1 - t) • w + t • e) j * a j) = (1 - t) * A + t * a i := by
    intro t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc,
      Finset.sum_add_distrib, ← Finset.mul_sum, heA]
    rfl
  have hbary : ∀ t : ℝ,
      (∑ j, ((1 - t) • w + t • e) j • v j) = p + t • (v i - p) := by
    intro t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, ← Finset.smul_sum, hep]
    change (1 - t) • p + t • v i = _
    module
  have hd : a i - A - 2 * ⟪p, v i - p⟫_ℝ ≤ 0 := by
    apply quadratic_coefficient_nonpos (sq_nonneg ‖v i - p‖)
    intro t ht ht1
    have hwt := (convex_stdSimplex ℝ ι) hw he (sub_nonneg.mpr ht1) ht (by ring)
    have hm := hmax hwt
    change F ((1 - t) • w + t • e) ≤ F w at hm
    dsimp only [F] at hm
    rw [hlin t, hbary t, norm_add_sq_real, inner_smul_right,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hm
    change (1 - t) * A + t * a i -
      (‖p‖ ^ 2 + 2 * (t * ⟪p, v i - p⟫_ℝ) + (t * ‖v i - p‖) ^ 2) ≤
      A - ‖p‖ ^ 2 at hm
    nlinarith
  have hinner : ⟪p, v i - p⟫_ℝ = ⟪p, v i⟫_ℝ - ‖p‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [hinner] at hd
  change A - ‖p‖ ^ 2 ≤ 0 at hF
  rw [norm_sub_sq_real]
  dsimp only [a] at hd
  linarith

/-- Finite Kirszbraun ball intersection over the real underlying spaces.
In fact completeness of either space is unnecessary for a finite family. -/
theorem finite_ball_intersection_real {ι H₁ H₂ : Type*} [Fintype ι]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (s : ι → H₁) (y : ι → H₂)
    (h : ∀ i j, ‖y i - y j‖ ≤ ‖s i - s j‖) (x : H₁) :
    (⋂ i, Metric.closedBall (y i) ‖s i - x‖).Nonempty := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he =>
    let := he
    exact ⟨0, by simp⟩
  | inr he =>
    let := he
    obtain ⟨p, hp⟩ := exists_center_of_weighted_bound y (fun i => ‖s i - x‖) (by
      intro w hw hw1
      have hv := weighted_variance w y hw1
      have hs := weighted_variance w (fun i => s i - x) hw1
      have hc : (∑ i, ∑ j, w i * w j * ‖y i - y j‖ ^ 2) ≤
          ∑ i, ∑ j, w i * w j * ‖(s i - x) - (s j - x)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw i) (hw j))
        have hij := h i j
        rw [show (s i - x) - (s j - x) = s i - s j by abel]
        nlinarith [norm_nonneg (y i - y j), norm_nonneg (s i - s j)]
      rw [hv, hs] at hc
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      nlinarith [sq_nonneg ‖∑ i, w i • (s i - x)‖])
    refine ⟨p, Set.mem_iInter.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hi := hp i
    nlinarith [norm_nonneg (p - y i), norm_nonneg (s i - x)]

/-- The manuscript's finite ball-intersection assertion, for real or
complex Hilbert spaces in arbitrary dimensions, including the empty family. -/
theorem finite_ball_intersection : Spec.FiniteBallIntersection.{u, v, w, z, t} := by
  intro 𝕜₁ 𝕜₂ H₁ H₂ _ _ _ _ _ _ _ _ ι _ s y h x
  let := InnerProductSpace.rclikeToReal 𝕜₁ H₁
  let := InnerProductSpace.rclikeToReal 𝕜₂ H₂
  exact finite_ball_intersection_real s y h x

end ExpandedFA.Geometry.HilbertBallIntersection
