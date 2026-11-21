import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.ClosedConvexNoGap
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The closed convex counterexample after strong separation, paper.tex:1163–1169. -/

namespace ExpandedFA.P1.ClosedConvexNoGap
open Set Filter

@[simp] lemma point_zero (s t : ℝ) : point s t 0 = s := rfl
@[simp] lemma point_one (s t : ℝ) : point s t 1 = t := rfl

lemma point_coordinates (x : Plane) : point (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> rfl

lemma point_decomposition (s t : ℝ) :
    point s t = s • point 1 0 + t • point 0 1 := by
  ext i
  fin_cases i <;> simp [point, PiLp.add_apply, PiLp.smul_apply]

lemma functional_coordinates (h : Plane →L[ℝ] ℝ) (s t : ℝ) :
    h (point s t) = s * h (point 1 0) + t * h (point 0 1) := by
  rw [point_decomposition, map_add, map_smul, map_smul]
  rfl

lemma mem_A_iff (x : Plane) : x ∈ A ↔ 0 ≤ x 0 ∧ 1 ≤ x 0 * x 1 := by
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨hs.le, (div_le_iff₀ hs).mp ht |>.trans_eq (mul_comm _ _)⟩
  · rintro ⟨hs, ht⟩
    have hpos : 0 < x 0 := by
      by_contra hn
      have hz : x 0 = 0 := le_antisymm (le_of_not_gt hn) hs
      norm_num [hz] at ht
    exact ⟨hpos, (div_le_iff₀ hpos).mpr (by nlinarith [ht])⟩

lemma A_nonempty : A.Nonempty := ⟨point 1 1, by norm_num [A]⟩
lemma B_nonempty : B.Nonempty := ⟨point 0 0, rfl⟩

lemma A_disjoint_B : Disjoint A B := by
  apply Set.disjoint_left.mpr
  intro x hx hd
  exact (ne_of_gt hx.1) hd

lemma A_closed : IsClosed A := by
  have h0 : Continuous (fun x : Plane => x 0) := (EuclideanSpace.proj 0).continuous
  have h1 : Continuous (fun x : Plane => x 1) := (EuclideanSpace.proj 1).continuous
  have heq : A = {x : Plane | 0 ≤ x 0} ∩ {x : Plane | 1 ≤ x 0 * x 1} := by
    ext x
    exact mem_A_iff x
  rw [heq]
  exact (isClosed_le continuous_const h0).inter
    (isClosed_le continuous_const (h0.mul h1))

lemma B_closed : IsClosed B :=
  isClosed_eq (EuclideanSpace.proj 0).continuous continuous_const

lemma A_convex : Convex ℝ A := by
  intro x hx y hy a b ha hb hab
  change 0 < (a • x + b • y) 0 ∧ 1 / (a • x + b • y) 0 ≤ (a • x + b • y) 1
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hc : ConvexOn ℝ (Ioi 0) (fun s : ℝ => 1 / s) := by
    simpa only [zpow_neg_one, one_div] using (convexOn_zpow (-1 : ℤ) :
      ConvexOn ℝ (Ioi 0) (fun s : ℝ => s ^ (-1 : ℤ)))
  refine ⟨(convex_Ioi (0 : ℝ) hx.1 hy.1 ha hb hab), ?_⟩
  have hi := hc.2 hx.1 hy.1 ha hb hab
  simp only [smul_eq_mul] at hi
  exact hi.trans (add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
    (mul_le_mul_of_nonneg_left hy.2 hb))

lemma B_convex : Convex ℝ B := by
  intro x hx y hy a b ha hb hab
  change x 0 = 0 at hx
  change y 0 = 0 at hy
  change (a • x + b • y) 0 = 0
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hx, hy, mul_zero, add_zero]

theorem geometry : Spec.geometry_type :=
  ⟨A_nonempty, B_nonempty, A_disjoint_B, A_closed, B_closed, A_convex, B_convex⟩

lemma horizontal_distance (s t : ℝ) : dist (point s t) (point 0 t) = |s| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.sqrt_sq_eq_abs]

lemma arbitrarily_close (ε : ℝ) (hε : 0 < ε) :
    ∃ c ∈ A, ∃ d ∈ B, dist c d < ε := by
  refine ⟨point (ε / 2) (1 / (ε / 2)), ⟨by simpa using half_pos hε, le_rfl⟩,
    point 0 (1 / (ε / 2)), rfl, ?_⟩
  rw [horizontal_distance, abs_of_pos (half_pos hε)]
  linarith

theorem zero_distance : Spec.zero_distance_type := by
  refine ⟨le_antisymm ?_ ?_, arbitrarily_close⟩
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨c, hc, d, hd, hdist⟩ := arbitrarily_close ε hε
    have hb : BddBelow mutualDistances := ⟨0, by
      rintro r ⟨x, hx, y, hy, rfl⟩
      exact dist_nonneg⟩
    simpa using (csInf_le hb (show dist c d ∈ mutualDistances from ⟨c, hc, d, hd, rfl⟩)).trans hdist.le
  · apply le_csInf
    · exact ⟨dist (point 1 1) (point 0 0), point 1 1, by norm_num [A],
        point 0 0, rfl, rfl⟩
    · rintro r ⟨c, hc, d, hd, rfl⟩
      exact dist_nonneg

lemma vertical_coefficient_zero (h : Plane →L[ℝ] ℝ)
    (hb : (∃ M : ℝ, ∀ d ∈ B, h d ≤ M) ∨ (∃ M : ℝ, ∀ d ∈ B, M ≤ h d)) :
    h (point 0 1) = 0 := by
  by_contra hn
  rcases hb with ⟨M, hM⟩ | ⟨M, hM⟩
  · have htest := hM (point 0 ((M + 1) / h (point 0 1))) rfl
    rw [functional_coordinates] at htest
    simp only [zero_mul, zero_add, div_mul_cancel₀ _ hn] at htest
    linarith
  · have htest := hM (point 0 ((M - 1) / h (point 0 1))) rfl
    rw [functional_coordinates] at htest
    simp only [zero_mul, zero_add, div_mul_cancel₀ _ hn] at htest
    linarith

theorem vertical_coefficient : Spec.vertical_coefficient_type := by
  intro h hb
  have hz := vertical_coefficient_zero h hb
  refine ⟨hz, ?_⟩
  intro d hd
  rw [← point_coordinates d, functional_coordinates, hd, hz]
  ring

lemma boundary_mem (s : ℝ) (hs : 0 < s) : point s (1 / s) ∈ A := ⟨hs, le_rfl⟩

theorem approaching_values : Spec.approaching_values_type := by
  intro h hb
  obtain ⟨hz, hB⟩ := vertical_coefficient h hb
  constructor
  · intro n
    have hn : 0 < (n : ℝ) + 1 := by positivity
    refine ⟨by simpa using one_div_pos.mpr hn, ?_⟩
    simp only [point_zero, point_one, one_div_one_div]
    exact le_rfl
  · intro d hd
    have hv := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (h (point 1 0))
    have heq : (fun n : ℕ => h (point (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1))) =
        (fun n : ℕ => (1 / ((n : ℝ) + 1)) * h (point 1 0)) := by
      funext n
      rw [functional_coordinates, hz, mul_zero, add_zero]
    rw [heq, hB d hd]
    simpa only [zero_mul] using hv

theorem no_positive_gap : Spec.no_positive_gap_type := by
  rintro ⟨h, δ, hδ, hgap⟩
  obtain ⟨c, hc, d, hd, hdist⟩ := arbitrarily_close (δ / (‖h‖ + 1)) (by positivity)
  have hg := hgap c hc d hd
  have hn := h.le_opNorm (d - c)
  rw [map_sub, Real.norm_eq_abs, ← dist_eq_norm] at hn
  rw [dist_comm d c] at hn
  have hsmall : ‖h‖ * dist c d < δ := by
    have hmul := (lt_div_iff₀ (show 0 < ‖h‖ + 1 by positivity)).mp hdist
    nlinarith [dist_nonneg (x := c) (y := d)]
  have hlo := le_abs_self (h d - h c)
  linarith

theorem no_positive_gap_reverse : Spec.no_positive_gap_reverse_type := by
  rintro ⟨h, δ, hδ, hgap⟩
  apply no_positive_gap
  refine ⟨-h, δ, hδ, ?_⟩
  intro c hc d hd
  have hg := hgap c hc d hd
  simp only [neg_apply]
  linarith

end ExpandedFA.P1.ClosedConvexNoGap
