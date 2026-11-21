import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.LeraySchauder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24CompactMap
import Mathlib.Analysis.Normed.Module.Convex

/-! Compact-image fixed points and compact-homotopy continuation,
`fa2:p1:leray-schauder`, paper.tex:5657–5702. The auxiliary map uses
radial retraction in the vector coordinate and clipped feedback in time. -/

noncomputable section

open Set Metric
open scoped Topology

namespace ExpandedFA.P1.LeraySchauder

universe u

theorem compact_image_fixed_point : Spec.CompactImageFixedPoint.{u} :=
  C24CompactMap.banachCompactMap

section Radial

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial retraction, expressed without division by zero at the origin. -/
def radialRetraction (M : ℝ) (y : E) : E := (M / max M ‖y‖) • y

theorem continuous_radialRetraction {M : ℝ} (hM : 0 < M) :
    Continuous (radialRetraction M : E → E) := by
  apply Continuous.smul _ continuous_id
  exact continuous_const.div (continuous_const.max continuous_norm)
    (fun y => ne_of_gt (lt_of_lt_of_le hM (le_max_left _ _)))

theorem norm_radialRetraction_le {M : ℝ} (hM : 0 < M) (y : E) :
    ‖radialRetraction M y‖ ≤ M := by
  rw [radialRetraction, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hM.le (le_trans hM.le (le_max_left _ _)))]
  calc
    _ ≤ (M / max M ‖y‖) * max M ‖y‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    _ = M := div_mul_cancel₀ _ (ne_of_gt (hM.trans_le (le_max_left _ _)))

theorem radialRetraction_eq_self {M : ℝ} (hM : 0 < M) {y : E} (hy : ‖y‖ ≤ M) :
    radialRetraction M y = y := by
  simp [radialRetraction, max_eq_left hy, ne_of_gt hM]

theorem radialRetraction_eq_of_norm_lt {M : ℝ} (hM : 0 < M) {x y : E}
    (hxy : radialRetraction M y = x) (hx : ‖x‖ < M) : y = x := by
  by_cases hy : ‖y‖ ≤ M
  · rwa [radialRetraction_eq_self hM hy] at hxy
  · have hny : 0 < ‖y‖ := lt_trans hM (lt_of_not_ge hy)
    have hn : ‖radialRetraction M y‖ = M := by
      rw [radialRetraction, norm_smul, Real.norm_eq_abs,
        max_eq_right (le_of_not_ge hy), abs_of_pos (div_pos hM hny),
        div_mul_cancel₀ _ (ne_of_gt hny)]
    rw [hxy] at hn
    exact False.elim (hx.ne hn)

end Radial

section Continuation

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scalar feedback coordinate in the continuation construction. -/
def feedback (R : ℝ) (x : E) (t : ℝ) : ℝ := max 0 (min 1 (t + R - ‖x‖))

omit [NormedSpace ℝ E] in
theorem feedback_mem (R : ℝ) (x : E) (t : ℝ) :
    feedback R x t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

omit [NormedSpace ℝ E] in
theorem continuous_feedback (R : ℝ) :
    Continuous (fun p : E × ℝ => feedback R p.1 p.2) := by
  exact continuous_const.max (continuous_const.min
    ((continuous_snd.add continuous_const).sub (continuous_norm.comp continuous_fst)))

/-- A fixed point of the clipped auxiliary map must occur at time one.
This is the algebraic part of the compact-homotopy argument. -/
theorem auxiliary_fixed_point_time
    (F : E × Icc (0 : ℝ) 1 → E) {R M : ℝ} (hR : 0 < R) (hRM : R < M)
    (hzero : ∀ x, F (x, ⟨0, by constructor <;> norm_num⟩) = 0)
    (hbound : ∀ x t, F (x, t) = x → ‖x‖ < R)
    (x : E) (t : Icc (0 : ℝ) 1)
    (hx : radialRetraction M (F (x, t)) = x)
    (ht : feedback R x t = (t : ℝ)) :
    (t : ℝ) = 1 ∧ F (x, t) = x := by
  have hM : 0 < M := hR.trans hRM
  have htz : (t : ℝ) ≠ 0 := by
    intro hz
    have hteq : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext hz
    have hx0 : x = 0 := by
      simpa [hteq, hzero, radialRetraction] using hx.symm
    have hp : 0 < feedback R x t := by
      rw [hx0, feedback, norm_zero, hz, zero_add, sub_zero]
      exact lt_max_of_lt_right (lt_min (by norm_num) hR)
    rw [ht, hz] at hp
    exact lt_irrefl _ hp
  have ht1 : (t : ℝ) = 1 := by
    by_contra hn
    have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 hn
    have hnorm : ‖x‖ = R := by
      unfold feedback at ht
      have hmin : min 1 ((t : ℝ) + R - ‖x‖) = (t : ℝ) := by
        rcases max_eq_iff.mp ht with h | h
        · exact False.elim (htz h.1.symm)
        · exact h.1
      have heq : (t : ℝ) + R - ‖x‖ = (t : ℝ) := by
        rcases le_total 1 ((t : ℝ) + R - ‖x‖) with h | h
        · rw [min_eq_left h] at hmin
          linarith
        · rwa [min_eq_right h] at hmin
      linarith
    have heq := radialRetraction_eq_of_norm_lt hM hx (hnorm ▸ hRM)
    have hb := hbound x t heq
    linarith
  refine ⟨ht1, radialRetraction_eq_of_norm_lt hM hx ?_⟩
  have hn : ‖x‖ ≤ R := by
    by_contra hn
    have ha : (t : ℝ) + R - ‖x‖ < 1 := by linarith
    have hm : max 0 (min 1 ((t : ℝ) + R - ‖x‖)) < 1 :=
      max_lt (by norm_num) (lt_of_le_of_lt (min_le_right _ _) ha)
    change feedback R x t < 1 at hm
    rw [ht, ht1] at hm
    exact lt_irrefl _ hm
  exact hn.trans_lt hRM

end Continuation

/-- Compact-homotopy continuation, first over the underlying real space. -/
theorem real_compact_homotopy_continuation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E × Icc (0 : ℝ) 1 → E) (hF : Continuous F)
    (hcompact : ∀ B : Set (E × Icc (0 : ℝ) 1), Bornology.IsBounded B →
      IsCompact (closure (F '' B)))
    (hzero : ∀ x, F (x, ⟨0, by constructor <;> norm_num⟩) = 0)
    (R : ℝ) (hR : 0 < R)
    (hbound : ∀ x t, F (x, t) = x → ‖x‖ < R) :
    ∃ x, F (x, ⟨1, by constructor <;> norm_num⟩) = x := by
  let M := R + 1
  have hRM : R < M := by dsimp [M]; linarith
  have hM : 0 < M := hR.trans hRM
  let D : Set (E × ℝ) := closedBall (0 : E) M ×ˢ Icc (0 : ℝ) 1
  let q : D → E × Icc (0 : ℝ) 1 := fun p => (p.val.1, ⟨p.val.2, p.property.2⟩)
  have hq : Continuous q :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  let H : D → D := fun p =>
    ⟨(radialRetraction M (F (q p)), feedback R p.val.1 p.val.2),
      by
        constructor
        · simpa only [mem_closedBall, dist_zero_right] using
            norm_radialRetraction_le hM (F (q p))
        · exact feedback_mem _ _ _⟩
  have hH : Continuous H := by
    apply Continuous.subtype_mk
    exact ((continuous_radialRetraction hM).comp (hF.comp hq)).prodMk
      ((continuous_feedback R).comp continuous_subtype_val)
  let B : Set (E × Icc (0 : ℝ) 1) := closedBall (0 : E) M ×ˢ univ
  have hB : Bornology.IsBounded B :=
    isBounded_closedBall.prod (isCompact_univ : IsCompact (univ : Set (Icc (0 : ℝ) 1))).isBounded
  have hK := (hcompact B hB).image (continuous_radialRetraction hM)
  have hL := hK.prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  have hHrange : range (fun p : D => (H p : E × ℝ)) ⊆
      (radialRetraction M '' closure (F '' B)) ×ˢ Icc (0 : ℝ) 1 := by
    rintro _ ⟨p, rfl⟩
    constructor
    · refine ⟨F (q p), subset_closure ?_, rfl⟩
      exact mem_image_of_mem F ⟨p.property.1, mem_univ _⟩
    · exact feedback_mem _ _ _
  have hHcompact : IsCompact (closure (range (fun p : D => (H p : E × ℝ)))) :=
    hL.of_isClosed_subset isClosed_closure (closure_minimal hHrange hL.isClosed)
  have hDne : D.Nonempty := ⟨(0, 0), by simp [D, hM.le]⟩
  have hDclosed : IsClosed D := isClosed_closedBall.prod isClosed_Icc
  have hDconvex : Convex ℝ D := (convex_closedBall _ _).prod (convex_Icc _ _)
  obtain ⟨p, hp⟩ := C24CompactMap.realNormedCompactMap
    D hDne hDclosed hDconvex H hH hHcompact
  have hval := congrArg Subtype.val hp
  have hx : radialRetraction M (F (q p)) = p.val.1 := congrArg Prod.fst hval
  have ht : feedback R p.val.1 p.val.2 = p.val.2 := congrArg Prod.snd hval
  obtain ⟨ht1, hfix⟩ := auxiliary_fixed_point_time F hR hRM hzero hbound
    p.val.1 (q p).2 hx ht
  refine ⟨p.val.1, ?_⟩
  have heq : (q p).2 = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext ht1
  change F (p.val.1, (q p).2) = p.val.1 at hfix
  rwa [heq] at hfix

theorem compact_homotopy_continuation : Spec.CompactHomotopyContinuation.{u} := by
  intro 𝕜 E _ _ _ _ F hF hcompact hzero hbound
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨R, hR, hb⟩ := hbound
  exact real_compact_homotopy_continuation F hF hcompact hzero R hR hb

theorem bounded_solution_set_fixed_point : Spec.BoundedSolutionSetFixedPoint.{u} := by
  intro 𝕜 E _ _ _ _
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro T hT hcompact hbounded
  let F : E × Icc (0 : ℝ) 1 → E := fun p => (p.2 : ℝ) • T p.1
  have hF : Continuous F :=
    (continuous_subtype_val.comp continuous_snd).smul (hT.comp continuous_fst)
  have hFc : ∀ B : Set (E × Icc (0 : ℝ) 1), Bornology.IsBounded B →
      IsCompact (closure (F '' B)) := by
    intro B hB
    have hK := hcompact (Prod.fst '' B) hB.image_fst
    have hL := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod hK
    have hS := hL.image (continuous_fst.smul continuous_snd :
      Continuous (fun p : ℝ × E => p.1 • p.2))
    apply hS.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hS.isClosed
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨((p.2 : ℝ), T p.1), ⟨p.2.property, ?_⟩, rfl⟩
    exact subset_closure (mem_image_of_mem T (mem_image_of_mem Prod.fst hp))
  obtain ⟨R, hR, hb⟩ := hbounded.exists_pos_norm_lt
  obtain ⟨x, hx⟩ := real_compact_homotopy_continuation F hF hFc
    (fun x => by simp [F]) R hR (by
      intro x t ht
      exact hb x ⟨t, t.property, ht.symm⟩)
  exact ⟨x, by simpa [F] using hx⟩

end ExpandedFA.P1.LeraySchauder
