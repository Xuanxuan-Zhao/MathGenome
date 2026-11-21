import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesBlockObjects
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05RealHahnBanach
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Dual
import Mathlib.Tactic.Linarith

/-! The convex-block objects preceding James's lemma, paper.tex:3540–3557. -/

universe u
namespace ExpandedFA.P1.JamesBlockObjects
open Filter Set

abbrev L : Spec.LType.{u} := Spec.LValue
abbrev V : Spec.VType.{u} := Spec.VValue
noncomputable abbrev normOn : Spec.NormOnType.{u} := Spec.NormOnValue

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A common dual norm bound gives a two-sided scalar bound at every vector. -/
lemma eval_bounds {f : ℕ → E →L[ℝ] ℝ} {C : ℝ} (hC : ∀ n, ‖f n‖ ≤ C)
    (x : E) (n : ℕ) : -(C * ‖x‖) ≤ f n x ∧ f n x ≤ C * ‖x‖ := by
  have h : |f n x| ≤ C * ‖x‖ :=
    (f n).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg x))
  exact abs_le.mp h

lemma eval_bddAbove {f : ℕ → E →L[ℝ] ℝ} (hf : Spec.BoundedSequence f) (x : E) :
    IsBoundedUnder (· ≤ ·) atTop (fun n => f n x) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C * ‖x‖, show ∀ᶠ n : ℕ in atTop, f n x ≤ C * ‖x‖ from
    Eventually.of_forall (fun n => (eval_bounds hC x n).2)⟩

lemma eval_bddBelow {f : ℕ → E →L[ℝ] ℝ} (hf : Spec.BoundedSequence f) (x : E) :
    IsBoundedUnder (· ≥ ·) atTop (fun n => f n x) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨-(C * ‖x‖), show ∀ᶠ n : ℕ in atTop, -(C * ‖x‖) ≤ f n x from
    Eventually.of_forall (fun n => (eval_bounds hC x n).1)⟩

/-- The pointwise limsup is a finite real sublinear function. -/
lemma limsup_sublinear {f : ℕ → E →L[ℝ] ℝ} (hf : Spec.BoundedSequence f) :
    IsSublinear (fun x => limsup (fun n => f n x) atTop) := by
  constructor
  · intro x y
    simpa only [map_add, Pi.add_def] using
      (limsup_add_le (eval_bddBelow hf x) (eval_bddAbove hf x)
        (eval_bddBelow hf y).isCoboundedUnder_le (eval_bddAbove hf y))
  · intro t ht x
    have hm : Monotone (fun a : ℝ => t * a) :=
      fun _ _ hab => mul_le_mul_of_nonneg_left hab ht
    have h := hm.map_limsup_of_continuousAt (fun n => f n x)
      (continuous_const.mul continuous_id).continuousAt
      (eval_bddAbove hf x) (eval_bddBelow hf x).isCoboundedUnder_le
    simpa only [map_smul, smul_eq_mul, Function.comp_def] using h.symm

/-- Hahn–Banach supplies a continuous linear functional dominated by the limsup. -/
theorem L_nonempty : Spec.LNonempty.{u} := by
  intro E _ _ f hf
  obtain ⟨C, hC⟩ := hf
  have hf' : Spec.BoundedSequence f := ⟨C, hC⟩
  let p : E → ℝ := fun x => limsup (fun n => f n x) atTop
  have hp : IsSublinear p := limsup_sublinear hf'
  obtain ⟨F, _, hF⟩ := real_hahn_banach (⊥ : Submodule ℝ E) p hp 0 (by
    intro m
    have hm : (m : E) = 0 := m.property
    simp [hm, hp.map_zero])
  have hpbound (x : E) : p x ≤ C * ‖x‖ :=
    limsup_le_of_le (eval_bddBelow hf' x).isCoboundedUnder_le
      (Eventually.of_forall fun n => (eval_bounds hC x n).2)
  have hnorm (x : E) : ‖F x‖ ≤ C * ‖x‖ := by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h := (hF (-x)).trans (hpbound (-x))
      rw [map_neg, norm_neg] at h
      linarith
    · exact (hF x).trans (hpbound x)
  exact ⟨F.mkContinuous C hnorm, hF⟩

/-- Applying the upper inequality at `-x` gives the lower liminf bound. -/
theorem L_bounds : Spec.LBounds.{u} := by
  intro E _ _ f hf w hw x
  refine ⟨?_, hw x⟩
  have h := hw (-x)
  have heq : limsup (fun n => f n (-x)) atTop =
      -liminf (fun n => f n x) atTop := by
    simpa only [map_neg, zero_sub] using
      (limsup_const_sub atTop (fun n => f n x) 0
        (eval_bddAbove hf x).isCoboundedUnder_ge (eval_bddBelow hf x))
  rw [map_neg, heq, neg_le_neg_iff] at h
  exact h

/-- Tail convexification is transitive, without any boundedness assumption. -/
theorem V_transitive : Spec.VTransitive.{u} := by
  intro E _ _ f g hg h hh n
  apply convexHull_min (t := convexHull ℝ (f '' Ici n)) ?_
    (convex_convexHull ℝ _) (hh n)
  rintro _ ⟨j, hj, rfl⟩
  exact convexHull_mono (image_mono (Ici_subset_Ici.mpr hj)) (hg j)

/-- An increasing subsequence selects a member of each tail. -/
theorem subsequence_mem_V : Spec.SubsequenceMemV.{u} := by
  intro E _ _ f φ hφ n
  exact subset_convexHull ℝ _ ⟨φ n, hφ.id_le n, rfl⟩

/-- Tail convex combinations preserve the common norm bound. -/
lemma V_bounded {f g : ℕ → E →L[ℝ] ℝ} (hf : Spec.BoundedSequence f)
    (hg : g ∈ V f) : Spec.BoundedSequence g := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, fun n => ?_⟩
  have h : g n ∈ Metric.closedBall (0 : E →L[ℝ] ℝ) C := by
    apply convexHull_min (s := f '' Ici n) ?_ (convex_closedBall 0 C) (hg n)
    rintro _ ⟨j, _, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hC j
  simpa only [Metric.mem_closedBall, dist_zero_right] using h

/-- Evaluation of a finite tail convex combination respects a scalar upper bound. -/
lemma tail_eval_le {f : ℕ → E →L[ℝ] ℝ} {n : ℕ} {x : E} {b : ℝ}
    (hb : ∀ j ≥ n, f j x ≤ b) {h : E →L[ℝ] ℝ}
    (hh : h ∈ convexHull ℝ (f '' Ici n)) : h x ≤ b := by
  let ev : (E →L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun k => k x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact convexHull_min (t := {k | ev k ≤ b})
    (by rintro _ ⟨j, hj, rfl⟩; exact hb j hj)
    (convex_halfSpace_le ev.isLinear b) hh

/-- Convex combinations of tails cannot increase the pointwise limsup. -/
lemma V_limsup_le {f g : ℕ → E →L[ℝ] ℝ} (hf : Spec.BoundedSequence f)
    (hg : g ∈ V f) (x : E) :
    limsup (fun n => g n x) atTop ≤ limsup (fun n => f n x) atTop := by
  have hg' := V_bounded hf hg
  apply (limsup_le_iff' (eval_bddBelow hg' x).isCoboundedUnder_le
    (eval_bddAbove hg' x)).2
  intro b hb
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_lt_of_limsup_lt hb (eval_bddAbove hf x))
  exact eventually_atTop.2 ⟨N, fun n hn =>
    tail_eval_le (fun j hj => (hN j (hn.trans hj)).le) (hg n)⟩

theorem L_monotone : Spec.LMonotone.{u} := by
  intro E _ _ f g hf hg w hw x
  exact (hw x).trans (V_limsup_le hf hg x)

/-- For nonempty bounded A the defining real supremum is a genuine supremum. -/
theorem normOn_isLUB : Spec.NormOnIsLUB.{u} := by
  intro E _ _ A hA hAb h
  refine isLUB_csSup (hA.image (fun x => |h x|)) ?_
  obtain ⟨R, hR⟩ := hAb.exists_norm_le
  refine ⟨‖h‖ * R, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (h.le_opNorm x).trans (mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg h))

end ExpandedFA.P1.JamesBlockObjects
