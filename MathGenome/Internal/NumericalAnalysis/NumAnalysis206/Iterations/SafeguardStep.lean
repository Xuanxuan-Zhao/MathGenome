import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.SafeguardStep
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Iterations.BracketExistence
import Mathlib.Tactic.Linarith

namespace NumAnalysis206.Iterations.SafeguardStep
open Specs.NumAnalysis206.Iterations.SafeguardStep

lemma midpoint_central (α a b : ℝ) (hα : α ≤ 1 / 2) (hab : a < b) :
    Central α a b ((a + b) / 2) := by
  have h := mul_le_mul_of_nonneg_right hα (sub_nonneg.mpr hab.le)
  constructor <;> linarith

lemma central_interior (α a b x : ℝ) (hα : 0 < α) (hab : a < b)
    (hx : Central α a b x) : a < x ∧ x < b := by
  have h := mul_pos hα (sub_pos.mpr hab)
  rcases hx with ⟨hl, hr⟩
  constructor <;> linarith

theorem selection_correct : selection := by
  classical
  intro α a b hα hhalf hab
  have hm := midpoint_central α a b hhalf hab
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro proposal
    cases proposal with
    | none => exact hm
    | some x =>
      by_cases hx : Central α a b x
      · simp [choose, hx]
      · simpa [choose, hx] using hm
  · intro x hx
    simp [choose, hx]
  · intro x hx
    simp [choose, hx]

/-- A nonzero interior value selects the endpoint having its sign. -/
lemma sign_alternative (u v z : ℝ) (huv : u * v < 0) (hz : z ≠ 0) :
    (u * z < 0 ∧ z * v > 0) ∨ (z * v < 0 ∧ u * z > 0) := by
  rcases mul_neg_iff.mp huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rcases lt_or_gt_of_ne hz with hz | hz
    · exact Or.inl ⟨mul_neg_of_pos_of_neg hu hz, mul_pos_of_neg_of_neg hz hv⟩
    · exact Or.inr ⟨mul_neg_of_pos_of_neg hz hv, mul_pos hu hz⟩
  · rcases lt_or_gt_of_ne hz with hz | hz
    · exact Or.inr ⟨mul_neg_of_neg_of_pos hz hv, mul_pos_of_neg_of_neg hu hz⟩
    · exact Or.inl ⟨mul_neg_of_neg_of_pos hu hz, mul_pos hz hv⟩

lemma replacement_safe (f : ℝ → ℝ) (α a b x : ℝ)
    (hα : 0 < α) (hab : a < b) (hs : f a * f b < 0)
    (hx : Central α a b x) (hn : f x ≠ 0) :
    Safe f α a b (if f a * f x < 0 then .updated a x else .updated x b) := by
  classical
  obtain ⟨hax, hxb⟩ := central_interior α a b x hα hab hx
  obtain h | h := sign_alternative (f a) (f b) (f x) hs hn
  · simp only [ite_eq_left h.1, Safe]
    refine ⟨le_rfl, hax, hxb.le, ?_, h.1, ?_, Or.inl ⟨by trivial, h.2⟩⟩
    · intro p hp
      exact ⟨hp.1, hp.2.trans hxb.le⟩
    · rcases hx with ⟨hl, hr⟩
      nlinarith
  · have hnot : ¬ f a * f x < 0 := not_lt.mpr h.2.le
    simp only [ite_eq_right hnot, Safe]
    refine ⟨hax.le, hxb, le_rfl, ?_, h.1, ?_, Or.inr ⟨by trivial, h.2⟩⟩
    · intro p hp
      exact ⟨hax.le.trans hp.1, hp.2⟩
    · rcases hx with ⟨hl, hr⟩
      nlinarith

theorem step_safe : stepSafety := by
  classical
  intro f α a b hα hhalf hab hs point sign hsound
  cases point with
  | none => trivial
  | some x =>
    by_cases hx : Central α a b x
    · cases sign with
      | unknown => simp [attempt, hx, Safe]
      | zero =>
        simp only [attempt, ite_eq_left hx, Safe]
        exact ⟨central_interior α a b x hα hab hx, hsound⟩
      | negative =>
        simpa only [attempt, ite_eq_left hx] using
          replacement_safe f α a b x hα hab hs hx (ne_of_lt hsound)
      | positive =>
        simpa only [attempt, ite_eq_left hx] using
          replacement_safe f α a b x hα hab hs hx (ne_of_gt hsound)
    · simp [attempt, hx, Safe]

theorem failure_retains : failurePolicy := by
  classical
  intro f α a b
  refine ⟨?_, ?_, ?_⟩
  · intro sign
    rfl
  · intro point
    cases point with
    | none => rfl
    | some x => by_cases hx : Central α a b x <;> simp [attempt, hx]
  · intro x sign hx
    simp [attempt, hx]

theorem count_successes : countPolicy := by
  intro n result
  cases result <;> simp [advance]

theorem root_certificate : rootCertificate := by
  intro f α A B a b hα hhalf hAB hf hsign hAa hab hbB hs point sign hsound
  have hf' : ContinuousOn f (Set.Icc a b) := hf.mono fun _ hp =>
    ⟨hAa.trans hp.1, hp.2.trans hbB⟩
  have hsafe := step_safe f α a b hα hhalf hab hs point sign hsound
  cases heq : attempt f α a b point sign with
  | retained =>
      exact BracketExistence.root_exists_closed a b f hab hf' hs.le
  | root x =>
      rw [heq] at hsafe
      exact ⟨⟨hsafe.1.1.le, hsafe.1.2.le⟩, hsafe.2⟩
  | updated c d =>
      rw [heq] at hsafe
      rcases hsafe with ⟨hac, hcd, hdb, hsub, hprod, _⟩
      exact BracketExistence.root_exists_closed c d f hcd (hf'.mono hsub) hprod.le

end NumAnalysis206.Iterations.SafeguardStep
