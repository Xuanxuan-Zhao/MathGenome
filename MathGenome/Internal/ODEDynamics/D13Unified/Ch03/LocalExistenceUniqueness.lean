import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.ControlledPicard
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.LocalExistenceUniqueness
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open Set Metric

namespace D13Unified.Ch03.LocalExistenceUniqueness
universe u
open Specs.D13Unified.Ch03.LocalExistenceUniqueness

/-- A positive Picard time exists even if either of the nonnegative bounds is
zero. Adding one in the denominators avoids division by those bounds. -/
lemma exists_picard_time (a b M L : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∃ h : ℝ, 0 < h ∧ h ≤ a ∧ M * h ≤ b ∧ L * h < 1 := by
  have hMp : 0 < M + 1 := by positivity
  have hLp : 0 < L + 1 := by positivity
  have hmin : 0 < min a (min (b / (M + 1)) (1 / (L + 1))) := by
    exact lt_min ha (lt_min (div_pos hb hMp) (div_pos zero_lt_one hLp))
  obtain ⟨h, hh, hsmall⟩ := exists_between hmin
  have hparts := lt_min_iff.mp hsmall
  have hrest := lt_min_iff.mp hparts.2
  have hMh := (lt_div_iff₀ hMp).mp hrest.1
  have hLh := (lt_div_iff₀ hLp).mp hrest.2
  exact ⟨h, hh, hparts.1.le, by nlinarith, by nlinarith⟩

theorem overlap_uniqueness : overlapUniquenessExpected.{u} :=
  ControlledPicard.overlap_uniqueness

/-- Local control is shrunk to a compact product box, so the field has a finite
norm bound there. The controlled Picard solution restricts to a C¹ solution on
the open interior; no completeness or positivity of the state dimension is
added to the source hypotheses. -/
theorem local_existence_uniqueness : localExistenceUniquenessExpected.{u} := by
  intro E _ _ _ F hF s ξ hs
  obtain ⟨a, b, L, ha, hb, hL, hdom, hlip⟩ := hF s ξ hs
  have hat : 0 < a / 2 := by positivity
  have hbt : 0 < b / 2 := by positivity
  have htime : Icc (s - a / 2) (s + a / 2) ⊆ ball s a := by
    rw [Real.ball_eq_Ioo]
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hstate : closedBall ξ (b / 2) ⊆ ball ξ b :=
    closedBall_subset_ball (by linarith)
  have hbox : Icc (s - a / 2) (s + a / 2) ×ˢ closedBall ξ (b / 2) ⊆ F.domain :=
    fun _ h => hdom ⟨htime h.1, hstate h.2⟩
  have hc : IsCompact (Icc (s - a / 2) (s + a / 2) ×ˢ closedBall ξ (b / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall ξ (b / 2))
  obtain ⟨M, hbound⟩ := hc.exists_bound_of_continuousOn (F.continuousOn_eval.mono hbox)
  have hcenter : (s, ξ) ∈ Icc (s - a / 2) (s + a / 2) ×ˢ closedBall ξ (b / 2) :=
    ⟨⟨by linarith, by linarith⟩, mem_closedBall_self hbt.le⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound (s, ξ) hcenter)
  obtain ⟨h, hh, hha, hMh, hLh⟩ := exists_picard_time (a / 2) (b / 2) M L hat hbt hM hL
  obtain ⟨x, hx, _, _, _⟩ := ControlledPicard.controlled_picard
    F s ξ (a / 2) (b / 2) M L h hM hL hh hha hMh hLh hbox
    (fun t ht z hz => hbound (t, z) ⟨ht, hz⟩)
    (fun t ht z hz w hw => hlip t (htime ht) z (hstate hz) w (hstate hw))
  let I := OpenTimeInterval.bounded (s - h) (s + h) (by linarith)
  have hsub : I.carrier ⊆ (Specs.D13Unified.Ch03.ControlledPicard.controlledInterval s h hh).carrier :=
    Ioo_subset_Icc_self
  have hxI : IsClassicalIVPOn F I x s ξ := by
    refine ⟨(classical_iff_solutionOn F I x).mpr ?_, ?_, hx.2.2⟩
    · exact ⟨hx.1.1.mono hsub, fun t ht => hx.1.2.1 t (hsub ht),
        fun t ht => (hx.1.2.2 t (hsub ht)).mono hsub⟩
    · exact ⟨by linarith, by linarith⟩
  exact ⟨I, x, hxI, fun J y hy => overlap_uniqueness F hF I J x y s ξ hxI hy⟩

theorem no_crossing : noCrossingExpected.{u} := by
  intro E _ _ _ F hF I J x y s hx hy hs heq
  exact overlap_uniqueness F hF I J x y s (x s)
    ⟨hx, hs.1, rfl⟩ ⟨hy, hs.2, heq.symm⟩

end D13Unified.Ch03.LocalExistenceUniqueness
