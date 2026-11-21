import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.KKTNecessity
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.FritzJohn
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.MFCQTangency
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section
universe u v w
namespace VariationalNotes.Ch06
open Specs
open ContinuousLinearMap

/-- MFCQ excludes every abnormal Fritz John multiplier, without any additional
smoothness hypothesis on the algebraic multiplier system. -/
theorem objectiveMultiplier_pos_of_mfcq :
    KKTNecessitySpecs.objectiveMultiplier_pos_of_mfcq.{u,v,w} := by
  classical
  intro X _ _ I J _ _ U f g h x lam0 lam nu hm hfj
  obtain ⟨hx, hnonneg, hlam, hcomp, hne, hstation⟩ := hfj
  obtain ⟨_, hsurj, w, hw, hstrict⟩ := hm
  have hinactive (i : I) (hi : i ∉ activeSet g x) : lam i = 0 :=
    (mul_eq_zero.mp (hcomp i)).resolve_right hi
  have heval (d : X) : lam0 * fderiv ℝ f x d +
      (∑ i, lam i * fderiv ℝ (g i) x d) +
      (∑ j, nu j * fderiv ℝ (h j) x d) = 0 := by
    simpa only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply] using
      congrArg (fun L : X →L[ℝ] ℝ => L d) hstation
  by_contra hnotpos
  have h0 : lam0 = 0 := le_antisymm (le_of_not_gt hnotpos) hnonneg
  have heqw (j : J) : fderiv ℝ (h j) x w = 0 := congrFun hw j
  have hsum : ∑ i, lam i * fderiv ℝ (g i) x w = 0 := by
    simpa [h0, heqw] using heval w
  have hnonpos (i : I) : lam i * fderiv ℝ (g i) x w ≤ 0 := by
    by_cases hi : i ∈ activeSet g x
    · exact mul_nonpos_of_nonneg_of_nonpos (hlam i) (hstrict i hi).le
    · simp [hinactive i hi]
  have hlamzero (i : I) : lam i = 0 := by
    by_cases hi : i ∈ activeSet g x
    · have ht := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hnonpos i)).mp hsum
        i (Finset.mem_univ i)
      exact (mul_eq_zero.mp ht).resolve_right (hstrict i hi).ne
    · exact hinactive i hi
  have hnuzero (j : J) : nu j = 0 := by
    obtain ⟨d, hd⟩ := hsurj (Pi.single j 1)
    have hdk (k : J) : fderiv ℝ (h k) x d = (Pi.single j 1 : J → ℝ) k :=
      congrFun hd k
    simpa [h0, hlamzero, hdk, Pi.single_apply] using heval d
  rcases hne with hne | ⟨i, hi⟩ | ⟨j, hj⟩
  · exact hne h0
  · exact hi (hlamzero i)
  · exact hj (hnuzero j)

/-- Normalize the shared Fritz John system by its positive objective coefficient. -/
theorem normalize_fritzJohn : KKTNecessitySpecs.normalize_fritzJohn.{u,v,w} := by
  classical
  intro X _ _ I J _ _ U f g h x lam0 lam nu hfj hpos
  obtain ⟨hx, _, hlam, hcomp, _, hstation⟩ := hfj
  refine ⟨hx, fun i => div_nonneg (hlam i) hpos.le, ?_, ?_⟩
  · intro i
    rw [div_mul_eq_mul_div, hcomp i, zero_div]
  · have hs := congrArg (fun L : X →L[ℝ] ℝ => lam0⁻¹ • L) hstation
    simpa [smul_add, Finset.smul_sum, smul_smul, hpos.ne',
      div_eq_mul_inv, mul_comm] using hs

/-- The local minimum gives Fritz John multipliers unconditionally; MFCQ makes
these multipliers normal, so normalization supplies KKT multipliers. -/
theorem kkt_of_mfcq : KKTNecessitySpecs.kkt_of_mfcq.{u,v,w} := by
  intro X _ _ _ I J _ _ U f g h x hs hmin hm
  obtain ⟨lam0, lam, nu, hfj⟩ := fritzJohn U f g h x hs hm.1 hmin
  exact ⟨_, _, normalize_fritzJohn U f g h x lam0 lam nu hfj
    (objectiveMultiplier_pos_of_mfcq U f g h x lam0 lam nu hm hfj)⟩

/-- LICQ suffices through the accepted LICQ-to-MFCQ implication. -/
theorem kkt_of_licq : KKTNecessitySpecs.kkt_of_licq.{u,v,w} := by
  intro X _ _ _ I J _ _ U f g h x hs hmin hl
  exact kkt_of_mfcq U f g h x hs hmin (licq_implies_mfcq U g h x hl)

/-- The complete Fritz John and KKT necessity theorem from §v06-04, retaining
unconditional Fritz John existence and both qualified normality conclusions. -/
theorem fritzJohn_and_kkt : KKTNecessitySpecs.fritzJohn_and_kkt.{u,v,w} := by
  intro X _ _ _ I J _ _ U f g h x hs hx hmin
  refine ⟨fritzJohn U f g h x hs hx hmin, ?_, ?_⟩
  · intro hm
    exact ⟨fun lam0 lam nu hfj =>
      objectiveMultiplier_pos_of_mfcq U f g h x lam0 lam nu hm hfj,
      kkt_of_mfcq U f g h x hs hmin hm⟩
  · intro hl
    exact ⟨fun lam0 lam nu hfj =>
      objectiveMultiplier_pos_of_mfcq U f g h x lam0 lam nu
        (licq_implies_mfcq U g h x hl) hfj,
      kkt_of_licq U f g h x hs hmin hl⟩

end VariationalNotes.Ch06
