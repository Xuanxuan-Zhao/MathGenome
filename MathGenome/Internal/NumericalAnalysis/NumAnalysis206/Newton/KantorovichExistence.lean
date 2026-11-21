import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.KantorovichExistence
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.KantorovichSteps
import Mathlib.Topology.MetricSpace.Cauchy

noncomputable section
universe u v w
open Set Metric Filter
namespace NumAnalysis206.Newton

/-- Successive step bounds telescope without any compactness assumption. -/
lemma norm_sub_le_of_step_bounds {X : Type v} [NormedAddCommGroup X]
    (x : ℕ → X) (t : ℕ → ℝ)
    (hs : ∀ n, ‖x (n + 1) - x n‖ ≤ t (n + 1) - t n)
    (n j : ℕ) (hnj : n ≤ j) : ‖x j - x n‖ ≤ t j - t n := by
  induction j, hnj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    calc
      ‖x (j + 1) - x n‖ ≤ ‖x (j + 1) - x j‖ + ‖x j - x n‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (t (j + 1) - t j) + (t j - t n) := add_le_add (hs j) ih
      _ = t (j + 1) - t n := by ring

open Majorant

/-- Completeness and the residual majorant produce the W77 zero and its
error bound, including when `2 * η * L = 1`. -/
theorem kantorovich_existence :
    Specs.NumAnalysis206.Newton.KantorovichExistence.Statement := by
  intro 𝕜 _ X Y _ _ _ _ _ _ F U x₀ A η L hU hF hx₀ hA hη hL hb hres hball hLip x
  let G : X → X := fun z => A.symm (F z)
  have hsteps := kantorovich_steps 𝕜 X Y F U x₀ A η L
    hU hF hx₀ hA hη hL hb hres hball hLip
  have hs : ∀ n, ‖x (n + 1) - x n‖ ≤ iterate η L (n + 1) - iterate η L n :=
    fun n => (hsteps.2.2.2.2 n).2.2.2.2.2.2
  have htel := norm_sub_le_of_step_bounds x (iterate η L) hs
  have ht := iterate_tendsto hη hL hb
  have htail : Tendsto (fun n => lowerRoot η L - iterate η L n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := lowerRoot η L)).sub ht
  have hc : CauchySeq x := by
    apply cauchySeq_of_le_tendsto_0' (fun n => lowerRoot η L - iterate η L n) _ htail
    intro n j hnj
    rw [dist_comm, dist_eq_norm]
    exact (htel n j hnj).trans (sub_le_sub_right (iterate_bounds hη hL hb j).2.le _)
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hc
  have herr (n : ℕ) : ‖p - x n‖ ≤ lowerRoot η L - iterate η L n := by
    apply le_of_tendsto_of_tendsto ((hp.sub_const (x n)).norm) (ht.sub_const (iterate η L n))
    exact (eventually_ge_atTop n).mono fun j hj => htel n j hj
  have hpmem : p ∈ closedBall x₀ (lowerRoot η L) := by
    rw [mem_closedBall, dist_eq_norm]
    have h := herr 0
    change ‖p - x₀‖ ≤ lowerRoot η L - 0 at h
    simpa only [sub_zero] using h
  have hGp : ContinuousAt G p :=
    ((hsteps.1 p (hball hpmem)).differentiableAt (hU.mem_nhds (hball hpmem))).continuousAt
  have hm : Tendsto (fun n => majorant η L (iterate η L n)) atTop (nhds 0) := by
    have hmcont : Continuous (majorant η L) := by
      unfold majorant
      fun_prop
    simpa only [Function.comp_def, (root_data hη hL hb).2.2.2.2.2.1] using
      hmcont.continuousAt.tendsto.comp ht
  have hz : Tendsto (fun n => ‖G (x n)‖) atTop (nhds 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) _ hm
    exact fun n => (hsteps.2.2.2.2 n).2.2.2.2.1
  have hGzero : G p = 0 := by
    apply norm_eq_zero.mp
    exact tendsto_nhds_unique (hGp.tendsto.comp hp).norm hz
  have hFzero : F p = 0 := by
    apply A.symm.injective
    simpa only [map_zero] using hGzero
  exact ⟨htel, hc, p, hpmem, hFzero, hp, herr⟩

end NumAnalysis206.Newton
