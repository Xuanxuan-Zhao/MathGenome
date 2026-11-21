import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.SafeguardConvergence
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Iterations.SafeguardStep
import Mathlib.Tactic.Linarith

namespace NumAnalysis206.Iterations.SafeguardConvergence
open Specs.NumAnalysis206.Iterations.SafeguardStep
open Specs.NumAnalysis206.Iterations.SafeguardConvergence
open Filter Topology

lemma update_safe (f : ℝ → ℝ) (α : ℝ) (l r : ℕ → ℝ) (n : ℕ)
    (hα : 0 < α) (hh : α ≤ 1 / 2) (hab : l n < r n)
    (hs : f (l n) * f (r n) < 0) (hu : Update f α l r n) :
    Safe f α (l n) (r n) (.updated (l (n + 1)) (r (n + 1))) := by
  obtain ⟨point, sign, hsound, heq⟩ := hu
  have h := SafeguardStep.step_safe f α (l n) (r n) hα hh hab hs point sign hsound
  rwa [heq] at h

lemma prefix_invariant (f : ℝ → ℝ) (α a b : ℝ) (l r : ℕ → ℝ)
    (hα : 0 < α) (hh : α ≤ 1 / 2) (hab : a < b) (hs : f a * f b < 0)
    (n : ℕ) (hp : Prefix f α a b l r n) : Invariant f α a b l r n := by
  induction n with
  | zero =>
    simp only [Invariant, hp.left_initial, hp.right_initial, pow_zero, mul_one]
    exact ⟨le_rfl, hab, le_rfl, hs, le_rfl⟩
  | succ n ih =>
    have hprev : Prefix f α a b l r n :=
      ⟨hp.left_initial, hp.right_initial, fun k hk => hp.updates k (Nat.lt_succ_of_lt hk)⟩
    obtain ⟨hal, hlr, hrb, hsign, hw⟩ := ih hprev
    obtain ⟨hll, hlr', hrr, hsub, hsign', hw', hsame⟩ :=
      update_safe f α l r n hα hh hlr hsign (hp.updates n (Nat.lt_succ_self n))
    refine ⟨hal.trans hll, hlr', hrr.trans hrb, hsign', ?_⟩
    calc
      r (n + 1) - l (n + 1) ≤ (1 - α) * (r n - l n) := hw'
      _ ≤ (1 - α) * ((b - a) * (1 - α) ^ n) :=
        mul_le_mul_of_nonneg_left hw (by linarith)
      _ = (b - a) * (1 - α) ^ (n + 1) := by rw [pow_succ]; ring

theorem finite_bounds : finiteBounds := by
  intro f α a b l r hα hh hab hs N hp n hn
  exact prefix_invariant f α a b l r hα hh hab hs n
    ⟨hp.left_initial, hp.right_initial, fun k hk => hp.updates k (hk.trans_le hn)⟩

lemma midpoint_bound (u v p : ℝ) (hp : p ∈ Set.Icc u v) :
    |(u + v) / 2 - p| ≤ (v - u) / 2 := by
  rw [abs_le]
  constructor <;> linarith [hp.1, hp.2]

/-- Any selection inside the shrinking enclosures has their common limit. -/
lemma tendsto_of_enclosure (l r z : ℕ → ℝ) (p : ℝ) (bound : ℕ → ℝ)
    (hp : ∀ n, p ∈ Set.Icc (l n) (r n))
    (hz : ∀ n, z n ∈ Set.Icc (l n) (r n))
    (hw : ∀ n, r n - l n ≤ bound n)
    (hb : Tendsto bound atTop (𝓝 0)) : Tendsto z atTop (𝓝 p) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine tendsto_const_nhds.squeeze hb (fun n => dist_nonneg) ?_
  intro n
  change dist (z n) p ≤ bound n
  rw [Real.dist_eq, abs_le]
  have hpn := hp n
  have hzn := hz n
  have hwn := hw n
  constructor <;> linarith [hpn.1, hpn.2, hzn.1, hzn.2]

theorem infinite_convergence : infiniteConvergence := by
  intro f α a b l r hα hh hab hf hs hl0 hr0 hu
  have hi : ∀ n, Invariant f α a b l r n := fun n =>
    prefix_invariant f α a b l r hα hh hab hs n ⟨hl0, hr0, fun k _ => hu k⟩
  have hstep : ∀ n, Set.Icc (l (n + 1)) (r (n + 1)) ⊆ Set.Icc (l n) (r n) := by
    intro n
    exact (update_safe f α l r n hα hh (hi n).2.1 (hi n).2.2.2.1 (hu n)).2.2.2.1
  have hnest : ∀ i j, i ≤ j → Set.Icc (l j) (r j) ⊆ Set.Icc (l i) (r i) := by
    intro i j hij
    have hanti : Antitone (fun n => Set.Icc (l n) (r n)) :=
      antitone_nat_of_succ_le hstep
    exact hanti hij
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => Set.Icc (l n) (r n)) hstep
    (fun n => Set.nonempty_Icc.mpr (hi n).2.1.le) isCompact_Icc (fun _ => isClosed_Icc)
  have hpmem : ∀ n, p ∈ Set.Icc (l n) (r n) := Set.mem_iInter.mp hp
  have hpow : Tendsto (fun n : ℕ => (1 - α) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have hbound : Tendsto (fun n : ℕ => (b - a) * (1 - α) ^ n) atTop (𝓝 0) := by
    simpa using hpow.const_mul (b - a)
  have hwidth : ∀ n, r n - l n ≤ (b - a) * (1 - α) ^ n := fun n => (hi n).2.2.2.2
  have hl : Tendsto l atTop (𝓝 p) := tendsto_of_enclosure l r l p _ hpmem
    (fun n => ⟨le_rfl, (hi n).2.1.le⟩) hwidth hbound
  have hr : Tendsto r atTop (𝓝 p) := tendsto_of_enclosure l r r p _ hpmem
    (fun n => ⟨(hi n).2.1.le, le_rfl⟩) hwidth hbound
  have hm : Tendsto (fun n => (l n + r n) / 2) atTop (𝓝 p) := by
    simpa using (hl.add hr).div_const (2 : ℝ)
  have hp0 : p ∈ Set.Icc a b := by simpa [hl0, hr0] using hpmem 0
  have hfl : Tendsto (fun n => f (l n)) atTop (𝓝 (f p)) :=
    (hf p hp0).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hl,
      Eventually.of_forall (fun n => ⟨(hi n).1, (hi n).2.1.le.trans (hi n).2.2.1⟩)⟩)
  have hfr : Tendsto (fun n => f (r n)) atTop (𝓝 (f p)) :=
    (hf p hp0).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hr,
      Eventually.of_forall (fun n => ⟨(hi n).1.trans (hi n).2.1.le, (hi n).2.2.1⟩)⟩)
  have hprod : f p * f p ≤ 0 := le_of_tendsto (hfl.mul hfr)
    (Eventually.of_forall (fun n => (hi n).2.2.2.1.le))
  have hroot : f p = 0 := (sq_nonpos_iff (f p)).mp (by simpa [pow_two] using hprod)
  refine ⟨hi, hnest, p, hroot, hpmem, hl, hr, hm, ?_⟩
  intro n
  exact (midpoint_bound (l n) (r n) p (hpmem n)).trans
    (div_le_div_of_nonneg_right (hwidth n) (by norm_num))

theorem attempt_rules : attemptRules :=
  ⟨SafeguardStep.selection_correct, SafeguardStep.step_safe,
    SafeguardStep.failure_retains, SafeguardStep.count_successes,
    SafeguardStep.root_certificate⟩

theorem safeguarded_bracketing : safeguardedBracketing :=
  ⟨attempt_rules, finite_bounds, infinite_convergence⟩

end NumAnalysis206.Iterations.SafeguardConvergence
