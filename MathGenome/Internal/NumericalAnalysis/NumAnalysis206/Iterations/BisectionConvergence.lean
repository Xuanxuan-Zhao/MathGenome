import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.BisectionConvergence
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Iterations.BisectionInvariants
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic

namespace NumAnalysis206.Iterations.BisectionConvergence

open Specs.NumAnalysis206.Iterations.BisectionInvariants
open Specs.NumAnalysis206.Iterations.BisectionConvergence
open Filter
open scoped Topology

/-- Apply the accepted finite-run theorem to each finite prefix. -/
theorem run_invariants (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hsign : f a * f b ≤ 0)
    (r : InfiniteRun f a b) : RunInvariants f a b r := by
  constructor
  · intro n
    exact (BisectionInvariants.finite_invariants f a b n hab hf hsign
      (r.toFinite n)).1 n le_rfl
  · intro n
    exact (BisectionInvariants.finite_invariants f a b (n+1) hab hf hsign
      (r.toFinite (n+1))).2 n (Nat.lt_succ_self n)

/-- The nested brackets shrink to one point. Continuity and the nonpositive
endpoint products make that point a root, including zero-endpoint cases. -/
theorem infinite_convergence : infiniteConvergence := by
  intro f a b hab hf hsign r
  have hinv := run_invariants f a b hab hf hsign r
  refine ⟨hinv, ?_⟩
  have hleft : Monotone r.left := by
    apply monotone_nat_of_le_succ
    intro n
    exact (hinv.2 n ⟨le_rfl, (hinv.1 (n+1)).1.le⟩).1
  have hright : Antitone r.right := by
    apply antitone_nat_of_succ_le
    intro n
    exact (hinv.2 n ⟨(hinv.1 (n+1)).1.le, le_rfl⟩).2
  let p : ℝ := ⨆ n, r.left n
  have hp : ∀ n, p ∈ Set.Icc (r.left n) (r.right n) :=
    Set.mem_iInter.mp (hleft.ciSup_mem_iInter_Icc_of_antitone hright
      (fun n => (hinv.1 n).1.le))
  have hbdd : BddAbove (Set.range r.left) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact ((hinv.1 n).2.1 ⟨le_rfl, (hinv.1 n).1.le⟩).2
  have hl : Tendsto r.left atTop (𝓝 p) := tendsto_atTop_ciSup hleft hbdd
  have hw : Tendsto (fun n => r.right n - r.left n) atTop (𝓝 (0 : ℝ)) := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).mul_const (b-a)
    simpa only [zero_mul, ← (fun n => (hinv.1 n).2.2.2.1)] using ht
  have hr : Tendsto r.right atTop (𝓝 p) := by
    have ht := hw.add hl
    simpa only [sub_add_cancel, zero_add] using ht
  have hm : Tendsto (fun n => midpoint (r.left n) (r.right n)) atTop (𝓝 p) := by
    have ht := (hl.add hr).div_const 2
    convert ht using 1 <;> simp [midpoint, add_self_div_two]
  have hpab : p ∈ Set.Icc a b := by
    have := hp 0
    simpa only [r.left_zero, r.right_zero] using this
  have hfl : Tendsto (fun n => f (r.left n)) atTop (𝓝 (f p)) := by
    apply (hf p hpab).tendsto.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨hl, Filter.Eventually.of_forall fun n =>
      (hinv.1 n).2.1 ⟨le_rfl, (hinv.1 n).1.le⟩⟩
  have hfr : Tendsto (fun n => f (r.right n)) atTop (𝓝 (f p)) := by
    apply (hf p hpab).tendsto.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨hr, Filter.Eventually.of_forall fun n =>
      (hinv.1 n).2.1 ⟨(hinv.1 n).1.le, le_rfl⟩⟩
  have hzero : f p = 0 := by
    have hsq : f p * f p ≤ 0 :=
      le_of_tendsto (hfl.mul hfr) (Filter.Eventually.of_forall fun n => (hinv.1 n).2.2.1)
    exact mul_self_eq_zero.mp (le_antisymm hsq (mul_self_nonneg _))
  refine ⟨p, hp, hzero, ?_, hl, hr, hm, ?_⟩
  · intro q hq
    apply le_antisymm
    · exact ge_of_tendsto' hr (fun n => (hq n).2)
    · exact le_of_tendsto' hl (fun n => (hq n).1)
  · intro n
    calc
      |midpoint (r.left n) (r.right n) - p| ≤ (r.right n - r.left n)/2 :=
        BisectionInvariants.midpoint_distance _ _ _ (hp n)
      _ = (1/2 : ℝ)^(n+1) * (b-a) := by rw [(hinv.1 n).2.2.2.1, pow_succ]; ring

end NumAnalysis206.Iterations.BisectionConvergence
