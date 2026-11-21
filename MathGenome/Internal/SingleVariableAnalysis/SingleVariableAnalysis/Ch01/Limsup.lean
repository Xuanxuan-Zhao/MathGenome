import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SupInf
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Monotone
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Subsequence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Squeeze
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Limsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Upper and lower limits

K03.01.limsup (paper.tex:288–302). Index `n` represents positive index `n+1`.
The tail definitions use the complete extended real lattice, including unbounded
sequences. Global real upper and lower bounds prove finiteness before real
extraction. Tail convergence uses monotone convergence. Extremal subsequences
use the order-topological characterization of limsup/liminf as cluster points,
and the first-countable cluster-point subsequence construction. Thus the
selected indices are strictly increasing, not merely cofinal or repeated.
-/

noncomputable section
namespace SingleVariableAnalysis

open Filter
open scoped Topology

def tailSupremum (a : ℕ → ℝ) (N : ℕ) : EReal := ⨆ n ≥ N, (a n : EReal)
def tailInfimum (a : ℕ → ℝ) (N : ℕ) : EReal := ⨅ n ≥ N, (a n : EReal)
def sequenceLimsup (a : ℕ → ℝ) : EReal := ⨅ N, tailSupremum a N
def sequenceLiminf (a : ℕ → ℝ) : EReal := ⨆ N, tailInfimum a N

theorem tailSupremum_antitone (a : ℕ → ℝ) : Antitone (tailSupremum a) := by
  intro N M hNM
  exact iSup_le fun n => iSup_le fun hn => le_iSup_of_le n (le_iSup_of_le (hNM.trans hn) le_rfl)

theorem tailInfimum_monotone (a : ℕ → ℝ) : Monotone (tailInfimum a) := by
  intro N M hNM
  exact le_iInf fun n => le_iInf fun hn => iInf_le_of_le n (iInf_le_of_le (hNM.trans hn) le_rfl)

private theorem tail_bounds (a : ℕ → ℝ) {b c : ℝ} (hb : ∀ n, b ≤ a n)
    (hc : ∀ n, a n ≤ c) (N : ℕ) :
    (b : EReal) ≤ tailSupremum a N ∧ tailSupremum a N ≤ (c : EReal) ∧
    (b : EReal) ≤ tailInfimum a N ∧ tailInfimum a N ≤ (c : EReal) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (EReal.coe_le_coe (hb N)).trans
      (le_iSup_of_le N (le_iSup_of_le le_rfl le_rfl))
  · exact iSup_le fun n => iSup_le fun _ => EReal.coe_le_coe (hc n)
  · exact le_iInf fun n => le_iInf fun _ => EReal.coe_le_coe (hb n)
  · exact (iInf_le_of_le N (iInf_le_of_le le_rfl le_rfl)).trans
      (EReal.coe_le_coe (hc N))

private theorem finite_of_bounds {x : EReal} {b c : ℝ}
    (hb : (b : EReal) ≤ x) (hc : x ≤ (c : EReal)) :
    (x.toReal : EReal) = x := by
  exact EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top c) hc)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot b) hb)

theorem bounded_bounds_finite (a : ℕ → ℝ) (ha : BddAbove (Set.range a))
    (hb : BddBelow (Set.range a)) :
    (∀ N, ((tailSupremum a N).toReal : EReal) = tailSupremum a N ∧
      ((tailInfimum a N).toReal : EReal) = tailInfimum a N) ∧
    ((sequenceLimsup a).toReal : EReal) = sequenceLimsup a ∧
    ((sequenceLiminf a).toReal : EReal) = sequenceLiminf a := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨b, hb⟩ := hb
  have ht := tail_bounds a (fun n => hb (Set.mem_range_self n))
    (fun n => hc (Set.mem_range_self n))
  refine ⟨fun N => ⟨finite_of_bounds (ht N).1 (ht N).2.1,
    finite_of_bounds (ht N).2.2.1 (ht N).2.2.2⟩, ?_, ?_⟩
  · exact finite_of_bounds (le_iInf fun N => (ht N).1)
      ((iInf_le _ 0).trans (ht 0).2.1)
  · exact finite_of_bounds ((ht 0).2.2.1.trans (le_iSup _ 0))
      (iSup_le fun N => (ht N).2.2.2)

private theorem finite_ne {x : EReal} (h : (x.toReal : EReal) = x) :
    x ≠ ⊤ ∧ x ≠ ⊥ := by
  rw [← h]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

theorem bounded_tail_convergence (a : ℕ → ℝ) (ha : BddAbove (Set.range a))
    (hb : BddBelow (Set.range a)) :
    Antitone (fun N => (tailSupremum a N).toReal) ∧
    Monotone (fun N => (tailInfimum a N).toReal) ∧
    RealSequenceConverges (fun N => (tailSupremum a N).toReal) (sequenceLimsup a).toReal ∧
    RealSequenceConverges (fun N => (tailInfimum a N).toReal) (sequenceLiminf a).toReal := by
  obtain ⟨hT, hU, hL⟩ := bounded_bounds_finite a ha hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N M hNM
    apply EReal.coe_le_coe_iff.mp
    rw [(hT M).1, (hT N).1]
    exact tailSupremum_antitone a hNM
  · intro N M hNM
    apply EReal.coe_le_coe_iff.mp
    rw [(hT N).2, (hT M).2]
    exact tailInfimum_monotone a hNM
  · exact (realSequenceConverges_iff _ _).mpr
      ((EReal.tendsto_toReal (finite_ne hU).1 (finite_ne hU).2).comp
        (tendsto_atTop_iInf (tailSupremum_antitone a)))
  · exact (realSequenceConverges_iff _ _).mpr
      ((EReal.tendsto_toReal (finite_ne hL).1 (finite_ne hL).2).comp
        (tendsto_atTop_iSup (tailInfimum_monotone a)))

private theorem sequenceLimsup_eq_filter (a : ℕ → ℝ) :
    sequenceLimsup a = limsup (fun n => (a n : EReal)) atTop :=
  limsup_eq_iInf_iSup_of_nat.symm

private theorem sequenceLiminf_eq_filter (a : ℕ → ℝ) :
    sequenceLiminf a = liminf (fun n => (a n : EReal)) atTop :=
  liminf_eq_iSup_iInf_of_nat.symm

theorem bounded_extreme_subsequential_limits (a : ℕ → ℝ)
    (ha : BddAbove (Set.range a)) (hb : BddBelow (Set.range a)) :
    RealSubsequentialLimit a (sequenceLimsup a).toReal ∧
    RealSubsequentialLimit a (sequenceLiminf a).toReal := by
  obtain ⟨_, hU, hL⟩ := bounded_bounds_finite a ha hb
  have hsup : MapClusterPt (sequenceLimsup a) atTop (fun n => (a n : EReal)) := by
    rw [sequenceLimsup_eq_filter]
    exact MapClusterPt.limsup
  have hinf : MapClusterPt (sequenceLiminf a) atTop (fun n => (a n : EReal)) := by
    rw [sequenceLiminf_eq_filter]
    exact MapClusterPt.liminf
  obtain ⟨φ, hφ, hφlim⟩ := hsup.tendsto_subseq
  obtain ⟨ψ, hψ, hψlim⟩ := hinf.tendsto_subseq
  constructor
  · refine ⟨φ, hφ, (realSequenceConverges_iff _ _).mpr ?_⟩
    rw [← hU] at hφlim
    exact EReal.tendsto_coe.mp hφlim
  · refine ⟨ψ, hψ, (realSequenceConverges_iff _ _).mpr ?_⟩
    rw [← hL] at hψlim
    exact EReal.tendsto_coe.mp hψlim

theorem subsequential_limit_bounds (a : ℕ → ℝ) (v : ℝ)
    (hv : RealSubsequentialLimit a v) :
    sequenceLiminf a ≤ (v : EReal) ∧ (v : EReal) ≤ sequenceLimsup a := by
  obtain ⟨φ, hφ, hv⟩ := hv
  have ht : Tendsto (fun j => (a (φ j) : EReal)) atTop (𝓝 (v : EReal)) :=
    EReal.tendsto_coe.mpr ((realSequenceConverges_iff _ _).mp hv)
  have hcl : MapClusterPt (v : EReal) atTop (fun n => (a n : EReal)) :=
    MapClusterPt.of_comp hφ.tendsto_atTop ht.mapClusterPt
  rw [sequenceLiminf_eq_filter, sequenceLimsup_eq_filter]
  exact ⟨hcl.liminf_le, hcl.le_limsup⟩

theorem bounded_subsequential_limit_bounds (a : ℕ → ℝ)
    (ha : BddAbove (Set.range a)) (hb : BddBelow (Set.range a))
    (v : ℝ) (hv : RealSubsequentialLimit a v) :
    (sequenceLiminf a).toReal ≤ v ∧ v ≤ (sequenceLimsup a).toReal := by
  obtain ⟨_, hU, hL⟩ := bounded_bounds_finite a ha hb
  have h := subsequential_limit_bounds a v hv
  rw [← hL, ← hU] at h
  exact ⟨EReal.coe_le_coe_iff.mp h.1, EReal.coe_le_coe_iff.mp h.2⟩

end SingleVariableAnalysis
