import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PC1MonotoneSubstitution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Slope

open MeasureTheory Set
open scoped Interval

namespace D12Complex.Ch03.PC1MonotoneSubstitution

/-- On one smooth piece monotonicity supplies the derivative sign, including zero speed. -/
lemma weighted_substitution_piece {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφ : ContDiffOn ℝ 1 φ (Icc a b)) (hm : MonotoneOn φ (Icc a b))
    {g : ℝ → ℂ} (hg : IntervalIntegrable g volume (φ a) (φ b)) :
    IntervalIntegrable (fun t => deriv φ t • g (φ t)) volume a b ∧
      (∫ t in a..b, deriv φ t • g (φ t)) = ∫ s in φ a..φ b, g s := by
  have hc : ContinuousOn φ [[a, b]] := by
    simpa only [uIcc_of_le hab] using hφ.continuousOn
  have hd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt φ (deriv φ t) t := by
    intro t ht
    have ht' : t ∈ Ioo a b := by simpa only [min_eq_left hab, max_eq_right hab] using ht
    exact ((hφ.differentiableOn_one t (Ioo_subset_Icc_self ht')).differentiableAt
      (Icc_mem_nhds ht'.1 ht'.2)).hasDerivAt
  have hn : ∀ t ∈ Ioo (min a b) (max a b), 0 ≤ deriv φ t := by
    intro t ht
    have ht' : t ∈ Ioo a b := by simpa only [min_eq_left hab, max_eq_right hab] using ht
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht'.1 ht'.2)]
    exact hm.derivWithin_nonneg
  exact ⟨(intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg hc hd hn).2 hg,
    intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg hc hd hn⟩

/-- Glue adjacent substitution identities. Neither node sequence needs to be strict;
in particular, the target nodes may repeat on flat parameter pieces. -/
lemma weighted_substitution_partition (F G : ℝ → ℂ) :
    ∀ (n : ℕ) (source target : Fin (n + 1) → ℝ),
      (∀ i : Fin n, IntervalIntegrable F volume (source i.castSucc) (source i.succ)) →
      (∀ i : Fin n, IntervalIntegrable G volume (target i.castSucc) (target i.succ)) →
      (∀ i : Fin n, (∫ t in source i.castSucc..source i.succ, F t) =
        ∫ s in target i.castSucc..target i.succ, G s) →
      IntervalIntegrable F volume (source 0) (source (Fin.last n)) ∧
      IntervalIntegrable G volume (target 0) (target (Fin.last n)) ∧
      (∫ t in source 0..source (Fin.last n), F t) =
        ∫ s in target 0..target (Fin.last n), G s := by
  intro n
  induction n with
  | zero =>
      intro source target hF hG heq
      simp
  | succ n ih =>
      intro source target hF hG heq
      let source' : Fin (n + 1) → ℝ := fun i => source i.castSucc
      let target' : Fin (n + 1) → ℝ := fun i => target i.castSucc
      have hF' : ∀ i : Fin n,
          IntervalIntegrable F volume (source' i.castSucc) (source' i.succ) := by
        intro i
        simpa [source', Fin.castSucc_succ] using hF i.castSucc
      have hG' : ∀ i : Fin n,
          IntervalIntegrable G volume (target' i.castSucc) (target' i.succ) := by
        intro i
        simpa [target', Fin.castSucc_succ] using hG i.castSucc
      have heq' : ∀ i : Fin n,
          (∫ t in source' i.castSucc..source' i.succ, F t) =
            ∫ s in target' i.castSucc..target' i.succ, G s := by
        intro i
        simpa [source', target', Fin.castSucc_succ] using heq i.castSucc
      obtain ⟨hfirst, htarget_first, hfirst_eq⟩ := ih source' target' hF' hG' heq'
      have hlast := hF (Fin.last n)
      refine ⟨hfirst.trans hlast, htarget_first.trans (hG (Fin.last n)), ?_⟩
      calc
        _ = (∫ t in source' 0..source' (Fin.last n), F t) +
            ∫ t in source (Fin.last n).castSucc..source (Fin.last n).succ, F t := by
          simpa [source'] using
            (intervalIntegral.integral_add_adjacent_intervals hfirst hlast).symm
        _ = (∫ s in target' 0..target' (Fin.last n), G s) +
            ∫ s in target (Fin.last n).castSucc..target (Fin.last n).succ, G s := by
          rw [hfirst_eq, heq (Fin.last n)]
        _ = _ := by
          simpa [target'] using
            intervalIntegral.integral_add_adjacent_intervals htarget_first (hG (Fin.last n))

/-- Weighted real change of variables for a finite piecewise C¹ nondecreasing map,
with arbitrary interval-integrable complex integrand and possibly flat pieces. -/
theorem weighted_substitution : Specs.weighted_substitution_type := by
  intro φ c d n node hcd _hc hm hs hzero hlast hC1 g hg
  have hnode : ∀ i, node i ∈ Icc c d := by
    intro i
    constructor
    · rw [← hzero]
      exact hs.monotone (Fin.zero_le i)
    · rw [← hlast]
      exact hs.monotone (Fin.le_last i)
  have himage : ∀ i, φ (node i) ∈ [[φ c, φ d]] := by
    intro i
    exact mem_uIcc_of_le
      (hm (left_mem_Icc.mpr hcd) (hnode i) (hnode i).1)
      (hm (hnode i) (right_mem_Icc.mpr hcd) (hnode i).2)
  have hgi : ∀ i : Fin n,
      IntervalIntegrable g volume (φ (node i.castSucc)) (φ (node i.succ)) := by
    intro i
    exact hg.mono_set (uIcc_subset_uIcc (himage i.castSucc) (himage i.succ))
  have hpieces : ∀ i : Fin n,
      IntervalIntegrable (fun t => deriv φ t • g (φ t)) volume
          (node i.castSucc) (node i.succ) ∧
        (∫ t in node i.castSucc..node i.succ, deriv φ t • g (φ t)) =
          ∫ s in φ (node i.castSucc)..φ (node i.succ), g s := by
    intro i
    exact weighted_substitution_piece (hs i.castSucc_lt_succ).le (hC1 i)
      (hm.mono (Icc_subset_Icc (hnode i.castSucc).1 (hnode i.succ).2)) (hgi i)
  obtain ⟨hi, _, heq⟩ := weighted_substitution_partition
    (fun t => deriv φ t • g (φ t)) g n node (fun i => φ (node i))
    (fun i => (hpieces i).1) hgi (fun i => (hpieces i).2)
  simpa only [hzero, hlast] using And.intro hi heq

end D12Complex.Ch03.PC1MonotoneSubstitution
