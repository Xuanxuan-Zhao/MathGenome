import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.ApproximateSpectrumBoundary
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.Conventions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08ClosedRange
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.ByContra

/-! The approximate-point conclusions of `fa2:p2:local-spectrum` work over
both original scalar fields. The proofs below use `RCLike` so that the real
specializations use real operators, their intrinsic real spectra, and frontier
in ℝ. No nontriviality or spectral nonemptiness is assumed. -/

namespace ExpandedFA.Fredholm.ApproximateSpectrumBoundary

open Filter Set
open scoped Topology
open BanachAlgebra

open Specs.ExpandedFA.Fredholm.ApproximateSpectrumBoundary

universe u v

variable {𝕜 : Type v} [RCLike 𝕜]

/-- Failure of unit-sphere approximation is precisely a norm lower bound.
This step uses no completeness and includes the zero space. -/
theorem not_approximate_iff_bound {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (T : X →L[𝕜] X) (z : 𝕜) :
    z ∉ approximatePointSpectrum 𝕜 X T ↔
      ∃ C : ℝ, 0 < C ∧ ∀ x : X, ‖x‖ ≤ C * ‖T x - z • x‖ := by
  change (¬ ∀ ε : ℝ, 0 < ε → ∃ x : X, ‖x‖ = 1 ∧ ‖T x - z • x‖ < ε) ↔ _
  constructor
  · intro h
    push Not at h
    obtain ⟨ε, hε, h⟩ := h
    refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y := (algebraMap ℝ 𝕜 ‖x‖⁻¹) • x
    have hy : ‖y‖ = 1 := by simp [y, norm_smul, inv_mul_cancel₀ hxpos.ne']
    have hb := h y hy
    have heq : ‖T y - z • y‖ = ‖x‖⁻¹ * ‖T x - z • x‖ := by
      let A : X →L[𝕜] X := T - z • (1 : X →L[𝕜] X)
      change ‖A ((algebraMap ℝ 𝕜 ‖x‖⁻¹) • x)‖ = _
      rw [A.map_smul, norm_smul]
      simp [A]
    rw [heq, ← div_eq_inv_mul, le_div_iff₀ hxpos] at hb
    exact (le_inv_mul_iff₀ hε).mpr hb
  · rintro ⟨C, hC, h⟩ hap
    obtain ⟨x, hx, hxres⟩ := hap C⁻¹ (inv_pos.mpr hC)
    have hb := h x
    rw [hx] at hb
    have := (mul_lt_mul_of_pos_left hxres hC)
    rw [mul_inv_cancel₀ hC.ne'] at this
    exact (not_lt_of_ge hb) this

theorem unit_sequence_rclike {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (T : X →L[𝕜] X) (z : 𝕜) :
    z ∈ approximatePointSpectrum 𝕜 X T ↔
      ∃ x : ℕ → X, (∀ n, ‖x n‖ = 1) ∧
        Tendsto (fun n => T (x n) - z • x n) atTop (𝓝 0) := by
  constructor
  · intro h
    choose x hx hres using fun n : ℕ => h ((n : ℝ) + 1)⁻¹ (by positivity)
    refine ⟨x, hx, ?_⟩
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => (hres n).le)
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · rintro ⟨x, hx, hlim⟩ ε hε
    have he := (tendsto_zero_iff_norm_tendsto_zero.mp hlim).eventually (gt_mem_nhds hε)
    obtain ⟨n, hn⟩ := he.exists
    exact ⟨x n, hx n, hn⟩

theorem closed_range_complement_rclike {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (T : X →L[𝕜] X) (z : 𝕜) :
    z ∉ approximatePointSpectrum 𝕜 X T ↔
      Function.Injective (T - z • (1 : X →L[𝕜] X)) ∧
        IsClosed (Set.range (T - z • (1 : X →L[𝕜] X))) := by
  rw [not_approximate_iff_bound]
  let A : X →L[𝕜] X := T - z • (1 : X →L[𝕜] X)
  change (∃ C : ℝ, 0 < C ∧ ∀ x : X, ‖x‖ ≤ C * ‖A x‖) ↔
    Function.Injective A ∧ IsClosed (Set.range A)
  constructor
  · rintro ⟨C, hC, hb⟩
    obtain ⟨hi, hc, _⟩ := P1.C08ClosedRange.bounded_below_closed_range 𝕜 X X A C hC hb
    exact ⟨hi, hc⟩
  · rintro ⟨hi, hc⟩
    exact (P1.C08ClosedRange.injective_closed_range_iff 𝕜 X X A hi).mp hc

/-- Neumann inversion excludes spectral points from the inverse-norm disk
around any resolvent point. In particular the product below is at least one. -/
theorem resolvent_lower_bound_rclike {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (T : X →L[𝕜] X) (z w : 𝕜)
    (hz : z ∈ spectrum 𝕜 T) (hw : w ∈ resolventSet 𝕜 T) :
    1 ≤ ‖w - z‖ * ‖resolvent T w‖ := by
  change ¬ IsUnit (algebraMap 𝕜 (X →L[𝕜] X) z - T) at hz
  change w ∈ resolventSet 𝕜 T at hw
  by_contra! hsmall
  have hs : ‖-((z - w) • resolvent T w)‖ < 1 := by
    simpa only [norm_neg, norm_smul, norm_sub_rev z w] using hsmall
  have hi : IsUnit (1 + (z - w) • resolvent T w) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hs
  have heq : (algebraMap 𝕜 (X →L[𝕜] X) z - T) * resolvent T w =
      1 + (z - w) • resolvent T w := by
    have he : algebraMap 𝕜 (X →L[𝕜] X) z - T =
        (algebraMap 𝕜 (X →L[𝕜] X) w - T) + (z - w) • (1 : X →L[𝕜] X) := by
      simp only [Algebra.algebraMap_eq_smul_one, sub_smul]
      abel
    rw [he, add_mul, smul_mul_assoc, one_mul]
    rw [show (algebraMap 𝕜 (X →L[𝕜] X) w - T) * resolvent T w = 1 from
      Ring.mul_inverse_cancel _ hw]
  rw [← heq] at hi
  exact hz (((spectrum.isUnit_resolvent.mp hw).mul_right_iff).mp hi)

/-- The quantitative bound makes divergence explicit for every resolvent
sequence approaching a boundary point; bounded subsequences cannot occur. -/
theorem boundary_resolvent_blowup_rclike {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (T : X →L[𝕜] X) (z : 𝕜)
    (hz : z ∈ frontier (spectrum 𝕜 T)) (w : ℕ → 𝕜)
    (hw : ∀ n, w n ∈ resolventSet 𝕜 T) (hlim : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => ‖resolvent T (w n)‖) atTop atTop := by
  have hzspec : z ∈ spectrum 𝕜 T :=
    (spectrum.isClosed (𝕜 := 𝕜) T).closure_eq ▸ frontier_subset_closure hz
  have hnorm : Tendsto (fun n => ‖w n - z‖) atTop (𝓝 0) := by
    simpa using (hlim.sub_const z).norm
  apply tendsto_atTop.mpr
  intro b
  have hε : 0 < (|b| + 1)⁻¹ := by positivity
  filter_upwards [hnorm.eventually (gt_mem_nhds hε)] with n hn
  have hl := resolvent_lower_bound_rclike T z (w n) hzspec (hw n)
  change 1 ≤ ‖w n - z‖ * ‖resolvent T (w n)‖ at hl
  change b ≤ ‖resolvent T (w n)‖
  by_contra! hb
  have hbn : b ≤ |b| + 1 := by linarith [le_abs_self b]
  have hbpos : 0 < |b| + 1 := by positivity
  have hmul : ‖w n - z‖ * (|b| + 1) < 1 := by
    exact (lt_inv_mul_iff₀' hbpos).mp (by simpa using hn)
  have hp := mul_le_mul_of_nonneg_left (hb.le.trans hbn) (norm_nonneg (w n - z))
  linarith

/-- A lower bound at z bounds the resolvent uniformly in a sufficiently
small neighborhood, independently of surjectivity at z. -/
theorem resolvent_norm_le_of_bound {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (T : X →L[𝕜] X) (z w : 𝕜) (C : ℝ) (hC : 0 < C)
    (hb : ∀ x : X, ‖x‖ ≤ C * ‖T x - z • x‖)
    (hw : w ∈ resolventSet 𝕜 T) (hclose : C * ‖w - z‖ < 1 / 2) :
    ‖resolvent T w‖ ≤ 2 * C := by
  refine (resolvent T w).opNorm_le_bound (by positivity) ?_
  intro y
  let x := resolvent T w y
  have hx : w • x - T x = y := by
    change ((algebraMap 𝕜 (X →L[𝕜] X) w - T) * resolvent T w) y = y
    rw [show (algebraMap 𝕜 (X →L[𝕜] X) w - T) * resolvent T w = 1 from
      Ring.mul_inverse_cancel _ hw]
    rfl
  have he : T x - z • x = (w - z) • x - y := by
    rw [sub_smul, ← hx]
    abel
  have hres : ‖T x - z • x‖ ≤ ‖w - z‖ * ‖x‖ + ‖y‖ := by
    rw [he]
    simpa only [norm_smul] using norm_sub_le ((w - z) • x) y
  have hbound := (hb x).trans (mul_le_mul_of_nonneg_left hres hC.le)
  have hnx := norm_nonneg x
  change ‖x‖ ≤ 2 * C * ‖y‖
  nlinarith

/-- A boundary point has approaching resolvent points. If it had a lower
bound, their inverses would be uniformly bounded, contradicting blow-up. -/
theorem boundary_inclusion_rclike {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (T : X →L[𝕜] X) :
    frontier (spectrum 𝕜 T) ⊆ approximatePointSpectrum 𝕜 X T := by
  intro z hz
  by_contra hznot
  obtain ⟨C, hC, hb⟩ := (not_approximate_iff_bound T z).mp hznot
  have hzfront : z ∈ frontier (spectrum 𝕜 T) := hz
  rw [frontier_eq_closure_inter_closure] at hzfront
  have hzcl : z ∈ closure (spectrum 𝕜 T)ᶜ := hzfront.2
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp hzcl
  have hwres (n : ℕ) : w n ∈ resolventSet 𝕜 T := spectrum.notMem_iff.mp (hw n)
  have hnorm : Tendsto (fun n => C * ‖w n - z‖) atTop (𝓝 0) := by
    simpa using ((hlim.sub_const z).norm.const_mul C)
  have hlarge := (boundary_resolvent_blowup_rclike T z hz w hwres hlim).eventually
    (eventually_gt_atTop (2 * C))
  have hsmall := hnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨n, hnlarge, hnsmall⟩ := (hlarge.and hsmall).exists
  exact (not_lt_of_ge (resolvent_norm_le_of_bound T z (w n) C hC hb (hwres n) hnsmall))
    hnlarge


/-- Complex and real specializations retain their original scalar fields. -/
theorem unit_sequence : UnitSequence.{u} := by
  intro X _ _ T z
  exact unit_sequence_rclike T z

theorem closed_range_complement : ClosedRangeComplement.{u} := by
  intro X _ _ _ T z
  exact closed_range_complement_rclike T z

theorem resolvent_lower_bound : ResolventLowerBound.{u} := by
  intro X _ _ _ T z w hz hw
  exact resolvent_lower_bound_rclike T z w hz hw

theorem boundary_resolvent_blowup : BoundaryResolventBlowup.{u} := by
  intro X _ _ _ T z hz w hw hlim
  exact boundary_resolvent_blowup_rclike T z hz w hw hlim

theorem boundary_inclusion : BoundaryInclusion.{u} := by
  intro X _ _ _ T
  exact boundary_inclusion_rclike T

theorem real_unit_sequence : RealUnitSequence.{u} := by
  intro X _ _ T z
  exact unit_sequence_rclike T z

theorem real_closed_range_complement : RealClosedRangeComplement.{u} := by
  intro X _ _ _ T z
  exact closed_range_complement_rclike T z

theorem real_boundary_inclusion : RealBoundaryInclusion.{u} := by
  intro X _ _ _ T
  exact boundary_inclusion_rclike T

end ExpandedFA.Fredholm.ApproximateSpectrumBoundary
