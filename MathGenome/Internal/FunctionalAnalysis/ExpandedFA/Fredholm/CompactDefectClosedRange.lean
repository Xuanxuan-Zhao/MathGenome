import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.CompactDefectClosedRange
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.Definitions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic

/-! Compact defects on arbitrary real or complex normed spaces.
No completeness of the ambient space or its quotient is used.
Compactness always supplies a limit in the original space. -/
namespace ExpandedFA.Fredholm
open Filter
open scoped Topology
universe u v
variable {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕂 E]

/-- Extract an image subsequence with limit in the actual target. -/
private theorem compact_bounded_subsequence
    (K : E →ₗ[𝕂] E) (hK : Compactness.IsCompactLinearMap K)
    (x : ℕ → E) (hx : Bornology.IsBounded (Set.range x)) :
    ∃ (y : E) (k : ℕ → ℕ), StrictMono k ∧
      Tendsto (fun n => K (x (k n))) atTop (𝓝 y) := by
  have hc := (Compactness.compact_iff_bounded_images K).mp hK (Set.range x) hx
  obtain ⟨y, _, k, hk, hlim⟩ := hc.tendsto_subseq (x := fun n => K (x n))
    (fun n => subset_closure ⟨x n, Set.mem_range_self n, rfl⟩)
  exact ⟨y, k, hk, hlim⟩

/-- Nonzero eigenspaces of compact operators, including on incomplete spaces. -/
theorem compact_nonzero_eigenspace_closed_finite_dimensional
    (K : E →L[𝕂] E) (hK : Compactness.IsCompactLinearMap K.toLinearMap)
    (μ : 𝕂) (hμ : μ ≠ 0) :
    IsClosed (LinearMap.ker (μ • LinearMap.id - K.toLinearMap) : Set E) ∧
    FiniteDimensional 𝕂 (LinearMap.ker (μ • LinearMap.id - K.toLinearMap)) := by
  let M : Submodule 𝕂 E := LinearMap.ker (μ • LinearMap.id - K.toLinearMap)
  have hclosed : IsClosed (M : Set E) :=
    (μ • ContinuousLinearMap.id 𝕂 E - K).isClosed_ker
  have heigen (x : E) (hx : x ∈ M) : K x = μ • x := by
    exact (sub_eq_zero.mp hx).symm
  have hinv : ∀ x ∈ M, K.toLinearMap x ∈ M := by
    intro x hx
    change K x ∈ M
    rw [heigen x hx]
    exact M.smul_mem μ hx
  have hcompact := (Compactness.compact_iff_isCompactOperator K.toLinearMap).mp hK
  have hrestrict : IsCompactOperator (K.toLinearMap.restrict hinv) :=
    hcompact.restrict hinv hclosed
  have hscalar : K.toLinearMap.restrict hinv = μ • (LinearMap.id : M →ₗ[𝕂] M) := by
    ext x
    exact heigen x x.property
  rw [hscalar] at hrestrict
  have hid : IsCompactOperator (id : M → M) :=
    (IsCompactOperator.smul_iff₀ hμ).mp hrestrict
  let : LocallyCompactSpace M := LocallyCompactSpace.of_isCompactOperator_id hid
  exact ⟨hclosed, FiniteDimensional.of_locallyCompactSpace 𝕂⟩

/-- The case `μ = 1`: the nullspace of `I - K` is closed and finite dimensional. -/
theorem identity_sub_compact_kernel_closed_finite_dimensional
    (K : E →L[𝕂] E) (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    IsClosed (LinearMap.ker (LinearMap.id - K.toLinearMap) : Set E) ∧
    FiniteDimensional 𝕂 (LinearMap.ker (LinearMap.id - K.toLinearMap)) := by
  have h := compact_nonzero_eigenspace_closed_finite_dimensional K hK 1 one_ne_zero
  rw [one_smul] at h
  exact h


/-- A failure of a lower bound modulo the kernel gives bounded normalized
representatives with arbitrarily small images. -/
private theorem normalized_kernel_counterexample (A : E →L[𝕂] E)
    (h : ∀ c : ℝ, 0 < c → ∃ x : E,
      ‖A x‖ < c * ‖A.toLinearMap.ker.mkQ x‖) :
    ∀ ε : ℝ, 0 < ε → ∃ x : E,
      ‖A.toLinearMap.ker.mkQ x‖ = 1 ∧ ‖x‖ < 2 ∧ ‖A x‖ < ε := by
  intro ε hε
  let N := A.toLinearMap.ker
  obtain ⟨y, hy⟩ := h ε hε
  have hd : 0 < ‖N.mkQ y‖ := by
    by_contra hd
    have : ‖N.mkQ y‖ = 0 := le_antisymm (le_of_not_gt hd) (norm_nonneg _)
    simp only [N, this, mul_zero] at hy
    exact (norm_nonneg _).not_gt hy
  let a : 𝕂 := RCLike.ofReal (‖N.mkQ y‖⁻¹)
  let z : E := a • y
  have ha : ‖a‖ = ‖N.mkQ y‖⁻¹ := by
    simp [a]
  have hz : ‖N.mkQ z‖ = 1 := by
    simp only [z, map_smul, norm_smul, ha]
    exact inv_mul_cancel₀ hd.ne'
  have hzA : ‖A z‖ < ε := by
    calc
      ‖A z‖ = ‖N.mkQ y‖⁻¹ * ‖A y‖ := by simp only [z, map_smul, norm_smul, ha]
      _ < ‖N.mkQ y‖⁻¹ * (ε * ‖N.mkQ y‖) :=
        mul_lt_mul_of_pos_left hy (inv_pos.mpr hd)
      _ = ε := by rw [mul_left_comm, inv_mul_cancel₀ hd.ne', mul_one]
  obtain ⟨x, hx, hxnorm⟩ := Submodule.Quotient.norm_mk_lt (N.mkQ z) zero_lt_one
  have hxq : N.mkQ x = N.mkQ z := hx
  have hxA : A x = A z := by
    exact congrArg (N.liftQ A.toLinearMap le_rfl) hxq
  exact ⟨x, by rw [hxq, hz], by simpa only [hz, one_add_one_eq_two] using hxnorm,
    by rwa [hxA]⟩

/-- The quantitative distance estimate for `A = I - K`.
All distances and limits use the given norm topology. -/
theorem identity_sub_compact_distance_estimate
    (K : E →L[𝕂] E) (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : E,
      c * Metric.infDist x
        (LinearMap.ker (LinearMap.id - K.toLinearMap) : Set E) ≤
      ‖(ContinuousLinearMap.id 𝕂 E - K) x‖ := by
  let A := ContinuousLinearMap.id 𝕂 E - K
  let N := A.toLinearMap.ker
  have hdist (x : E) : ‖N.mkQ x‖ = Metric.infDist x (N : Set E) :=
    QuotientAddGroup.norm_mk x
  change ∃ c : ℝ, 0 < c ∧ ∀ x : E, c * Metric.infDist x (N : Set E) ≤ ‖A x‖
  simp_rw [← hdist]
  by_contra h
  push Not at h
  have hnormalized := normalized_kernel_counterexample A h
  have hex (n : ℕ) : ∃ x : E, ‖N.mkQ x‖ = 1 ∧ ‖x‖ < 2 ∧
      ‖A x‖ < 1 / ((n : ℝ) + 1) :=
    hnormalized _ (by positivity)
  choose x hxq hxnorm hxA using hex
  have hb : Bornology.IsBounded (Set.range x) :=
    (Metric.isBounded_closedBall (x := (0 : E)) (r := (2 : ℝ))).subset
      (Set.range_subset_iff.mpr (fun n => by
        simpa only [Metric.mem_closedBall, dist_zero_right] using (hxnorm n).le))
  have hAzero : Tendsto (fun n => A (x n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hxA n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨y, k, hk, hKy⟩ :=
    compact_bounded_subsequence K.toLinearMap hK x hb
  have hxy : Tendsto (fun n => x (k n)) atTop (𝓝 y) := by
    have hsum := (hAzero.comp hk.tendsto_atTop).add hKy
    change Tendsto (fun n => (x (k n) - K (x (k n))) + K (x (k n)))
      atTop (𝓝 (0 + y)) at hsum
    simpa only [sub_add_cancel, zero_add] using hsum
  have hyA : A y = 0 :=
    tendsto_nhds_unique (A.continuous.continuousAt.tendsto.comp hxy)
      (hAzero.comp hk.tendsto_atTop)
  have hyN : y ∈ N := hyA
  have hyq : ‖N.mkQ y‖ = 0 := by
    change ‖(Submodule.Quotient.mk y : E ⧸ N)‖ = 0
    rw [(Submodule.Quotient.mk_eq_zero N).mpr hyN, norm_zero]
  have hqd : Tendsto (fun n => Metric.infDist (x (k n)) (N : Set E)) atTop
      (𝓝 (Metric.infDist y (N : Set E))) :=
    (Metric.continuous_infDist_pt (N : Set E)).continuousAt.tendsto.comp hxy
  have hqone : Metric.infDist y (N : Set E) = 1 := by
    apply tendsto_nhds_unique hqd
    simpa only [← hdist, hxq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have : (0 : ℝ) = 1 := by rwa [← hdist, hyq] at hqone
  exact zero_ne_one this


/-- Bounded representatives modulo the kernel and compactness give a limit
in `E` itself. No completeness of either `E` or its quotient is used. -/
theorem identity_sub_compact_closed_range
    (K : E →L[𝕂] E) (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    IsClosed (LinearMap.range (ContinuousLinearMap.id 𝕂 E - K).toLinearMap : Set E) := by
  let A := ContinuousLinearMap.id 𝕂 E - K
  let N := A.toLinearMap.ker
  obtain ⟨c, hc, hbound⟩ := identity_sub_compact_distance_estimate K hK
  have hquot (x : E) : c * ‖N.mkQ x‖ ≤ ‖A x‖ := by
    rw [show ‖N.mkQ x‖ = Metric.infDist x (N : Set E) from QuotientAddGroup.norm_mk x]
    exact hbound x
  apply IsSeqClosed.isClosed
  intro y b hy hlim
  choose x hx using hy
  have hAx (n : ℕ) : A (x n) = y n := hx n
  have hrep (n : ℕ) : ∃ z : E, N.mkQ z = N.mkQ (x n) ∧
      ‖z‖ < ‖N.mkQ (x n)‖ + 1 :=
    Submodule.Quotient.norm_mk_lt (N.mkQ (x n)) zero_lt_one
  choose z hzq hznorm using hrep
  have hAz (n : ℕ) : A (z n) = y n := by
    calc
      A (z n) = A (x n) := congrArg (N.liftQ A.toLinearMap le_rfl) (hzq n)
      _ = y n := hAx n
  obtain ⟨M, hM⟩ := hlim.cauchySeq.isBounded_range.exists_norm_le
  have hbz : Bornology.IsBounded (Set.range z) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M / c + 1, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hq : ‖N.mkQ (x n)‖ ≤ M / c := by
      apply (le_div_iff₀ hc).mpr
      calc
        ‖N.mkQ (x n)‖ * c = c * ‖N.mkQ (x n)‖ := mul_comm _ _
        _ ≤ ‖A (x n)‖ := hquot (x n)
        _ ≤ M := by rw [hAx]; exact hM _ (Set.mem_range_self n)
    exact (hznorm n).le.trans (add_le_add hq le_rfl)
  obtain ⟨w, k, hk, hKw⟩ :=
    compact_bounded_subsequence K.toLinearMap hK z hbz
  have hzlim : Tendsto (fun n => z (k n)) atTop (𝓝 (b + w)) := by
    have hs := (hlim.comp hk.tendsto_atTop).add hKw
    convert hs using 1
    ext n
    change z (k n) = y (k n) + K (z (k n))
    rw [← hAz]
    exact (sub_add_cancel (z (k n)) (K (z (k n)))).symm
  have hAb : A (b + w) = b := by
    apply tendsto_nhds_unique (A.continuous.continuousAt.tendsto.comp hzlim)
    simpa only [Function.comp_def, hAz] using hlim.comp hk.tendsto_atTop
  exact ⟨b + w, hAb⟩

/-- The compact polynomial `I - (I - K)^m`. A recursion in the same
bounded-linear composition algebra avoids any completeness assumption. -/
theorem compact_identity_sub_power
    (K : E →L[𝕂] E) (hK : Compactness.IsCompactLinearMap K.toLinearMap) (m : ℕ) :
    Compactness.IsCompactLinearMap
      (ContinuousLinearMap.id 𝕂 E - (ContinuousLinearMap.id 𝕂 E - K) ^ m).toLinearMap := by
  induction m with
  | zero =>
    have heq : ContinuousLinearMap.id 𝕂 E - (ContinuousLinearMap.id 𝕂 E - K) ^ 0 = 0 := by
      ext x
      simp
    rw [heq]
    exact (Compactness.compact_iff_isCompactOperator _).mpr isCompactOperator_zero
  | succ m ih =>
    let A := ContinuousLinearMap.id 𝕂 E - K
    have hnative := (Compactness.compact_iff_isCompactOperator K.toLinearMap).mp hK
    have hi := (Compactness.compact_iff_isCompactOperator _).mp ih
    have hadd : Compactness.IsCompactLinearMap
        ((ContinuousLinearMap.id 𝕂 E - A ^ m) + (A ^ m).comp K).toLinearMap :=
      (Compactness.compact_iff_isCompactOperator _).mpr (hi.add (hnative.clm_comp (A ^ m)))
    have heq : ContinuousLinearMap.id 𝕂 E - A ^ (m + 1) =
        (ContinuousLinearMap.id 𝕂 E - A ^ m) + (A ^ m).comp K := by
      rw [pow_succ]
      ext x
      change x - (A ^ m) (x - K x) = (x - (A ^ m) x) + (A ^ m) (K x)
      rw [map_sub]
      abel
    rw [heq]
    exact hadd

/-- Every positive power has closed, finite-dimensional kernel and closed range. -/
theorem identity_sub_compact_powers_closed_range_finite_kernel
    (K : E →L[𝕂] E) (hK : Compactness.IsCompactLinearMap K.toLinearMap)
    (m : ℕ) (_hm : 1 ≤ m) :
    IsClosed (LinearMap.ker ((ContinuousLinearMap.id 𝕂 E - K) ^ m).toLinearMap : Set E) ∧
    FiniteDimensional 𝕂 (LinearMap.ker ((ContinuousLinearMap.id 𝕂 E - K) ^ m).toLinearMap) ∧
    IsClosed (LinearMap.range ((ContinuousLinearMap.id 𝕂 E - K) ^ m).toLinearMap : Set E) := by
  let Km := ContinuousLinearMap.id 𝕂 E - (ContinuousLinearMap.id 𝕂 E - K) ^ m
  have hKm := compact_identity_sub_power K hK m
  have hker := identity_sub_compact_kernel_closed_finite_dimensional Km hKm
  have hran := identity_sub_compact_closed_range Km hKm
  have heq : ContinuousLinearMap.id 𝕂 E - Km = (ContinuousLinearMap.id 𝕂 E - K) ^ m :=
    sub_sub_cancel _ _
  change IsClosed (LinearMap.ker (ContinuousLinearMap.id 𝕂 E - Km).toLinearMap : Set E) ∧
    FiniteDimensional 𝕂 (LinearMap.ker (ContinuousLinearMap.id 𝕂 E - Km).toLinearMap) at hker
  rw [heq] at hker hran
  exact ⟨hker.1, hker.2, hran⟩


/-- All assigned assertions for a compact algebraic linear map. Continuity is
obtained from compactness, with no extra hypothesis on K or on completeness. -/
theorem identity_sub_compact_linear : CompactDefectClosedRangeSpec.LinearCompactDefect := by
  intro 𝕂 _ E _ _ K hK
  let T : E →L[𝕂] E :=
    ⟨K, ((Compactness.compact_iff_isCompactOperator K).mp hK).continuous⟩
  have hT : Compactness.IsCompactLinearMap T.toLinearMap := hK
  have hker := identity_sub_compact_kernel_closed_finite_dimensional T hT
  have hdist := identity_sub_compact_distance_estimate T hT
  have hran := identity_sub_compact_closed_range T hT
  refine ⟨hker.2, hdist, hran, ?_⟩
  intro n hn
  obtain ⟨_, hkn, hrn⟩ := identity_sub_compact_powers_closed_range_finite_kernel T hT n hn
  have heq : ((ContinuousLinearMap.id 𝕂 E - T) ^ n).toLinearMap =
      (LinearMap.id - K) ^ n := by
    rw [ContinuousLinearMap.toLinearMap_pow]
    rfl
  rw [heq] at hkn hrn
  exact ⟨hkn, hrn⟩

end ExpandedFA.Fredholm
