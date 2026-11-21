import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.CompactDefectStabilization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactDefectClosedRange
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Batteries.Tactic.OpenPrivate

/-! Stabilization and bounded Riesz decomposition of I - K on a normed space.
No completeness hypothesis is used, including for the inverse on the stable range. -/
namespace ExpandedFA.Fredholm
open Filter
open scoped Topology
open CompactDefectStabilizationSpec
open private compact_bounded_subsequence from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactDefectClosedRange

universe u v
variable {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕂 E]

/-- Continuous linear coordinates provide unique bounded projections. -/
lemma bounded_coordinates_of_isTopCompl {M N : Submodule 𝕂 E}
    (h : Submodule.IsTopCompl M N) :
    ∃ (P : E →L[𝕂] M) (Q : E →L[𝕂] N),
      ∀ x, (P x : E) + (Q x : E) = x ∧
        ∀ (m : M) (n : N), (m : E) + (n : E) = x → m = P x ∧ n = Q x := by
  refine ⟨M.projectionOntoL N h, N.projectionOntoL M h.symm, ?_⟩
  intro x
  refine ⟨Submodule.projectionL_add_projectionL_eq_self h x, ?_⟩
  intro m n hmn
  constructor
  · simpa using congrArg (M.projectionOntoL N h) hmn
  · simpa using congrArg (N.projectionOntoL M h.symm) hmn

theorem power_chains : CompactDefectStabilizationSpec.Chains := by
  intro 𝕂 _ E _ _ K
  exact ⟨by simp [kernelChain, Module.End.one_eq_id], by simp [rangeChain, Module.End.one_eq_id],
    ((ContinuousLinearMap.id 𝕂 E - K).toLinearMap).iterateKer.monotone,
    ((ContinuousLinearMap.id 𝕂 E - K).toLinearMap).iterateRange.monotone⟩

/-- Once two consecutive ranges coincide, applying the map preserves equality. -/
lemma range_pow_constant (f : E →ₗ[𝕂] E) {m : ℕ}
    (h : LinearMap.range (f ^ m) = LinearMap.range (f ^ (m + 1))) :
    ∀ n, m ≤ n → LinearMap.range (f ^ n) = LinearMap.range (f ^ m) := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp
  | succ k ih =>
    change f.iterateRange (m + k + 1) = f.iterateRange m
    rw [LinearMap.iterateRange_succ]
    change (LinearMap.range (f ^ (m + k))).map f = _
    rw [ih (by omega)]
    exact (LinearMap.iterateRange_succ (f := f) (n := m)).symm.trans h.symm

theorem power_chain_propagation : CompactDefectStabilizationSpec.Propagation := by
  intro 𝕂 _ E _ _ K m
  let f := (ContinuousLinearMap.id 𝕂 E - K).toLinearMap
  constructor
  · intro h n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (Module.End.ker_pow_constant h k).symm
  · exact range_pow_constant f

/-- Riesz's lemma inside the larger subspace, with distances measured in `E`. -/
lemma exists_unit_mem_separated {P Q : Submodule 𝕂 E} (hPQ : P < Q)
    (hP : IsClosed (P : Set E)) :
    ∃ x ∈ Q, ‖x‖ = 1 ∧ ∀ y ∈ P, (1 / 2 : ℝ) ≤ ‖x - y‖ := by
  have hproper : ∃ x : Q, x ∉ P.comap Q.subtype := by
    obtain ⟨x, hxQ, hxP⟩ := IsConcreteLE.exists_of_lt hPQ
    exact ⟨⟨x, hxQ⟩, hxP⟩
  obtain ⟨x, _, hxnorm, hx⟩ := _root_.riesz_lemma_of_lt_one
    (hP.preimage continuous_subtype_val) hproper (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨x, x.property, hxnorm, fun y hy => ?_⟩
  exact hx ⟨y, hPQ.le hy⟩ hy

/-- A compact map cannot send a bounded sequence to separated points. -/
lemma compact_not_separated (K : E →L[𝕂] E)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) (x : ℕ → E)
    (hx : ∀ n, ‖x n‖ = 1)
    (hsep : ∀ m n, m < n → (1 / 2 : ℝ) ≤ ‖K (x m) - K (x n)‖) : False := by
  have hb : Bornology.IsBounded (Set.range x) := by
    have hb0 : Bornology.IsBounded (Metric.closedBall (0 : E) 1) :=
      Metric.isBounded_closedBall
    apply hb0.subset
    rintro _ ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using (hx n).le
  obtain ⟨y, k, hk, hlim⟩ :=
    compact_bounded_subsequence K.toLinearMap hK x hb
  have hc := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hc
  obtain ⟨N, hN⟩ := hc (1 / 2) (by norm_num)
  have hlt := hN (N + 1) (by omega)
  have hge := hsep (k N) (k (N + 1)) (hk (by omega))
  rw [dist_eq_norm, norm_sub_rev] at hlt
  exact hlt.not_ge hge

/-- The kernels cannot increase strictly at every stage. -/
theorem exists_kernel_power_eq_succ (K : E →L[𝕂] E)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    ∃ m, kernelChain K m = kernelChain K (m + 1) := by
  classical
  by_contra! h
  let f := (ContinuousLinearMap.id 𝕂 E - K).toLinearMap
  have hmono := (power_chains K).2.2.1
  have hchoose (n : ℕ) : ∃ x ∈ kernelChain K (n + 1), ‖x‖ = 1 ∧
      ∀ y ∈ kernelChain K n, (1 / 2 : ℝ) ≤ ‖x - y‖ := by
    apply exists_unit_mem_separated (lt_of_le_of_ne (hmono (Nat.le_succ n)) (h n))
    have hc := ((ContinuousLinearMap.id 𝕂 E - K) ^ n).isClosed_ker
    simpa [kernelChain, ContinuousLinearMap.toLinearMap_pow] using hc
  choose x hx hnorm hfar using hchoose
  have hAx (n : ℕ) : f (x n) ∈ kernelChain K n := by
    change (f ^ n) (f (x n)) = 0
    have hn := hx n
    change (f ^ (n + 1)) (x n) = 0 at hn
    simpa only [pow_succ, Module.End.mul_apply] using hn
  apply compact_not_separated K hK x hnorm
  intro j n hjn
  have hxj : x j ∈ kernelChain K n := hmono hjn (hx j)
  have hAxj : f (x j) ∈ kernelChain K n := hmono hjn.le (hAx j)
  have hKxj : K (x j) ∈ kernelChain K n := by
    have heq : K (x j) = x j - f (x j) := by simp [f]
    rw [heq]
    exact (kernelChain K n).sub_mem hxj hAxj
  have hs := hfar n (f (x n) + K (x j)) ((kernelChain K n).add_mem (hAx n) hKxj)
  have heq : x n - (f (x n) + K (x j)) = K (x n) - K (x j) := by
    simp [f]
    abel
  rw [heq, norm_sub_rev] at hs
  exact hs

/-- The closed ranges cannot decrease strictly at every stage. -/
theorem exists_range_power_eq_succ (K : E →L[𝕂] E)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    ∃ m, rangeChain K m = rangeChain K (m + 1) := by
  classical
  by_contra! h
  let f := (ContinuousLinearMap.id 𝕂 E - K).toLinearMap
  have hanti := (power_chains K).2.2.2
  have hchoose (n : ℕ) : ∃ x ∈ rangeChain K n, ‖x‖ = 1 ∧
      ∀ y ∈ rangeChain K (n + 1), (1 / 2 : ℝ) ≤ ‖x - y‖ := by
    apply exists_unit_mem_separated
      (lt_of_le_of_ne (hanti (Nat.le_succ n)) (h n).symm)
    have hc := (identity_sub_compact_powers_closed_range_finite_kernel K hK
      (n + 1) (by omega)).2.2
    simpa [rangeChain, ContinuousLinearMap.toLinearMap_pow] using hc
  choose x hx hnorm hfar using hchoose
  have hAx (n : ℕ) : f (x n) ∈ rangeChain K (n + 1) := by
    obtain ⟨z, hz⟩ := hx n
    exact ⟨z, by rw [pow_succ', Module.End.mul_apply, hz]⟩
  apply compact_not_separated K hK x hnorm
  intro n j hnj
  have hxj : x j ∈ rangeChain K (n + 1) := hanti hnj (hx j)
  have hAxj : f (x j) ∈ rangeChain K (n + 1) :=
    hanti (Nat.succ_le_succ hnj.le) (hAx j)
  have hKxj : K (x j) ∈ rangeChain K (n + 1) := by
    have heq : K (x j) = x j - f (x j) := by simp [f]
    rw [heq]
    exact (rangeChain K (n + 1)).sub_mem hxj hAxj
  have hs := hfar n (f (x n) + K (x j))
    ((rangeChain K (n + 1)).add_mem (hAx n) hKxj)
  have heq : x n - (f (x n) + K (x j)) = K (x n) - K (x j) := by
    simp [f]
    abel
  rwa [heq] at hs

theorem power_chains_stabilize : CompactDefectStabilizationSpec.Stabilization := by
  intro 𝕂 _ E _ _ K hK
  obtain ⟨r, hr⟩ := exists_kernel_power_eq_succ K hK
  obtain ⟨s, hs⟩ := exists_range_power_eq_succ K hK
  exact ⟨⟨r, (power_chain_propagation K r).1 hr⟩,
    ⟨s, (power_chain_propagation K s).2 hs⟩⟩

/-- The algebraic splitting only uses stabilization at the doubled power. -/
lemma isCompl_kernel_range_of_stable (f : E →ₗ[𝕂] E) (p : ℕ)
    (hN : LinearMap.ker (f ^ (p + p)) = LinearMap.ker (f ^ p))
    (hR : LinearMap.range (f ^ (p + p)) = LinearMap.range (f ^ p)) :
    IsCompl (LinearMap.ker (f ^ p)) (LinearMap.range (f ^ p)) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hxN hxR
    obtain ⟨z, rfl⟩ := hxR
    change (f ^ p) ((f ^ p) z) = 0 at hxN
    have hz : z ∈ LinearMap.ker (f ^ (p + p)) := by
      change (f ^ (p + p)) z = 0
      simpa only [pow_add, Module.End.mul_apply] using hxN
    rw [hN] at hz
    exact hz
  · apply codisjoint_iff.mpr
    apply top_unique
    intro x _
    have hxR : (f ^ p) x ∈ LinearMap.range (f ^ (p + p)) := by
      rw [hR]
      exact ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hxR
    apply Submodule.mem_sup.mpr
    refine ⟨x - (f ^ p) z, ?_, (f ^ p) z, ⟨z, rfl⟩, sub_add_cancel _ _⟩
    change (f ^ p) (x - (f ^ p) z) = 0
    rw [map_sub, ← Module.End.mul_apply, ← pow_add, hz, sub_self]

lemma power_kernel_invariant (f : E →ₗ[𝕂] E) (p : ℕ) :
    ∀ x ∈ LinearMap.ker (f ^ p), f x ∈ LinearMap.ker (f ^ p) := by
  intro x hx
  change (f ^ p) (f x) = 0
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
  change (f ^ p) x = 0 at hx
  rw [hx, map_zero]

lemma power_range_invariant (f : E →ₗ[𝕂] E) (p : ℕ) :
    ∀ x ∈ LinearMap.range (f ^ p), f x ∈ LinearMap.range (f ^ p) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨f x, ?_⟩
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]

/-- Compactness gives the inverse bound even when the space is incomplete. -/
lemma compact_identity_sub_equiv (K : E →L[𝕂] E)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap)
    (hinj : Function.Injective (ContinuousLinearMap.id 𝕂 E - K))
    (hsurj : Function.Surjective (ContinuousLinearMap.id 𝕂 E - K)) :
    ∃ e : E ≃L[𝕂] E, ∀ x, e x = (ContinuousLinearMap.id 𝕂 E - K) x := by
  let A := ContinuousLinearMap.id 𝕂 E - K
  obtain ⟨c, hc, hbound⟩ := identity_sub_compact_distance_estimate K hK
  have hker : LinearMap.ker (LinearMap.id - K.toLinearMap) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have hb (x : E) : c * ‖x‖ ≤ ‖A x‖ := by
    simpa only [hker, Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right] using hbound x
  let e := LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩
  refine ⟨e.toContinuousLinearEquivOfBounds ‖A‖ c⁻¹
    (fun x => A.le_opNorm x) ?_, fun _ => rfl⟩
  intro y
  have he : A (e.symm y) = y := e.apply_symm_apply y
  have hb' := hb (e.symm y)
  rw [he] at hb'
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb')

/-- The restriction to a power kernel is killed by that same power. -/
lemma power_kernel_nilpotent (A : E →L[𝕂] E) (p : ℕ) :
    ∃ T : LinearMap.ker (A.toLinearMap ^ p) →L[𝕂] LinearMap.ker (A.toLinearMap ^ p),
      (∀ x, (T x : E) = A x) ∧ T ^ p = 0 := by
  let T := A.restrict (power_kernel_invariant A.toLinearMap p)
  have hpow (n : ℕ) (x : LinearMap.ker (A.toLinearMap ^ p)) :
      ((T ^ n) x : E) = (A.toLinearMap ^ n) x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change A ((T ^ n) x : E) = A ((A.toLinearMap ^ n) x)
      rw [ih]
  refine ⟨T, fun _ => rfl, ?_⟩
  ext x
  change ((T ^ p) x : E) = 0
  rw [hpow]
  exact x.property

/-- On the stable range the restricted map is bijective, by algebra alone. -/
lemma stable_range_bijective (f : E →ₗ[𝕂] E) (p : ℕ) (hp : 1 ≤ p)
    (hc : IsCompl (LinearMap.ker (f ^ p)) (LinearMap.range (f ^ p)))
    (hR : LinearMap.range (f ^ p) = LinearMap.range (f ^ (p + 1))) :
    Function.Bijective (f.restrict (power_range_invariant f p)) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    have hfx : f (x : E) = 0 := congrArg Subtype.val hx
    have hxN : (x : E) ∈ LinearMap.ker (f ^ p) := by
      apply f.iterateKer.monotone hp
      change f (x : E) = 0
      exact hfx
    have hx0 := Submodule.disjoint_def.mp hc.disjoint (x : E) hxN x.property
    exact Subtype.ext hx0
  · intro y
    have hy : (y : E) ∈ LinearMap.range (f ^ (p + 1)) := by
      rw [← hR]
      exact y.property
    obtain ⟨z, hz⟩ := hy
    refine ⟨⟨(f ^ p) z, ⟨z, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change f ((f ^ p) z) = y
    simpa only [pow_succ', Module.End.mul_apply] using hz

theorem riesz_decomposition_at_common_index : CompactDefectStabilizationSpec.AtCommonIndex := by
  intro 𝕂 _ E _ _ K hK p hp hN hR
  let A := ContinuousLinearMap.id 𝕂 E - K
  let f := A.toLinearMap
  have hN2 := (power_chain_propagation K p).1 hN (p + p) (by omega)
  have hR2 := (power_chain_propagation K p).2 hR (p + p) (by omega)
  have hc : IsCompl (kernelChain K p) (rangeChain K p) :=
    isCompl_kernel_range_of_stable f p hN2 hR2
  have hclosed := identity_sub_compact_powers_closed_range_finite_kernel K hK p hp
  have hNc : IsClosed (kernelChain K p : Set E) := by
    simpa only [kernelChain, ContinuousLinearMap.toLinearMap_pow] using hclosed.1
  have hNfin : FiniteDimensional 𝕂 (kernelChain K p) := by
    unfold kernelChain
    rw [← ContinuousLinearMap.toLinearMap_pow]
    exact hclosed.2.1
  have hRc : IsClosed (rangeChain K p : Set E) := by
    simpa only [rangeChain, ContinuousLinearMap.toLinearMap_pow] using hclosed.2.2
  let := hNfin
  have htop : Submodule.IsTopCompl (kernelChain K p) (rangeChain K p) :=
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hc.symm hRc).symm
  have hNi := power_kernel_invariant f p
  have hRi := power_range_invariant f p
  have hKi : ∀ x ∈ rangeChain K p, K x ∈ rangeChain K p := by
    intro x hx
    have heq : K x = x - f x := by simp [f, A]
    rw [heq]
    exact (rangeChain K p).sub_mem hx (hRi x hx)
  let KR : rangeChain K p →L[𝕂] rangeChain K p := K.restrict hKi
  have hKR : Compactness.IsCompactLinearMap KR.toLinearMap :=
    (Compactness.compact_iff_isCompactOperator _).mpr
      (((Compactness.compact_iff_isCompactOperator _).mp hK).restrict hKi hRc)
  have hbij := stable_range_bijective f p hp hc hR
  have heq : (ContinuousLinearMap.id 𝕂 (rangeChain K p) - KR).toLinearMap =
      f.restrict hRi := by
    ext x
    rfl
  have hbij' : Function.Bijective (ContinuousLinearMap.id 𝕂 (rangeChain K p) - KR) := by
    change Function.Bijective (ContinuousLinearMap.id 𝕂 (rangeChain K p) - KR).toLinearMap
    rwa [heq]
  obtain ⟨e, he⟩ := compact_identity_sub_equiv KR hKR hbij'.1 hbij'.2
  refine ⟨htop, hNc, hNfin, hRc,
    bounded_coordinates_of_isTopCompl htop,
    hNi, hRi, power_kernel_nilpotent A p, e, ?_⟩
  intro x
  rw [he]
  rfl

/-- Every sufficiently large exponent gives the full decomposition, with
both chains constant from one common positive cutoff. -/
theorem riesz_decomposition : CompactDefectStabilizationSpec.FullTheorem := by
  intro 𝕂 _ E _ _ K hK
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := power_chains_stabilize K hK
  let q := max (max a b) 1
  have haq : a ≤ q := (le_max_left a b).trans (le_max_left _ _)
  have hbq : b ≤ q := (le_max_right a b).trans (le_max_left _ _)
  have hq : 1 ≤ q := le_max_right _ _
  refine ⟨q, hq, ?_⟩
  intro r hr
  have har := haq.trans hr
  have hbr := hbq.trans hr
  have hN : kernelChain K r = kernelChain K (r + 1) :=
    (ha r har).trans (ha (r + 1) (by omega)).symm
  have hR : rangeChain K r = rangeChain K (r + 1) :=
    (hb r hbr).trans (hb (r + 1) (by omega)).symm
  exact ⟨(ha r har).trans (ha q haq).symm,
    (hb r hbr).trans (hb q hbq).symm,
    riesz_decomposition_at_common_index K hK r (hq.trans hr) hN hR⟩

end ExpandedFA.Fredholm
