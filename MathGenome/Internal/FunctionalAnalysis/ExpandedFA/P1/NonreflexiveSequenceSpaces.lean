import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.NonreflexiveSequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14WeakSubsequence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Stability

/-! The three canonical endpoint counterexamples. The c₀ bidual identification
uses the accepted bilinear sequence dualities; the ℓ¹ argument uses coordinate
functionals and the sum functional; ℓ∞ uses its closed subspace c₀. -/

noncomputable section
open Filter
open scoped Topology ENNReal

namespace ExpandedFA.P1.NonreflexiveSequenceSpaces
open C01SequenceSpaces
open ExpandedFA.FunctionSpaces.SequenceDuals
universe u

-- Cache the inherited structures before iterating the dual constructor.
local instance (𝕜 : Type u) [RCLike 𝕜] : NormedAddCommGroup (SequenceC0 𝕜) :=
  inferInstance
local instance (𝕜 : Type u) [RCLike 𝕜] : NormedSpace 𝕜 (SequenceC0 𝕜) :=
  inferInstance

/-- Transport the continuous scalar-linear dual along an isometric equivalence. -/
def dualPrecomposeIsometry {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (U : E ≃ₗᵢ[𝕜] F) :
    (F →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] (E →L[𝕜] 𝕜) where
  toLinearEquiv :=
    { toFun := fun f => f.comp U.toContinuousLinearEquiv.toContinuousLinearMap
      invFun := fun g => g.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      left_inv := by intro f; ext x; simp
      right_inv := by intro g; ext x; simp }
  norm_map' f := ContinuousLinearMap.opNorm_comp_linearIsometryEquiv f U

/-- The two endpoint dualities give the actual c₀ bidual identification. -/
def c0BidualEquiv {𝕜 : Type u} [RCLike 𝕜] :
    ((SequenceC0 𝕜 →L[𝕜] 𝕜) →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] SequenceLInfinity 𝕜 :=
  (dualPrecomposeIsometry (c0DualityEquiv (𝕜 := 𝕜))).trans l1Duality.symm

@[simp] theorem c0BidualEquiv_evaluation {𝕜 : Type u} [RCLike 𝕜]
    (x : SequenceC0 𝕜) :
    (c0BidualEquiv (𝕜 := 𝕜))
      (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 _ x) = x.val := by
  apply (l1Duality (𝕜 := 𝕜)).injective
  simp only [c0BidualEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  change (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 _ x).comp
    (c0DualityEquiv (𝕜 := 𝕜)).toContinuousLinearEquiv.toContinuousLinearMap =
      (l1Duality (𝕜 := 𝕜)) x.val
  ext a
  change (∑' j, a j * x.val j) = ∑' j, x.val j * a j
  simp_rw [mul_comm]

theorem c0_bidual_image : Spec.C0BidualImage.{u} := by
  intro 𝕜 _
  refine ⟨c0BidualEquiv, c0BidualEquiv_evaluation, ?_, ?_⟩
  · simp only [c0BidualEquiv_evaluation]
    ext a
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.property, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
  · simp only [c0BidualEquiv_evaluation]
    rintro ⟨x, hx⟩
    change x.val = (1 : SequenceLInfinity 𝕜) at hx
    have ht := x.property
    rw [hx] at ht
    have h10 : (1 : 𝕜) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
    exact one_ne_zero h10

theorem c0_not_reflexive : Spec.C0Nonreflexive.{u} := by
  intro 𝕜 _ h
  obtain ⟨B, _, _, hnot⟩ := c0_bidual_image 𝕜
  obtain ⟨x, hx⟩ := h (B.symm 1)
  apply hnot
  exact ⟨x, (congrArg B hx).trans (B.apply_symm_apply 1)⟩

/-- Every functional of the original norm dual tests a weak limit. -/
private theorem weak_limit_test {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {a : ℕ → E} {x : E}
    (h : Tendsto a atTop
      (@nhds E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
        (topDualPairing 𝕜 E)) x))
    (f : E →L[𝕜] 𝕜) : Tendsto (fun n => f (a n)) atTop (𝓝 (f x)) := by
  rw [dualPairTopology_evaluation 𝕜 E, nhds_iInf] at h
  simp only [tendsto_iInf, nhds_induced, tendsto_comap_iff, Function.comp_def] at h
  exact h f

theorem l1_unit_vectors_no_weak_subsequence : Spec.L1NoWeakSubsequence.{u} := by
  intro 𝕜 _ k hk ⟨x, hx⟩
  have hx0 : x = 0 := by
    apply lp.ext
    funext j
    have ht := weak_limit_test hx (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 1 j)
    have hz : Tendsto (fun n => (lp.single 1 (k n) (1 : 𝕜) : SequenceLp 𝕜 1) j)
        atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (j + 1)] with n hn
      have hne : j ≠ k n := by have hle : n ≤ k n := hk.le_apply; omega
      simp [lp.single_apply, hne]
    exact tendsto_nhds_unique ht hz
  have ht := weak_limit_test hx (l1Pairing (1 : SequenceLInfinity 𝕜))
  have h1 : Tendsto (fun _ : ℕ => (1 : 𝕜)) atTop (𝓝 0) := by
    simpa only [l1Pairing_single, lp.infty_coeFn_one, Pi.one_apply, hx0, map_zero] using ht
  exact one_ne_zero (tendsto_nhds_unique h1 tendsto_const_nhds).symm

theorem l1_not_reflexive : Spec.L1Nonreflexive.{u} := by
  intro 𝕜 _ h
  let a : ℕ → SequenceLp 𝕜 1 := fun n => lp.single 1 n 1
  have ha : Bornology.IsBounded (Set.range a) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    simp [a, lp.norm_single (by simp : 0 < (1 : ℝ≥0∞))]
  obtain ⟨k, hk, x, hx⟩ := C14WeakSubsequence.reflexive_weak_subsequence 𝕜 _ h a ha
  exact l1_unit_vectors_no_weak_subsequence 𝕜 k hk ⟨x, hx⟩

theorem c0_closed : Spec.C0Closed.{u} := by
  intro 𝕜 _
  apply isClosed_of_closure_subset
  intro x hx
  change Tendsto (fun j => x j) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  change Tendsto (fun j => y j) atTop (𝓝 0) at hy
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy (ε / 2) (half_pos hε)
  refine ⟨N, fun j hj => ?_⟩
  rw [dist_zero_right]
  calc
    ‖x j‖ ≤ ‖x j - y j‖ + ‖y j‖ := norm_le_norm_sub_add (x j) (y j)
    _ ≤ ‖x - y‖ + ‖y j‖ :=
      add_le_add (lp.norm_apply_le_norm ENNReal.top_ne_zero (x - y) j) le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add (by simpa [dist_eq_norm] using hxy)
      (by simpa only [dist_zero_right] using hN j hj)
    _ = ε := add_halves ε

theorem linfty_not_reflexive : Spec.LInfinityNonreflexive.{u} := by
  intro 𝕜 _ h
  exact c0_not_reflexive 𝕜
    ((C14Stability.reflexivity_stability 𝕜 (SequenceLInfinity 𝕜)
      (sequenceC0Submodule 𝕜) (c0_closed 𝕜)).1 h).1

end ExpandedFA.P1.NonreflexiveSequenceSpaces
