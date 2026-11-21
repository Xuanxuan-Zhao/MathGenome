import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.CompactLowerOrder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.SobolevFormBridge
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.RellichEmbeddings
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RieszSchauder
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Function.Holder

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace ExpandedFA.PartV.CompactLowerOrder
open ExpandedFA.Sobolev ExpandedFA.Distributions SobolevFormBridge

section Abstract
variable {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- On the stable range the compact defect is an isomorphism. Its finite
codimension then gives Fredholmness; additivity of index gives index zero. -/
theorem compact_defect_fredholm (K : E →L[𝕜] E) (hK : IsCompactOperator K) :
    (ContinuousLinearMap.id 𝕜 E - K).IsFredholm ∧
      (ContinuousLinearMap.id 𝕜 E - K).toLinearMap.index = 0 := by
  have hKs : Compactness.IsCompactLinearMap K.toLinearMap :=
    (Compactness.compact_iff_isCompactOperator K.toLinearMap).mpr hK
  obtain ⟨p, _, hp⟩ := Fredholm.riesz_decomposition K hKs
  obtain ⟨hc, _, hN, hR, _, _, hmap, _, e, he⟩ := (hp p le_rfl).2.2
  let R := Fredholm.CompactDefectStabilizationSpec.rangeChain K p
  let A := ContinuousLinearMap.id 𝕜 E - K
  have : R.CoFG :=
    ((Submodule.fg_iff_finiteDimensional _).mpr hN).cofg_of_isCompl hc.isCompl
  have hinv : (A.restrict hmap).IsInvertible := by
    refine ⟨e, ?_⟩
    ext x
    exact he x
  have hA : A.IsFredholm :=
    ContinuousLinearMap.IsFredholm.of_isInvertible_restrict hR hR hmap hinv
  have hi : R.subtypeL.IsFredholm := Submodule.isFredholm_subtypeL hR
  have heq : A.comp R.subtypeL = R.subtypeL.comp e.toContinuousLinearMap := by
    ext x
    exact (he x).symm
  have hidx := hA.index_comp hi
  rw [heq, hi.index_comp e.isFredholm] at hidx
  have he0 : e.toContinuousLinearMap.toLinearMap.index = 0 :=
    LinearMap.index_of_bijective e.bijective
  change R.subtype.index + e.toContinuousLinearMap.toLinearMap.index =
    A.toLinearMap.index + R.subtype.index at hidx
  rw [he0] at hidx
  exact ⟨hA, by change A.toLinearMap.index = 0; omega⟩

/-- Transport a compact defect through an arbitrary bounded isomorphism. -/
theorem compact_perturbation_fredholm {F : Type} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (e : E ≃L[𝕜] F) (B : E →L[𝕜] F)
    (hB : IsCompactOperator B) :
    (e.toContinuousLinearMap + B).IsFredholm ∧
      (e.toContinuousLinearMap + B).toLinearMap.index = 0 := by
  let K : E →L[𝕜] E := -(e.symm.toContinuousLinearMap.comp B)
  have hK : IsCompactOperator K := (hB.clm_comp e.symm.toContinuousLinearMap).neg
  obtain ⟨hA, hidx⟩ := compact_defect_fredholm K hK
  have heq : e.toContinuousLinearMap.comp (ContinuousLinearMap.id 𝕜 E - K) =
      e.toContinuousLinearMap + B := by
    ext x
    simp [K]
  have hfred := e.isFredholm.comp hA
  rw [heq] at hfred
  have hi := e.isFredholm.index_comp hA
  rw [heq] at hi
  have he0 : e.toContinuousLinearMap.toLinearMap.index = 0 :=
    LinearMap.index_of_bijective e.bijective
  rw [he0, hidx, add_zero] at hi
  exact ⟨hfred, hi⟩

end Abstract

section Hilbert
variable {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The intrinsic adjoint-form nullspace is the kernel of the Hilbert
adjoint of the Riesz representative. -/
theorem adjoint_nullspace (e : E ≃L[𝕜] (E →L⋆[𝕜] 𝕜))
    (he : ∀ x v, e x v = ⟪v, x⟫_𝕜)
    (T : E →L[𝕜] (E →L⋆[𝕜] 𝕜)) (v : E) :
    (∀ u, T u v = 0) ↔
      (ContinuousLinearMap.adjoint (e.symm.toContinuousLinearMap.comp T)) v = 0 := by
  let S := e.symm.toContinuousLinearMap.comp T
  have hr (u v : E) : T u v = ⟪v, S u⟫_𝕜 := by
    rw [← he]
    simp [S]
  change (∀ u, T u v = 0) ↔ v ∈ (ContinuousLinearMap.adjoint S).ker
  rw [← S.orthogonal_range]
  rw [Submodule.mem_orthogonal']
  constructor
  · intro h y hy
    obtain ⟨u, rfl⟩ := hy
    exact (hr u v).symm.trans (h u)
  · intro h u
    exact (hr u v).trans (h (S u) ⟨u, rfl⟩)

/-- Closed range is exactly compatibility against the adjoint nullspace.
The proof uses the closed range's double orthogonal complement. -/
theorem range_compatibility (e : E ≃L[𝕜] (E →L⋆[𝕜] 𝕜))
    (he : ∀ x v, e x v = ⟪v, x⟫_𝕜)
    (T : E →L[𝕜] (E →L⋆[𝕜] 𝕜))
    (hT : IsClosed (T.range : Set (E →L⋆[𝕜] 𝕜)))
    (F : E →L⋆[𝕜] 𝕜) :
    (∃ u, T u = F) ↔ ∀ v, (∀ u, T u v = 0) → F v = 0 := by
  let S := e.symm.toContinuousLinearMap.comp T
  have hr (u v : E) : T u v = ⟪v, S u⟫_𝕜 := by
    rw [← he]
    simp [S]
  have hclosed : IsClosed (S.range : Set E) := by
    have hset : (S.range : Set E) = e ⁻¹' (T.range : Set (E →L⋆[𝕜] 𝕜)) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, by simp [S]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, (congrArg e.symm hx).trans (e.symm_apply_apply y)⟩
    rw [hset]
    exact hT.preimage e.continuous
  constructor
  · rintro ⟨u, rfl⟩ v hv
    exact hv u
  · intro h
    have hf : e.symm F ∈ S.range.orthogonal.orthogonal := by
      apply (Submodule.mem_orthogonal _ _).mpr
      intro v hv
      rw [← he, e.apply_symm_apply]
      apply h v
      intro u
      rw [hr]
      exact S.range.inner_left_of_mem_orthogonal ⟨u, rfl⟩ hv
    rw [Submodule.orthogonal_orthogonal_eq_closure,
      hclosed.submodule_topologicalClosure_eq] at hf
    obtain ⟨u, hu⟩ := hf
    refine ⟨u, ?_⟩
    apply e.symm.injective
    exact hu
end Hilbert

section Sobolev
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- L∞ multiplication on actual scalar-valued L² classes. -/
def multiplier (q : DomainLp 𝕜 Ω ∞) : DomainLp 𝕜 Ω 2 →L[𝕜] DomainLp 𝕜 Ω 2 :=
  (ContinuousLinearMap.mul 𝕜 𝕜).holderL
    (volume.restrict (Ω : Set (Domain d))) ∞ 2 2 q

@[simp] theorem multiplier_coe (q : DomainLp 𝕜 Ω ∞) (u : DomainLp 𝕜 Ω 2) :
    multiplier q u =ᵐ[volume.restrict (Ω : Set (Domain d))] fun x => q x * u x :=
  (ContinuousLinearMap.mul 𝕜 𝕜).coeFn_holder q u

/-- This is a scalar-linear map into the pointwise antidual. -/
def antiRieszPullback (J : Energy 𝕜 Ω →L[𝕜] DomainLp 𝕜 Ω 2) :
    DomainLp 𝕜 Ω 2 →L[𝕜] (Energy 𝕜 Ω →L⋆[𝕜] 𝕜) :=
  ((innerSL 𝕜).comp J).flip

@[simp] theorem antiRieszPullback_apply
    (J : Energy 𝕜 Ω →L[𝕜] DomainLp 𝕜 Ω 2)
    (y : DomainLp 𝕜 Ω 2) (v : Energy 𝕜 Ω) :
    antiRieszPullback J y v = ⟪J v, y⟫_𝕜 := rfl

/-- Rellich for W₀ transfers through the proved gradient-norm equivalence. -/
theorem compact_inclusion (hΩ : EnergyScope Ω) :
    ∃ J : Energy 𝕜 Ω →L[𝕜] DomainLp 𝕜 Ω 2,
      (∀ u : W 𝕜 Ω, J (energyEquiv hΩ u) = u.val.val (zeroIndex d 1)) ∧
      IsCompactOperator J := by
  obtain ⟨J₀, hJ₀, hc⟩ := Rellich.zero_same_exponent
    (𝕜 := 𝕜) (p := 2) hΩ.1 (by norm_num)
  have hJ : ∀ u : W 𝕜 Ω, J₀ u = u.val.val (zeroIndex d 1) := by
    intro u
    exact Lp.ext (hJ₀ u)
  have hc₀ : IsCompactOperator J₀ := by
    refine ⟨closure (J₀ '' Metric.closedBall 0 1),
      hc _ Metric.isBounded_closedBall, ?_⟩
    apply Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : W 𝕜 Ω) zero_lt_one)
    intro x hx
    exact subset_closure ⟨x, hx, rfl⟩
  refine ⟨J₀.comp (energyEquiv hΩ).symm.toContinuousLinearMap, ?_,
    hc₀.comp_clm (energyEquiv hΩ).symm.toContinuousLinearMap⟩
  intro u
  simpa using hJ u

set_option maxHeartbeats 1200000 in
/-- The full integral-map and Fredholm statement, on every bounded open set
in the corrected energy scope, hence in particular on bounded C¹ domains. -/
theorem compact_lower_order : Spec.CompactLowerOrder := by
  intro 𝕜 _ d Ω hΩ
  have := energy_complete (𝕜 := 𝕜) hΩ
  let e := energyEquiv (𝕜 := 𝕜) hΩ
  obtain ⟨J, hJ, hcJ⟩ := compact_inclusion (𝕜 := 𝕜) hΩ
  refine ⟨e, J, energyEquiv_coe hΩ, hJ, hcJ, fun q => ?_⟩
  let B := (antiRieszPullback J).comp ((multiplier q).comp J)
  have hB : IsCompactOperator B :=
    (hcJ.clm_comp (multiplier q)).clm_comp (antiRieszPullback J)
  refine ⟨B, ?_, hB, ?_⟩
  · intro u v
    change ⟪J (e v), multiplier q (J (e u))⟫_𝕜 = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [multiplier_coe q (J (e u))] with x hx
    rw [hx, hJ u, hJ v, RCLike.inner_apply']
    ring
  · intro a c hc
    obtain ⟨e₀, he₀⟩ := coercive_isomorphism 𝕜 d Ω hΩ a c hc
    have hA₀ : e₀.toContinuousLinearMap = a.flip := by
      ext u v
      exact he₀ u v
    obtain ⟨hf, hi⟩ := compact_perturbation_fredholm e₀ B hB
    rw [hA₀] at hf hi
    refine ⟨hf.isClosed_range, hf.finite_ker, hf.finite_coker, hi, ?_⟩
    have hinner : Hilbert.Conventions.Spec.FormCoerciveValue
        𝕜 (Energy 𝕜 Ω) (innerSL 𝕜) 1 := by
      refine ⟨zero_lt_one, fun u => ?_⟩
      simp only [innerSL_apply_apply, one_mul]
      exact (norm_sq_eq_re_inner (𝕜 := 𝕜) u).le
    obtain ⟨r, hr⟩ := coercive_isomorphism 𝕜 d Ω hΩ (innerSL 𝕜) 1 hinner
    exact range_compatibility r hr (a.flip + B) hf.isClosed_range
end Sobolev

end ExpandedFA.PartV.CompactLowerOrder
