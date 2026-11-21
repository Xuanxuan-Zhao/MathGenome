import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.RestrictionSystem
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.KrullTopology.RestrictionContinuous
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.KrullTopology.ChangeBase
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.InverseLimit.Profiniteness
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.FieldRecovery
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.Normality
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Correspondence.ProfiniteExactSequence

/-! # The profinite exact sequence (FT-C09)
Restriction to an arbitrary Galois intermediate field is a quotient map.
The first isomorphism theorem, together with compactness and Hausdorffness,
identifies its group quotient with the target with its intrinsic Krull topology.
-/

universe u v
noncomputable section
namespace AdvancedFieldTheory

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [IsGalois K L]

/-- All three intrinsic groups in the sequence are profinite. -/
theorem exact_sequence_profinite_groups (M : IntermediateField K L) [IsGalois K M] :
    (CompactSpace (L ≃ₐ[M] L) ∧ T2Space (L ≃ₐ[M] L) ∧
      TotallyDisconnectedSpace (L ≃ₐ[M] L) ∧ IsTopologicalGroup (L ≃ₐ[M] L)) ∧
    (CompactSpace (L ≃ₐ[K] L) ∧ T2Space (L ≃ₐ[K] L) ∧
      TotallyDisconnectedSpace (L ≃ₐ[K] L) ∧ IsTopologicalGroup (L ≃ₐ[K] L)) ∧
    (CompactSpace (M ≃ₐ[K] M) ∧ T2Space (M ≃ₐ[K] M) ∧
      TotallyDisconnectedSpace (M ≃ₐ[K] M) ∧ IsTopologicalGroup (M ≃ₐ[K] M)) := by
  let : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  exact ⟨⟨inferInstance, galoisGroup_t2Space M L,
      galoisGroup_totallyDisconnectedSpace M L, inferInstance⟩,
    ⟨inferInstance, galoisGroup_t2Space K L,
      galoisGroup_totallyDisconnectedSpace K L, inferInstance⟩,
    ⟨inferInstance, galoisGroup_t2Space K M,
      galoisGroup_totallyDisconnectedSpace K M, inferInstance⟩⟩

/-- Inclusion identifies the intrinsic upper Galois group with the subspace
fixing subgroup, both algebraically and topologically. -/
theorem galois_inclusion_exact (M : IntermediateField K L) [IsGalois K M] :
    Function.Injective (fun σ : L ≃ₐ[M] L => σ.restrictScalars K) ∧
    Topology.IsEmbedding (fun σ : L ≃ₐ[M] L => σ.restrictScalars K) ∧
    (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L)).range =
      M.fixingSubgroup ∧
    ∃ e : M.fixingSubgroup ≃ₜ* (L ≃ₐ[M] L),
      ∀ σ : M.fixingSubgroup, e σ = M.fixingSubgroupEquiv σ := by
  refine ⟨AlgEquiv.restrictScalars_injective K,
    KrullTopology.changeBase_isEmbedding M, ?_, ?_⟩
  · ext σ
    constructor
    · rintro ⟨τ, rfl⟩
      exact (M.fixingSubgroupEquiv.symm τ).property
    · intro hσ
      exact ⟨M.fixingSubgroupEquiv ⟨σ, hσ⟩, rfl⟩
  · obtain ⟨hc, hi⟩ := KrullTopology.fixingSubgroupEquiv_bicontinuous M
    exact ⟨{ M.fixingSubgroupEquiv with
      continuous_toFun := hc
      continuous_invFun := hi }, fun _ => rfl⟩

/-- Restriction is a continuous surjective quotient homomorphism with precisely
the closed normal fixing subgroup as its kernel. -/
theorem galois_restriction_exact (M : IntermediateField K L) [IsGalois K M] :
    IsClosed (M.fixingSubgroup : Set (L ≃ₐ[K] L)) ∧
    M.fixingSubgroup.Normal ∧
    Continuous (restriction M) ∧
    Function.Surjective (restriction M) ∧
    (restriction M).ker = M.fixingSubgroup ∧
    Topology.IsQuotientMap (restriction M) := by
  let := galoisGroup_t2Space K M
  exact ⟨fixingSubgroup_isClosed K L M,
    (fixingSubgroup_normal_iff_isGalois M).mpr inferInstance,
    KrullTopology.restriction_continuous M, restriction_surjective M,
    restriction_ker M, .of_surjective_continuous
      (restriction_surjective M) (KrullTopology.restriction_continuous M)⟩

/-- The quotient topology on the cosets agrees with the intrinsic Krull
topology on the restricted Galois group, including infinite intermediate fields. -/
theorem restriction_quotient_topologicalIsomorphism
    (M : IntermediateField K L) [IsGalois K M] :
    ∃! e : ((L ≃ₐ[K] L) ⧸ M.fixingSubgroup) ≃ₜ* (M ≃ₐ[K] M),
      ∀ σ : L ≃ₐ[K] L, e (QuotientGroup.mk σ) = restriction M σ := by
  let := galoisGroup_t2Space K M
  let a : ((L ≃ₐ[K] L) ⧸ M.fixingSubgroup) ≃* (M ≃ₐ[K] M) :=
    (QuotientGroup.quotientMulEquivOfEq
      (show M.fixingSubgroup = (restriction M).ker from (restriction_ker M).symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (restriction M) (restriction_surjective M))
  have ha (σ : L ≃ₐ[K] L) : a (QuotientGroup.mk σ) = restriction M σ := by
    simp only [a, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hc : Continuous a := by
    apply (QuotientGroup.isQuotientMap_mk M.fixingSubgroup).continuous_iff.mpr
    exact KrullTopology.restriction_continuous M
  let h := a.toEquiv.toHomeomorphOfContinuousClosed hc hc.isClosedMap
  let e : ((L ≃ₐ[K] L) ⧸ M.fixingSubgroup) ≃ₜ* (M ≃ₐ[K] M) :=
    { a with continuous_toFun := hc, continuous_invFun := h.symm.continuous }
  refine ⟨e, ha, ?_⟩
  intro e' he'
  apply ContinuousMulEquiv.ext
  intro q
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective q
  exact (he' σ).trans (ha σ).symm

end AdvancedFieldTheory
