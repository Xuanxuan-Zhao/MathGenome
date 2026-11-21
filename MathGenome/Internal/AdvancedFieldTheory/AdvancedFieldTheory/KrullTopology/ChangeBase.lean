import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.GaloisTowers
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.KrullTopology.FiniteStabilizers
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.ChangeBase

/-! FT-T08: change of base preserves the Krull topology on a fixing subgroup. -/

universe u v
noncomputable section
open scoped Topology

namespace AdvancedFieldTheory.KrullTopology

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Restriction of scalars preserves the pointwise stabilizer of any set. -/
theorem changeBase_stabilizer_preimage (M : IntermediateField K L) (S : Set L) :
    (fun σ : L ≃ₐ[M] L => σ.restrictScalars K) ⁻¹'
      (finiteStabilizer K L S : Set (L ≃ₐ[K] L)) =
      (finiteStabilizer M L S : Set (L ≃ₐ[M] L)) := rfl

/-- In the ambient group the intrinsic stabilizer is `G_M ∩ G(S)`. -/
theorem changeBase_stabilizer_image (M : IntermediateField K L) (S : Set L) :
    (fun σ : L ≃ₐ[M] L => σ.restrictScalars K) ''
      (finiteStabilizer M L S : Set (L ≃ₐ[M] L)) =
      (M.fixingSubgroup : Set (L ≃ₐ[K] L)) ∩
        (finiteStabilizer K L S : Set (L ≃ₐ[K] L)) := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨(M.fixingSubgroupEquiv.symm τ).property, hτ⟩
  · rintro ⟨hM, hS⟩
    refine ⟨M.fixingSubgroupEquiv ⟨σ, hM⟩, hS, ?_⟩
    ext x
    rfl

/-- The two identity-neighborhood bases have identical preimages, hence the
natural inclusion induces the intrinsic Krull topology. No condition on `M/K`
is used: the upper extension is Galois by the tower theorem. -/
theorem changeBase_isEmbedding [IsGalois K L] (M : IntermediateField K L) :
    Topology.IsEmbedding (fun σ : L ≃ₐ[M] L => σ.restrictScalars K) := by
  have hM := galois_tower K L M
  have : IsGalois M L := { to_isSeparable := hM.2.2.2.2, to_normal := hM.2.2.2.1 }
  refine ⟨?_, AlgEquiv.restrictScalars_injective K⟩
  change Topology.IsInducing (AlgEquiv.restrictScalarsHom K :
    (L ≃ₐ[M] L) →* (L ≃ₐ[K] L))
  apply IsTopologicalGroup.isInducing_iff_nhds_one.mpr
  exact (finiteStabilizers_nhds_one M L).eq_of_same_basis
    ((finiteStabilizers_nhds_one K L).comap
      (fun σ : L ≃ₐ[M] L => σ.restrictScalars K))

/-- The intrinsic topology equals the topology induced by the natural inclusion. -/
theorem changeBase_topology_eq [IsGalois K L] (M : IntermediateField K L) :
    krullTopology M L = TopologicalSpace.induced
      (fun σ : L ≃ₐ[M] L => σ.restrictScalars K) (krullTopology K L) :=
  (changeBase_isEmbedding M).isInducing.eq_induced

/-- Under the canonical group isomorphism, the subspace topology on `G_M`
and the intrinsic Krull topology on `Gal(L/M)` agree. -/
theorem fixingSubgroupEquiv_bicontinuous [IsGalois K L]
    (M : IntermediateField K L) :
    Continuous M.fixingSubgroupEquiv ∧ Continuous M.fixingSubgroupEquiv.symm := by
  have hi : Topology.IsInducing M.fixingSubgroupEquiv.symm :=
    Topology.IsInducing.subtypeVal.of_comp_iff.mp
      (changeBase_isEmbedding M).isInducing
  exact ⟨(M.fixingSubgroupEquiv.symm.toEquiv.toHomeomorphOfIsInducing hi).symm.continuous,
    hi.continuous⟩

end AdvancedFieldTheory.KrullTopology
