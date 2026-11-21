import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.FiniteStabilizers
import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
Independent specification of FT-T08, notes/003/advanced-field-theory.tex:614–631.
The intermediate field is arbitrary. Both Krull topologies use the same top
field and its finite subsets; the subgroup carries the ambient subspace topology.
The algebraic identification is the canonical `IntermediateField.fixingSubgroupEquiv`.
-/

universe u v
noncomputable section

namespace Specs.AdvancedFieldTheory.KrullTopology

/-- Restricting scalars does not change which elements of the top field are fixed. -/
def changeBase_stabilizer_preimage_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) (S : Set L),
    (fun σ : L ≃ₐ[M] L => σ.restrictScalars K) ⁻¹'
      (stabilizer K S : Set (L ≃ₐ[K] L)) =
      (stabilizer M S : Set (L ≃ₐ[M] L))

/-- The intrinsic stabilizer is exactly the intersection inside the ambient group. -/
def changeBase_stabilizer_image_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) (S : Set L),
    (fun σ : L ≃ₐ[M] L => σ.restrictScalars K) ''
      (stabilizer M S : Set (L ≃ₐ[M] L)) =
      (M.fixingSubgroup : Set (L ≃ₐ[K] L)) ∩
        (stabilizer K S : Set (L ≃ₐ[K] L))

/-- The natural inclusion is a topological embedding for every intermediate field. -/
def changeBase_isEmbedding_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L),
    Topology.IsEmbedding (fun σ : L ≃ₐ[M] L => σ.restrictScalars K)

/-- Explicit equality of the intrinsic topology with the induced topology. -/
def changeBase_topology_eq_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L),
    krullTopology M L = TopologicalSpace.induced
      (fun σ : L ≃ₐ[M] L => σ.restrictScalars K) (krullTopology K L)

/-- The canonical algebraic identification is continuous in both directions,
with the subgroup equipped with its subspace topology. -/
def fixingSubgroupEquiv_bicontinuous_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L),
    Continuous M.fixingSubgroupEquiv ∧ Continuous M.fixingSubgroupEquiv.symm

end Specs.AdvancedFieldTheory.KrullTopology
