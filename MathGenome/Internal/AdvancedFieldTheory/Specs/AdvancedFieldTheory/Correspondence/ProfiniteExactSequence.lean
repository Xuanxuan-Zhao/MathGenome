import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.FiniteStabilizers
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.RestrictionSystem
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! Independent specification of FT-C09, notes/003/advanced-field-theory.tex:862–900.
All automorphism groups have their intrinsic Krull topologies; fixing subgroups
have the subspace topology and group quotients have the quotient topology.
No finiteness assumption is made on either Galois extension. -/

universe u v
namespace Specs.AdvancedFieldTheory

/-- Each term in the intrinsic exact sequence is a profinite topological group. -/
def exact_sequence_profinite_groups_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L) [IsGalois K M],
    (CompactSpace (L ≃ₐ[M] L) ∧ T2Space (L ≃ₐ[M] L) ∧
      TotallyDisconnectedSpace (L ≃ₐ[M] L) ∧ IsTopologicalGroup (L ≃ₐ[M] L)) ∧
    (CompactSpace (L ≃ₐ[K] L) ∧ T2Space (L ≃ₐ[K] L) ∧
      TotallyDisconnectedSpace (L ≃ₐ[K] L) ∧ IsTopologicalGroup (L ≃ₐ[K] L)) ∧
    (CompactSpace (M ≃ₐ[K] M) ∧ T2Space (M ≃ₐ[K] M) ∧
      TotallyDisconnectedSpace (M ≃ₐ[K] M) ∧ IsTopologicalGroup (M ≃ₐ[K] M))

/-- The natural inclusion is injective, is a topological embedding, and
identifies the intrinsic group homeomorphically with the fixing subgroup. -/
def galois_inclusion_exact_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L) [IsGalois K M],
    Function.Injective (fun σ : L ≃ₐ[M] L => σ.restrictScalars K) ∧
    Topology.IsEmbedding (fun σ : L ≃ₐ[M] L => σ.restrictScalars K) ∧
    (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L)).range =
      M.fixingSubgroup ∧
    ∃ e : M.fixingSubgroup ≃ₜ* (L ≃ₐ[M] L),
      ∀ σ : M.fixingSubgroup, e σ = M.fixingSubgroupEquiv σ

/-- Exactness at the middle and right, including the quotient-map assertion. -/
def galois_restriction_exact_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L) [IsGalois K M],
    IsClosed (M.fixingSubgroup : Set (L ≃ₐ[K] L)) ∧
    M.fixingSubgroup.Normal ∧
    Continuous (restriction_value M) ∧
    Function.Surjective (restriction_value M) ∧
    (restriction_value M).ker = M.fixingSubgroup ∧
    Topology.IsQuotientMap (restriction_value M)

/-- The unique topological group isomorphism induced by restriction, with
its actual value on every coset. The normal-subgroup instance is the standard
one for a Galois intermediate field. -/
def restriction_quotient_topologicalIsomorphism_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (M : IntermediateField K L) [IsGalois K M],
    ∃! e : ((L ≃ₐ[K] L) ⧸ M.fixingSubgroup) ≃ₜ* (M ≃ₐ[K] M),
      ∀ σ : L ≃ₐ[K] L, e (QuotientGroup.mk σ) = restriction_value M σ

end Specs.AdvancedFieldTheory
