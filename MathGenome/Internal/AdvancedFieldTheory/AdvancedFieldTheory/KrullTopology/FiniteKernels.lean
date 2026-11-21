import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.KrullTopology.FiniteStabilizers
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteGaloisStages.Containment
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.RestrictionSystem
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.FiniteKernels

/-! # The finite quotient kernels of the Krull topology

FT-T02. All finite Galois intermediate fields are used as indices. Finite-set
containment gives cofinality among the finite pointwise stabilizers, and
surjectivity of restriction gives the exact subgroup index.
-/

universe u v
noncomputable section
open scoped Topology

namespace AdvancedFieldTheory.KrullTopology

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- N_E, the kernel of restriction to a finite Galois intermediate field. -/
abbrev finiteGaloisKernel (E : FiniteGaloisIntermediateField K L) :
    Subgroup (L ≃ₐ[K] L) :=
  Specs.AdvancedFieldTheory.KrullTopology.kernel E

theorem finiteGaloisKernel_eq_fixingSubgroup (E : FiniteGaloisIntermediateField K L) :
    finiteGaloisKernel E = E.toIntermediateField.fixingSubgroup :=
  restriction_ker E.toIntermediateField

theorem finiteGaloisStages_finite_discrete (E : FiniteGaloisIntermediateField K L) :
    Finite (E ≃ₐ[K] E) ∧ DiscreteTopology (E ≃ₐ[K] E) :=
  ⟨inferInstance, inferInstance⟩

theorem finiteGaloisKernel_isOpen (E : FiniteGaloisIntermediateField K L) :
    IsOpen (finiteGaloisKernel E : Set (L ≃ₐ[K] L)) := by
  rw [finiteGaloisKernel_eq_fixingSubgroup]
  exact E.toIntermediateField.fixingSubgroup_isOpen

theorem finiteGaloisKernel_isClopen (E : FiniteGaloisIntermediateField K L) :
    IsClopen (finiteGaloisKernel E : Set (L ≃ₐ[K] L)) := by
  rw [finiteGaloisKernel_eq_fixingSubgroup]
  exact ⟨E.toIntermediateField.fixingSubgroup_isClosed,
    E.toIntermediateField.fixingSubgroup_isOpen⟩

theorem finiteGaloisKernel_normal (E : FiniteGaloisIntermediateField K L) :
    (finiteGaloisKernel E).Normal := by
  change (restriction E.toIntermediateField).ker.Normal
  infer_instance

theorem finiteGaloisKernel_finiteIndex (E : FiniteGaloisIntermediateField K L) :
    (finiteGaloisKernel E).FiniteIndex := by
  change (restriction E.toIntermediateField).ker.FiniteIndex
  infer_instance

variable [IsGalois K L]

theorem finiteGaloisKernels_nhds_one (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    (𝓝 (1 : L ≃ₐ[K] L)).HasBasis
      (fun _ : FiniteGaloisIntermediateField K L => True)
      (fun E => (finiteGaloisKernel E : Set (L ≃ₐ[K] L))) := by
  constructor
  intro U
  constructor
  · intro hU
    obtain ⟨S, hS, hSU⟩ := (finiteStabilizers_nhds_one K L).mem_iff.mp hU
    obtain ⟨E, hSE, hfin, hgal⟩ := exists_finite_galois_containing K L S hS
    let F : FiniteGaloisIntermediateField K L :=
      { toIntermediateField := E, finiteDimensional := hfin, isGalois := hgal }
    refine ⟨F, trivial, ?_⟩
    intro σ hσ
    apply hSU
    rw [finiteGaloisKernel_eq_fixingSubgroup] at hσ
    exact fun x hx => (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ x (hSE hx)
  · rintro ⟨E, _, hEU⟩
    exact Filter.mem_of_superset
      ((finiteGaloisKernel_isOpen E).mem_nhds (finiteGaloisKernel E).one_mem) hEU

theorem finiteGaloisKernel_index (E : FiniteGaloisIntermediateField K L) :
    (finiteGaloisKernel E).index = Nat.card (E ≃ₐ[K] E) := by
  change (restriction E.toIntermediateField).ker.index = _
  rw [Subgroup.index_ker,
    (restriction E.toIntermediateField).range_eq_top_of_surjective
      (restriction_surjective E.toIntermediateField), Subgroup.card_top]

theorem iInf_finiteGaloisKernel_eq_bot (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    (⨅ E : FiniteGaloisIntermediateField K L, finiteGaloisKernel E) = ⊥ := by
  apply le_antisymm _ bot_le
  intro σ hσ
  rw [Subgroup.mem_bot]
  ext x
  obtain ⟨E, hxE, hfin, hgal⟩ :=
    exists_finite_galois_containing K L {x} (Set.finite_singleton x)
  let F : FiniteGaloisIntermediateField K L :=
      { toIntermediateField := E, finiteDimensional := hfin, isGalois := hgal }
  have hσF := (Subgroup.mem_iInf.mp hσ) F
  rw [finiteGaloisKernel_eq_fixingSubgroup] at hσF
  exact (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσF x (hxE (Set.mem_singleton x))

theorem finite_extension_discreteTopology (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    DiscreteTopology (L ≃ₐ[K] L) := inferInstance

end AdvancedFieldTheory.KrullTopology
