import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.FiniteStabilizers
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.RestrictionSystem
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.GroupTheory.Index

/-! Independent specification of FT-T02, notes/003/advanced-field-theory.tex:399–432.
The index type contains every finite Galois intermediate field of the specified
ambient extension, with the canonical inclusion algebra structures. The topology
on each automorphism group is the Krull topology; on a finite stage it is discrete.
-/

universe u v
noncomputable section
open scoped Topology
set_option linter.checkUnivs false

namespace Specs.AdvancedFieldTheory.KrullTopology

/-- The actual kernel of restriction, not a certificate for a subgroup. -/
def kernel {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (E : FiniteGaloisIntermediateField K L) : Subgroup (L ≃ₐ[K] L) :=
  (Specs.AdvancedFieldTheory.restriction_value E.toIntermediateField).ker

def finiteGaloisKernel_type := ∀ {K : Type u} {L : Type v}
  [Field K] [Field L] [Algebra K L],
  FiniteGaloisIntermediateField K L → Subgroup (L ≃ₐ[K] L)

def finiteGaloisKernel_value : finiteGaloisKernel_type :=
  fun {_} {_} _ _ _ E => kernel E

def finiteGaloisKernel_eq_fixingSubgroup_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (E : FiniteGaloisIntermediateField K L),
    kernel E = E.toIntermediateField.fixingSubgroup

def finiteGaloisStages_finite_discrete_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (E : FiniteGaloisIntermediateField K L),
    Finite (E ≃ₐ[K] E) ∧ DiscreteTopology (E ≃ₐ[K] E)

def finiteGaloisKernels_nhds_one_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    (𝓝 (1 : L ≃ₐ[K] L)).HasBasis
      (fun _ : FiniteGaloisIntermediateField K L => True)
      (fun E => (kernel E : Set (L ≃ₐ[K] L)))

def finiteGaloisKernel_isOpen_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (E : FiniteGaloisIntermediateField K L),
    IsOpen (kernel E : Set (L ≃ₐ[K] L))

def finiteGaloisKernel_isClopen_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (E : FiniteGaloisIntermediateField K L),
    IsClopen (kernel E : Set (L ≃ₐ[K] L))

def finiteGaloisKernel_normal_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (E : FiniteGaloisIntermediateField K L), (kernel E).Normal

def finiteGaloisKernel_finiteIndex_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (E : FiniteGaloisIntermediateField K L), (kernel E).FiniteIndex

def finiteGaloisKernel_index_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L),
    (kernel E).index = Nat.card (E ≃ₐ[K] E)

def iInf_finiteGaloisKernel_eq_bot_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    (⨅ E : FiniteGaloisIntermediateField K L, kernel E) = ⊥

def finite_extension_discreteTopology_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L], DiscreteTopology (L ≃ₐ[K] L)

end Specs.AdvancedFieldTheory.KrullTopology
