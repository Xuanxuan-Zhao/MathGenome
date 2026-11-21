import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Topology.Bases

/-! Independent specification of finite pointwise stabilizers and the Krull topology.
Source: notes/003/advanced-field-theory.tex, chapter 2, definition preceding T01
and proposition T01. Finite sets include the empty set. -/

universe u v
noncomputable section
set_option linter.checkUnivs false
open scoped Pointwise Topology

namespace Specs.AdvancedFieldTheory.KrullTopology

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The actual subgroup of automorphisms fixing a set pointwise. -/
def stabilizer (S : Set L) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | ∀ x ∈ S, σ x = x}
  one_mem' := by simp
  mul_mem' := by
    intro σ τ hσ hτ x hx
    change σ (τ x) = x
    rw [hτ x hx, hσ x hx]
  inv_mem' := by
    intro σ hσ x hx
    change σ.symm x = x
    apply σ.injective
    simpa using (hσ x hx).symm

/-- All left cosets of all finite pointwise stabilizers. -/
def cosets : Set (Set (L ≃ₐ[K] L)) :=
  {U | ∃ (σ : L ≃ₐ[K] L) (S : Set L), S.Finite ∧ U = σ • (stabilizer K S : Set (L ≃ₐ[K] L))}

def finiteStabilizer_type := ∀ (K : Type u) (L : Type v) [Field K] [Field L]
  [Algebra K L], Set L → Subgroup (L ≃ₐ[K] L)
def finiteStabilizer_value : finiteStabilizer_type := fun K L _ _ _ => stabilizer K (L := L)

def finiteCosetBasis_type := ∀ (K : Type u) (L : Type v) [Field K] [Field L]
  [Algebra K L], Set (Set (L ≃ₐ[K] L))
def finiteCosetBasis_value : finiteCosetBasis_type := fun K L _ _ _ => cosets K (L := L)

def finiteStabilizerTopology_type := ∀ (K : Type u) (L : Type v) [Field K] [Field L]
  [Algebra K L], TopologicalSpace (L ≃ₐ[K] L)
def finiteStabilizerTopology_value : finiteStabilizerTopology_type :=
  fun K L _ _ _ => TopologicalSpace.generateFrom (cosets K (L := L))

variable {K}

def mem_finiteStabilizer_type : Prop := ∀ {K : Type u} {L : Type v}
  [Field K] [Field L] [Algebra K L] (S : Set L) (σ : L ≃ₐ[K] L),
  σ ∈ stabilizer K S ↔ ∀ x ∈ S, σ x = x

def finiteStabilizer_eq_fixingSubgroup_type : Prop := ∀ {K : Type u} {L : Type v}
  [Field K] [Field L] [Algebra K L] (S : Set L),
  stabilizer K S = (IntermediateField.adjoin K S).fixingSubgroup

def finiteStabilizer_empty_type : Prop := ∀ (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L], stabilizer K (∅ : Set L) = ⊤

def finiteStabilizer_union_type : Prop := ∀ {K : Type u} {L : Type v}
  [Field K] [Field L] [Algebra K L] (S T : Set L),
  stabilizer K S ⊓ stabilizer K T = stabilizer K (S ∪ T)

def finiteStabilizer_conjugate_type : Prop := ∀ {K : Type u} {L : Type v}
  [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (S : Set L),
  (fun τ => σ * τ * σ⁻¹) '' (stabilizer K S : Set (L ≃ₐ[K] L)) =
    (stabilizer K (σ '' S) : Set (L ≃ₐ[K] L))

/-- Exact equality with the original finite-dimensional-field basis. -/
def galBasis_eq_finiteStabilizers_type : Prop := ∀ (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L] [IsGalois K L],
  (galBasis K L).sets = {U | ∃ S : Set L, S.Finite ∧ U = (stabilizer K S : Set (L ≃ₐ[K] L))}

def finiteStabilizer_isOpen_type : Prop := ∀ {K : Type u} {L : Type v}
  [Field K] [Field L] [Algebra K L] [IsGalois K L] (S : Set L),
  S.Finite → IsOpen (stabilizer K S : Set (L ≃ₐ[K] L))

def finiteStabilizers_nhds_one_type : Prop := ∀ (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L] [IsGalois K L],
  (𝓝 (1 : L ≃ₐ[K] L)).HasBasis (fun S : Set L => S.Finite)
    (fun S => (stabilizer K S : Set (L ≃ₐ[K] L)))

def finiteCosetBasis_isTopologicalBasis_type : Prop := ∀ (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L] [IsGalois K L],
  TopologicalSpace.IsTopologicalBasis (cosets K (L := L))

def finiteStabilizerTopology_eq_krull_type : Prop := ∀ (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L] [IsGalois K L],
  TopologicalSpace.generateFrom (cosets K (L := L)) = krullTopology K L

def finiteCosetBasis_unique_type : Prop := ∀ (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L] [IsGalois K L],
  ∃! t : TopologicalSpace (L ≃ₐ[K] L),
    @TopologicalSpace.IsTopologicalBasis _ t (cosets K (L := L))

def finiteStabilizerTopology_isTopologicalGroup_type : Prop := ∀ (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L] [IsGalois K L],
  @IsTopologicalGroup (L ≃ₐ[K] L)
    (TopologicalSpace.generateFrom (cosets K (L := L))) _

end Specs.AdvancedFieldTheory.KrullTopology
