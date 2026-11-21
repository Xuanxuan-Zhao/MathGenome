import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Subspaces
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.ClosureCalculus

/-!
Subspace topology, closure, inclusion, mapping property, restricted bases,
and the singleton interior/boundary caution (paper.tex, d10:03:subspace and
d10:03:interior-caution). All general results use canonical subtypes and
allow the empty subset. Images under the inclusion give the paper's
literal intersection formulas on ambient subsets.
-/

open Set Topology
universe u v

namespace D10Topology.Ch03
open D10Topology.Ch01

theorem subspace_image_preimage {X : Type u} (A B : Set X) :
    (Subtype.val : A → X) '' ((Subtype.val : A → X) ⁻¹' B) = A ∩ B := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, ha⟩
  · rintro ⟨hA, hB⟩
    exact ⟨⟨x, hA⟩, hB, rfl⟩

theorem subspace_preimage_image {X : Type u} (A : Set X) (B : Set A) :
    (Subtype.val : A → X) ⁻¹' ((Subtype.val : A → X) '' B) = B :=
  Subtype.val_injective.preimage_image B

section General
variable {X : Type u} [t : TopologicalSpace X]

theorem subspace_topology_induced (A : Set X) :
    (inferInstance : TopologicalSpace A) = t.induced (Subtype.val : A → X) := rfl

theorem subspace_open_iff (A : Set X) (V : Set A) :
    IsOpen V ↔ ∃ U : Set X, IsOpen U ∧ (Subtype.val : A → X) ⁻¹' U = V :=
  isOpen_induced_iff

theorem subspace_closed_iff (A : Set X) (C : Set A) :
    IsClosed C ↔ ∃ F : Set X, IsClosed F ∧ (Subtype.val : A → X) ⁻¹' F = C :=
  isClosed_induced_iff

theorem subspace_open_iff_image (A : Set X) (V : Set A) :
    IsOpen V ↔ ∃ U : Set X, IsOpen U ∧ (Subtype.val : A → X) '' V = A ∩ U := by
  rw [subspace_open_iff]
  constructor
  · rintro ⟨U, hU, rfl⟩
    exact ⟨U, hU, subspace_image_preimage A U⟩
  · rintro ⟨U, hU, heq⟩
    refine ⟨U, hU, Subtype.val_injective.image_injective ?_⟩
    exact (subspace_image_preimage A U).trans heq.symm

theorem subspace_closed_iff_image (A : Set X) (C : Set A) :
    IsClosed C ↔ ∃ F : Set X, IsClosed F ∧ (Subtype.val : A → X) '' C = A ∩ F := by
  rw [subspace_closed_iff]
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, hF, subspace_image_preimage A F⟩
  · rintro ⟨F, hF, heq⟩
    refine ⟨F, hF, Subtype.val_injective.image_injective ?_⟩
    exact (subspace_image_preimage A F).trans heq.symm

theorem subspace_closure (A : Set X) (B : Set A) :
    closure B = (Subtype.val : A → X) ⁻¹' closure ((Subtype.val : A → X) '' B) :=
  IsEmbedding.subtypeVal.closure_eq_preimage_closure_image B

theorem subspace_closure_ambient (A B : Set X) (hBA : B ⊆ A) :
    (Subtype.val : A → X) '' closure ((Subtype.val : A → X) ⁻¹' B) = A ∩ closure B := by
  rw [subspace_closure, subspace_image_preimage,
    subspace_image_preimage, inter_eq_right.mpr hBA]

theorem subspace_inclusion_embedding (A : Set X) :
    IsEmbedding (Subtype.val : A → X) := IsEmbedding.subtypeVal

theorem subspace_continuous_iff {Z : Type v} [TopologicalSpace Z]
    (A : Set X) (g : Z → A) :
    Continuous g ↔ Continuous ((Subtype.val : A → X) ∘ g) :=
  IsEmbedding.subtypeVal.continuous_iff

theorem subspace_basis (A : Set X) (B : Set (Set X)) (hB : BasisFor t B) :
    BasisFor (inferInstance : TopologicalSpace A)
      ((fun U : Set X => (Subtype.val : A → X) ⁻¹' U) '' B) := by
  apply (basis_iff_mathlib _ _).mpr
  exact IsInducing.subtypeVal.isTopologicalBasis ((basis_iff_mathlib t B).mp hB)

theorem subspace_interior_subset (A B : Set X) :
    (Subtype.val : A → X) ⁻¹' interior B ⊆
      interior ((Subtype.val : A → X) ⁻¹' B) :=
  preimage_interior_subset_interior_preimage continuous_subtype_val

theorem subspace_interior_ambient_subset (A B : Set X) (_hBA : B ⊆ A) :
    A ∩ interior B ⊆
      (Subtype.val : A → X) '' interior ((Subtype.val : A → X) ⁻¹' B) := by
  rw [← subspace_image_preimage A (interior B)]
  exact image_mono (subspace_interior_subset A B)

end General

theorem singleton_interior_boundary_caution :
    let A : Set ℝ := {0}
    IsClosed A ∧ ¬ IsOpen A ∧
      interior A = ∅ ∧ A ∩ interior A = ∅ ∧
      interior ((Subtype.val : A → ℝ) ⁻¹' A) = univ ∧
      (Subtype.val : A → ℝ) '' interior ((Subtype.val : A → ℝ) ⁻¹' A) = A ∧
      frontier ((Subtype.val : A → ℝ) ⁻¹' A) = ∅ ∧
      A ∩ frontier A = A := by
  dsimp only
  have hpre : (Subtype.val : ({0} : Set ℝ) → ℝ) ⁻¹' ({0} : Set ℝ) = univ := by
    ext a
    simp only [mem_preimage, mem_univ, iff_true]
    exact a.property
  have hi : interior ({0} : Set ℝ) = ∅ := interior_singleton (0 : ℝ)
  have hn : ¬ IsOpen ({0} : Set ℝ) := by
    intro ho
    have he := ho.interior_eq
    rw [hi] at he
    have : (0 : ℝ) ∈ (∅ : Set ℝ) := he.symm ▸ mem_singleton (0 : ℝ)
    exact this.elim
  refine ⟨isClosed_singleton, hn, hi, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hi, inter_empty]
  · rw [hpre, interior_univ]
  · rw [hpre, interior_univ]
    simpa only [image_univ] using (Subtype.range_coe (s := ({0} : Set ℝ)))
  · rw [hpre, frontier_univ]
  · rw [frontier, isClosed_singleton.closure_eq, hi, sdiff_empty, inter_self]

end D10Topology.Ch03
