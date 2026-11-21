import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.KrullTopology.FiniteKernels
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Closure.FiniteCoordinates
import Mathlib.Topology.Algebra.Group.Neighborhood

/-! # Closure through finite restrictions

The closure formulas of FT-T07. No subgroup assumption on A is used.
-/

universe u v
noncomputable section
open scoped Topology

namespace AdvancedFieldTheory.KrullTopology

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- Every finite coordinate of a point of the closure is attained in A,
and this condition suffices for membership in the closure. -/
theorem mem_closure_iff_finiteCoordinates (A : Set (L ≃ₐ[K] L)) (σ : L ≃ₐ[K] L) :
    σ ∈ closure A ↔ ∀ E : FiniteGaloisIntermediateField K L,
      restriction E.toIntermediateField σ ∈ restriction E.toIntermediateField '' A := by
  rw [mem_closure_iff_nhds_basis ((finiteGaloisKernels_nhds_one K L).nhds_of_one σ)]
  simp only [true_implies, Set.mem_ofPred_eq]
  have h (E : FiniteGaloisIntermediateField K L) (τ : L ≃ₐ[K] L) :
      τ / σ ∈ finiteGaloisKernel E ↔
        restriction E.toIntermediateField τ = restriction E.toIntermediateField σ := by
    change (restriction E.toIntermediateField) (τ / σ) = 1 ↔ _
    rw [map_div, div_eq_one]
  constructor
  · intro hall E
    obtain ⟨τ, hτA, hτ⟩ := hall E
    exact ⟨τ, hτA, (h E τ).mp hτ⟩
  · intro hall E
    obtain ⟨τ, hτA, hτ⟩ := hall E
    exact ⟨τ, hτA, (h E τ).mpr hτ⟩

/-- Closure is the intersection of the inverse images of the finite-coordinate images. -/
theorem closure_eq_iInter_finiteCoordinates (A : Set (L ≃ₐ[K] L)) :
    closure A = ⋂ E : FiniteGaloisIntermediateField K L,
      (restriction E.toIntermediateField) ⁻¹' ((restriction E.toIntermediateField) '' A) := by
  ext σ
  simp only [Set.mem_iInter, Set.mem_preimage, mem_closure_iff_finiteCoordinates]

/-- Any inclusion-cofinal collection of finite Galois stages computes the same closure. -/
theorem closure_eq_iInter_cofinal_finiteCoordinates (A : Set (L ≃ₐ[K] L))
    (S : Set (FiniteGaloisIntermediateField K L))
    (hS : ∀ E : FiniteGaloisIntermediateField K L, ∃ D ∈ S, E ≤ D) :
    closure A = ⋂ D ∈ S,
      (restriction D.toIntermediateField) ⁻¹' ((restriction D.toIntermediateField) '' A) := by
  ext σ
  simp only [Set.mem_iInter, Set.mem_preimage, mem_closure_iff_finiteCoordinates]
  constructor
  · intro h D _
    exact h D
  · intro h E
    obtain ⟨D, hDS, hED⟩ := hS E
    obtain ⟨τ, hτA, hτD⟩ := h D hDS
    refine ⟨τ, hτA, ?_⟩
    have hcomp := restriction_comp hED
    change restriction E.toIntermediateField τ = restriction E.toIntermediateField σ
    rw [hcomp]
    exact congrArg (stageRestriction hED) hτD

end AdvancedFieldTheory.KrullTopology
