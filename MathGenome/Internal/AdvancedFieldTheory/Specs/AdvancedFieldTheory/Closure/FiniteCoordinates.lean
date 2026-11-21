import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.FiniteKernels

/-! Independent statements of the closure formulas in FT-T07,
notes/003/advanced-field-theory.tex:577–597. The automorphism group carries
its canonical Krull topology. The set A is arbitrary; cofinality means
inclusion-cofinality in all finite Galois intermediate fields. -/

universe u v
noncomputable section
open scoped Topology

namespace Specs.AdvancedFieldTheory.KrullTopology

def closure_eq_iInter_finiteCoordinates_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (A : Set (L ≃ₐ[K] L)),
    closure A = ⋂ E : FiniteGaloisIntermediateField K L,
      (Specs.AdvancedFieldTheory.restriction_value E.toIntermediateField) ⁻¹'
        ((Specs.AdvancedFieldTheory.restriction_value E.toIntermediateField) '' A)

def closure_eq_iInter_cofinal_finiteCoordinates_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (A : Set (L ≃ₐ[K] L)) (S : Set (FiniteGaloisIntermediateField K L)),
    (∀ E : FiniteGaloisIntermediateField K L, ∃ D ∈ S, E ≤ D) →
    closure A = ⋂ D ∈ S,
      (Specs.AdvancedFieldTheory.restriction_value D.toIntermediateField) ⁻¹'
        ((Specs.AdvancedFieldTheory.restriction_value D.toIntermediateField) '' A)

end Specs.AdvancedFieldTheory.KrullTopology
