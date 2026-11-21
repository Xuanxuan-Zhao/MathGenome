import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.FiniteKernels

/-! Independent specification of the two initial-topology assertions of FT-T03,
notes/003/advanced-field-theory.tex:433–450. The topology on the ambient
Galois group is the Krull topology; every target below explicitly has the
bottom (discrete) topology. The arbitrary source space expresses the full
universal property of each initial topology. -/

universe u v w
noncomputable section
set_option linter.checkUnivs false

namespace Specs.AdvancedFieldTheory.KrullTopology

def continuous_iff_evaluations_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {X : Type w} [TopologicalSpace X] (f : X → (L ≃ₐ[K] L)),
    Continuous f ↔ ∀ x : L, @Continuous X L _ ⊥ (fun z => f z x)

def continuous_iff_finiteRestrictions_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {X : Type w} [TopologicalSpace X] (f : X → (L ≃ₐ[K] L)),
    Continuous f ↔ ∀ E : FiniteGaloisIntermediateField K L,
      @Continuous X (E ≃ₐ[K] E) _ ⊥
        (fun z => Specs.AdvancedFieldTheory.restriction_value E.toIntermediateField (f z))

end Specs.AdvancedFieldTheory.KrullTopology
