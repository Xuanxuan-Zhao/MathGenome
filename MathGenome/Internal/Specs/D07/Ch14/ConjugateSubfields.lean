import MathGenome.Internal.Specs.D07.Ch14.FixedField

/-!
Independent specification of K07.14.conjugate_subfields, paper.tex:4182–4190.
The chosen K-algebra structure records the base embedding into L. The image
`E.map σ.toAlgHom` is precisely σ(E). The image of the fixing subgroup under
`MulAut.conj σ` is precisely {σ * τ * σ⁻¹ | τ fixes E pointwise}, with
automorphism multiplication given by left function composition.
No finite-degree, algebraicity, normality or separability hypothesis is needed.
-/

universe u v

namespace Specs.D07.Ch14.ConjugateSubfields

/-- The conjugation direction expressed by pointwise fixation. -/
def FixesImageIff : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (σ τ : L ≃ₐ[K] L),
    τ ∈ (E.map σ.toAlgHom).fixingSubgroup ↔
      σ⁻¹ * τ * σ ∈ E.fixingSubgroup

/-- Equality of the full fixing subgroups, not just one inclusion. -/
def ConjugateFixingSubgroup : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (σ : L ≃ₐ[K] L),
    (E.map σ.toAlgHom).fixingSubgroup =
      E.fixingSubgroup.map (MulAut.conj σ).toMonoidHom

end Specs.D07.Ch14.ConjugateSubfields
