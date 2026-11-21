import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations

/-!
Independent specification of the finite restriction sequence, FT-F01,
notes/003/advanced-field-theory.tex:149–151.
M is an arbitrary literal intermediate field which is Galois over K.
The intrinsic group Gal(E/M) is embedded by forgetting M-linearity.
-/

universe u v

noncomputable section

namespace Specs.AdvancedFieldTheory

def finiteRestriction_type := ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M],
    (E ≃ₐ[K] E) →* (M ≃ₐ[K] M)

def finiteRestriction_value : finiteRestriction_type :=
  fun {K} {E} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] M [IsGalois K M] =>
      AlgEquiv.restrictNormalHom M

def finiteRestriction_apply_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M],
    ∀ (σ : E ≃ₐ[K] E) (x : M),
      ((AlgEquiv.restrictNormalHom M σ x : M) : E) = σ (x : E)

def finiteRestriction_surjective_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M],
    Function.Surjective (AlgEquiv.restrictNormalHom M : (E ≃ₐ[K] E) →* (M ≃ₐ[K] M))

def finiteRestriction_ker_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M],
    (AlgEquiv.restrictNormalHom M : (E ≃ₐ[K] E) →* (M ≃ₐ[K] M)).ker = M.fixingSubgroup

def finiteRestriction_intrinsic_injective_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M],
    Function.Injective (AlgEquiv.restrictScalarsHom K : (E ≃ₐ[M] E) →* (E ≃ₐ[K] E))

def finiteRestriction_ker_eq_range_type : Prop :=
  ∀ {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M],
    (AlgEquiv.restrictNormalHom M : (E ≃ₐ[K] E) →* (M ≃ₐ[K] M)).ker =
      (AlgEquiv.restrictScalarsHom K : (E ≃ₐ[M] E) →* (E ≃ₐ[K] E)).range

end Specs.AdvancedFieldTheory
