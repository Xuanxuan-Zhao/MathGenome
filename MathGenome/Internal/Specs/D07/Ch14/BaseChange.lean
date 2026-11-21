import Mathlib.FieldTheory.Galois.Basic

/-!
Independent specification of K07.14.base_change (paper.tex:4230–4243).
The common overfield Ω is arbitrary. E and F are arbitrary intermediate
fields over K with their specified embeddings into Ω; E ⊔ F is their
compositum and E ⊓ F their intersection. Inclusions give the scalar actions
used below. There is no algebraicity or finiteness premise on F except in
the last assertion. `IsGalois` means normal and algebraically separable.
The equation accompanying the group equivalence specifies restriction on
every element of E, so an unrelated abstract group isomorphism is insufficient.
-/

universe u v
namespace Specs.D07.Ch14.BaseChange

open IntermediateField

def FiniteGaloisBaseChange : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E],
    letI : Algebra F ↥(E ⊔ F) := (inclusion le_sup_right).toAlgebra
    FiniteDimensional F ↥(E ⊔ F) ∧ IsGalois F ↥(E ⊔ F)

def RestrictionIsomorphism : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E],
    letI : Algebra F ↥(E ⊔ F) := (inclusion le_sup_right).toAlgebra
    letI : Algebra ↥(E ⊓ F) E := (inclusion inf_le_left).toAlgebra
    ∃ e : (↥(E ⊔ F) ≃ₐ[F] ↥(E ⊔ F)) ≃* (E ≃ₐ[↥(E ⊓ F)] E),
      ∀ (σ : ↥(E ⊔ F) ≃ₐ[F] ↥(E ⊔ F)) (x : E),
        (e σ x : Ω) = (σ (inclusion le_sup_left x) : Ω)

def CompositumDegreeFormula : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K F],
    Module.finrank K ↥(E ⊔ F) * Module.finrank K ↥(E ⊓ F) =
      Module.finrank K E * Module.finrank K F

end Specs.D07.Ch14.BaseChange
