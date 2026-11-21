import MathGenome.Internal.Specs.D07.Ch14.AutomorphismBound

/-!
Automorphism order and extension degree, K07.14.automorphism_bound.

The bound is the linear independence bound for field embeddings. Mathlib's
`IsGalois.card_aut_eq_finrank` proves the forward equality criterion using
normality and separability. Its converse uses Artin's fixed-field degree
formula and the tower law to show that the full fixed field has degree one
over the base. `IsGalois.of_fixedField_eq_bot` then applies the normal and
separable conclusion of Artin's theorem over that base. These results do
not require any characteristic restriction and include extensions of degree one.
-/

universe u v

namespace D07.Ch14.AutomorphismBound

open Specs.D07.Ch14.AutomorphismBound

theorem finite_automorphisms : FiniteAutomorphisms.{u, v} := by
  intro K L _ _ _ _
  infer_instance

theorem automorphism_bound : OrderBound.{u, v} := by
  intro K L _ _ _ _
  simpa only [Nat.card_eq_fintype_card] using (AlgEquiv.card_le (F := K) (K := L))

theorem equality_iff_galois : EqualityIffGalois.{u, v} := by
  intro K L _ _ _ _
  constructor
  · exact IsGalois.of_card_aut_eq_finrank K L
  · intro h
    let : IsGalois K L := h
    exact IsGalois.card_aut_eq_finrank K L

theorem equality_iff_fixed_field : EqualityIffFixedField.{u, v} := by
  intro K L _ _ _ _
  change Nat.card (L ≃ₐ[K] L) = Module.finrank K L ↔
    IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) = ⊥
  constructor
  · intro h
    let : IsGalois K L := (equality_iff_galois K L).mp h
    exact IsGalois.fixedField_top
  · intro h
    let : IsGalois K L := IsGalois.of_fixedField_eq_bot K L h
    exact IsGalois.card_aut_eq_finrank K L

end D07.Ch14.AutomorphismBound
