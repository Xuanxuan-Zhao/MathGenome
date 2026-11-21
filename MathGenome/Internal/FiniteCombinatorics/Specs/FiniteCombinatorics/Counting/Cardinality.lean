import Mathlib.Data.Fintype.Card

/-!
Independent statements for Proposition p204:W01, “Cardinality and maps”.
Finite sets are represented by their element types (in particular, set subtypes).
No nonemptiness assumption is imposed on either type.
-/

namespace Specs.FiniteCombinatorics.Counting

universe u v

/-- A bijection represented as an equivalence preserves finite cardinality. -/
def card_eq_of_equiv : Prop :=
  ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B],
    (A ≃ B) → Fintype.card A = Fintype.card B

/-- The same assertion for a given map satisfying bijectivity. -/
def card_eq_of_bijective : Prop :=
  ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (f : A → B), Function.Bijective f → Fintype.card A = Fintype.card B

/-- An injection bounds the size of its domain by that of its codomain. -/
def card_le_of_injective : Prop :=
  ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (f : A → B), Function.Injective f → Fintype.card A ≤ Fintype.card B

/-- A surjection bounds the size of its codomain by that of its domain. -/
def card_le_of_surjective : Prop :=
  ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (f : A → B), Function.Surjective f → Fintype.card B ≤ Fintype.card A

/-- For every given map of equally large finite types, injectivity iff surjectivity. -/
def injective_iff_surjective_of_card_eq : Prop :=
  ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (f : A → B), Fintype.card A = Fintype.card B →
      (Function.Injective f ↔ Function.Surjective f)

/-- Under equal cardinalities, injectivity is equivalent to bijectivity. -/
def injective_iff_bijective_of_card_eq : Prop :=
  ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (f : A → B), Fintype.card A = Fintype.card B →
      (Function.Injective f ↔ Function.Bijective f)

/-- Under equal cardinalities, surjectivity is equivalent to bijectivity. -/
def surjective_iff_bijective_of_card_eq : Prop :=
  ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (f : A → B), Fintype.card A = Fintype.card B →
      (Function.Surjective f ↔ Function.Bijective f)

end Specs.FiniteCombinatorics.Counting
