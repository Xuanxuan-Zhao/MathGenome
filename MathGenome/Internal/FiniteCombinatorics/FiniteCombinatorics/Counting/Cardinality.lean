import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.Cardinality
import Mathlib.Data.Fintype.EquivFin

/-! Proposition p204:W01: finite cardinality and maps, including empty types. -/

namespace FiniteCombinatorics.Counting

universe u v

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]

theorem card_eq_of_equiv (e : A ≃ B) : Fintype.card A = Fintype.card B :=
  Fintype.card_congr e

theorem card_eq_of_bijective (f : A → B) (hf : Function.Bijective f) :
    Fintype.card A = Fintype.card B :=
  Fintype.card_of_bijective hf

theorem card_le_of_injective (f : A → B) (hf : Function.Injective f) :
    Fintype.card A ≤ Fintype.card B :=
  Fintype.card_le_of_injective f hf

theorem card_le_of_surjective (f : A → B) (hf : Function.Surjective f) :
    Fintype.card B ≤ Fintype.card A :=
  Fintype.card_le_of_surjective f hf

theorem injective_iff_surjective_of_card_eq (f : A → B)
    (hcard : Fintype.card A = Fintype.card B) :
    Function.Injective f ↔ Function.Surjective f :=
  Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)

theorem injective_iff_bijective_of_card_eq (f : A → B)
    (hcard : Fintype.card A = Fintype.card B) :
    Function.Injective f ↔ Function.Bijective f := by
  constructor
  · intro hf
    exact ⟨hf, (injective_iff_surjective_of_card_eq f hcard).mp hf⟩
  · exact fun hf => hf.1

theorem surjective_iff_bijective_of_card_eq (f : A → B)
    (hcard : Fintype.card A = Fintype.card B) :
    Function.Surjective f ↔ Function.Bijective f := by
  constructor
  · intro hf
    exact ⟨(injective_iff_surjective_of_card_eq f hcard).mpr hf, hf⟩
  · exact fun hf => hf.2

end FiniteCombinatorics.Counting
