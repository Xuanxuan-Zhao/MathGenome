import MathGenome.Internal.Specs.D07.Ch09.MaximalQuotient
import MathGenome.Internal.D07.Ch09.MaximalIdeal
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! K07.09.maximal_quotient: fields are precisely maximal-ideal quotients.
The quotient and maximality are the canonical objects used upstream.
No nontriviality assumption on the ambient commutative ring is needed.
-/

universe u

namespace D07.Ch09.MaximalQuotient

open Specs.D07.Ch09.MaximalQuotient

theorem maximal_iff_isField_quotient : MaximalIffIsFieldQuotient.{u} := by
  intro R _ M
  exact Ideal.Quotient.maximal_ideal_iff_isField_quotient M

theorem maximal_iff_field_structure : MaximalIffFieldStructure.{u} := by
  intro R _ M
  rw [maximal_iff_isField_quotient R M]
  constructor
  · intro h
    exact ⟨h.toField, rfl⟩
  · rintro ⟨f, hf⟩
    change @IsField (R ⧸ M) (inferInstance : Ring (R ⧸ M)).toSemiring
    rw [← hf]
    exact @Field.toIsField (R ⧸ M) f

end D07.Ch09.MaximalQuotient
