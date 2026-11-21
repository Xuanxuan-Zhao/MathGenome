import MathGenome.Internal.Specs.D07.Ch12.NormalDefinition

/-!
# Normal extensions

K07.12.normal_definition, paper.tex:3836–3848.

For the forward implication, each algebraic element has an irreducible
minimal polynomial with that element as a root. Conversely, an irreducible
polynomial with root a is a nonzero scalar multiple of `minpoly K a`;
mapping coefficients and multiplying by a constant preserve splitting.
This works in arbitrary algebraic extensions, including infinite ones,
and does not assume separability.
-/

universe u v

namespace D07.Ch12.NormalDefinition

open Specs.D07.Ch12.NormalDefinition

theorem irreducibleCriterionIffMinimalPolynomialCriterion :
    IrreducibleCriterionIffMinimalPolynomialCriterion.{u, v} := by
  intro K L _ _ _ hAlg
  constructor
  · intro h a
    exact h (minpoly K a) (minpoly.irreducible (hAlg.isAlgebraic a).isIntegral)
      ⟨a, minpoly.aeval K a⟩
  · intro h f hf hRoot
    obtain ⟨a, ha⟩ := hRoot
    rw [minpoly.Irreducible.eq_minpoly hf ha, Polynomial.map_mul, Polynomial.map_C]
    exact (h a).C_mul _

theorem normalIffMinimalPolynomialSplits :
    NormalIffMinimalPolynomialSplits.{u, v} := by
  intro K L _ _ _ hAlg
  constructor
  · exact fun h a => h.splits a
  · intro h
    exact { toIsAlgebraic := hAlg, splits' := h }

theorem normalExtensionCharacterization :
    NormalExtensionCharacterization.{u, v} := by
  intro K L _ _ _
  constructor
  · intro h
    refine ⟨h.toIsAlgebraic, ?_⟩
    exact (irreducibleCriterionIffMinimalPolynomialCriterion K L h.toIsAlgebraic).mpr
      (fun a => h.splits a)
  · rintro ⟨hAlg, h⟩
    exact (normalIffMinimalPolynomialSplits K L hAlg).mpr
      ((irreducibleCriterionIffMinimalPolynomialCriterion K L hAlg).mp h)

end D07.Ch12.NormalDefinition
