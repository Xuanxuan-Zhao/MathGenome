import MathGenome.Internal.Specs.D07.Ch14.FixedField

/-!
The dimension assertion of Artin's theorem (paper.tex:4123–4140).
`MulSemiringAction H L` for a group H is an action by field automorphisms:
each action map preserves addition, multiplication and one and has inverse
the action of the inverse group element. `FaithfulSMul` is faithfulness of
these maps. Finite dimension is a conclusion, never a hypothesis.
-/

universe u v

namespace Specs.D07.Ch14.ArtinFixedFieldFixedFieldDimension

/-- The source's general faithful finite group action formulation. -/
def FaithfulActionDimension : Prop :=
  ∀ (H : Type u) (L : Type v) [Group H] [Finite H] [Field L]
    [MulSemiringAction H L] [FaithfulSMul H L],
    FiniteDimensional (FixedPoints.subfield H L) L ∧
      Module.finrank (FixedPoints.subfield H L) L = Nat.card H

/-- The same assertion for the canonical intermediate fixed field of the
upstream interface. The base K and L/K are arbitrary, and only H is finite. -/
def SubgroupFixedFieldDimension : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (H : Subgroup (L ≃ₐ[K] L)) [Finite H],
    FiniteDimensional (FixedField.fixedFieldValue K L H) L ∧
      Module.finrank (FixedField.fixedFieldValue K L H) L = Nat.card H

end Specs.D07.Ch14.ArtinFixedFieldFixedFieldDimension
