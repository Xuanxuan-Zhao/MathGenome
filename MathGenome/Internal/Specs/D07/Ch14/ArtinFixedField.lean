import MathGenome.Internal.Specs.D07.Ch14.ArtinFixedFieldFixedFieldDimension

/-!
Independent specification of K07.14.artin_fixed_field, paper.tex:4123–4144.

A group action by `MulSemiringAction` consists of field automorphisms (the
inverse map is the action of the inverse group element). `FaithfulSMul`
expresses faithfulness. The fixed field is the actual subfield of elements
fixed by every group element, with its inclusion into L as scalar map.
Only the group is finite in the hypotheses; finite extension degree is a
conclusion. `IsGalois` asserts normality and algebraic separability, with
the same canonical predicates as the upstream Chapter 12 specifications.
The final clause uses the action homomorphism itself, so it asserts that
every fixed-field automorphism is an action map, including the prescribed
left-composition convention. The trivial acting group is allowed.
-/

universe u v

namespace Specs.D07.Ch14.ArtinFixedField

/-- Artin's theorem for an arbitrary faithful finite group action. -/
def FaithfulActionArtin : Prop :=
  ∀ (H : Type u) (L : Type v) [Group H] [Finite H] [Field L]
    [MulSemiringAction H L] [FaithfulSMul H L],
    FiniteDimensional (FixedPoints.subfield H L) L ∧
      IsGalois (FixedPoints.subfield H L) L ∧
      Module.finrank (FixedPoints.subfield H L) L = Nat.card H ∧
      Function.Bijective
        (MulSemiringAction.toAlgAut H (FixedPoints.subfield H L) L)

/-- The canonical intermediate-field version, compatible with the accepted
fixed-field interface. Each F-automorphism has exactly the underlying map
of a member of H. No finite-degree assumption on L/K is added. -/
def SubgroupArtin : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (H : Subgroup (L ≃ₐ[K] L)) [Finite H],
    let F := FixedField.fixedFieldValue K L H
    FiniteDimensional F L ∧ IsGalois F L ∧
      Module.finrank F L = Nat.card H ∧
      ∀ σ : L ≃ₐ[F] L, ∃ h : H, ∀ x : L, σ x = h.val x

end Specs.D07.Ch14.ArtinFixedField
