import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped IntermediateField

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalInnerSplitSubtorus

open CharacterDescent (Cocharacter)
open GeometricRadicals (IsSplitTorus)
open SchemeDerivedGroup (IsSubgroupOf)

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient automorphism on the underlying scheme of the scalar extension. -/
noncomputable def coefficientChange (τ : Gal(K/F)) (X : GroupScheme F) :
    ((groupBaseChange F K).obj X).X.left ⟶ ((groupBaseChange F K).obj X).X.left :=
  pullback.lift
    (pullback.fst X.X.hom (fieldSpecMap F K))
    (pullback.snd X.X.hom (fieldSpecMap F K) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom))
    (by
      have h : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ fieldSpecMap F K =
          fieldSpecMap F K := by
        rw [← Spec.map_comp]
        congr 1
        ext a
        exact τ.commutes a
      rw [Category.assoc, h, pullback.condition])

/-- Descent of the largest split subtorus and its integral cocharacter lattice. -/
def LargestSplitSubtorus : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (τ : Gal(K/F)), Subgroup.zpowers τ = ⊤ →
    ∀ (U : AffineAlgebraicGroup F) (A : GroupScheme F), IsSplitTorus A →
    ∀ (i : (groupBaseChange F K).obj U.val ≅ (groupBaseChange F K).obj A)
      (b : (groupBaseChange F K).obj A ≅ (groupBaseChange F K).obj A),
    i.hom.hom.hom.left ≫ coefficientChange τ A ≫ b.hom.hom.hom.left =
      coefficientChange τ U.val ≫ i.hom.hom.hom.left →
    ∃ S : ClosedSubgroup U.val, IsSplitTorus S.group ∧
      (∀ R : ClosedSubgroup U.val, IsSplitTorus R.group → IsSubgroupOf R S) ∧
      let f : Cocharacter ((groupBaseChange F K).obj S.group) →
          Cocharacter ((groupBaseChange F K).obj A) :=
        fun η ↦ η ≫ (groupBaseChange F K).map S.inclusion ≫ i.hom
      Function.Injective f ∧ Set.range f = { μ | μ ≫ b.hom = μ }

end LinearAlgebraicGroups.Specs.ExceptionalInnerSplitSubtorus
