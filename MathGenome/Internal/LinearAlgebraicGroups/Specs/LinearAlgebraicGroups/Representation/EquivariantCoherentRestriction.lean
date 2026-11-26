import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.EquivariantCoherentRestriction

open EquivariantAffineModules

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y Z : SchemeOver k}
variable {a : ModObj T.X X} {b : ModObj T.X Z} {c : ModObj T.X Y}

/-- The maps in the localization sequence come from closed direct image and
open restriction with their scheme-theoretic equivariance. -/
def HasRestrictionSequence (i : Z ⟶ X) (j : Y ⟶ X) : Prop :=
  ∃ (push : GZero b →ₗ[CharacterRing T] GZero a)
    (res : GZero a →ₗ[CharacterRing T] GZero c),
    Function.Exact push res ∧ Function.Surjective res ∧
    (∀ H, ∃ (F : EquivariantCoherent a) (e : F.sheaf ≅
      (Scheme.Modules.pushforward i.left).obj H.sheaf),
      IsEquivariantPushforward i H F e ∧ push (classOf H) = classOf F) ∧
    (∀ F, ∃ (H : EquivariantCoherent c) (e : Pull j F.sheaf ≅ H.sheaf),
      IsEquivariantPullback j F H e ∧ res (classOf F) = classOf H)

/-- The right exact localization sequence for a split torus action and an
arbitrary invariant closed subscheme with its open complement. -/
def RestrictionSequence : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {X Y Z : SchemeOver k}
    (a : ModObj T.X X) (b : ModObj T.X Z) (c : ModObj T.X Y)
    (i : Z ⟶ X) (j : Y ⟶ X),
    IsSplitTorus T →
    LocallyOfFiniteType X.hom → IsSeparated X.hom → CompactSpace X.left →
    (∀ x : X.left, ∃ U : X.left.Opens,
      x ∈ U ∧ IsAffineOpen U ∧ a.smul.left ⁻¹ᵁ U = (snd T.X X).left ⁻¹ᵁ U) →
    IsClosedImmersion i.left → IsOpenImmersion j.left →
    IsEquivariantMap a b i → IsEquivariantMap a c j →
    Set.range j.left = (Set.range i.left)ᶜ →
    HasRestrictionSequence (a := a) (b := b) (c := c) i j

end LinearAlgebraicGroups.Specs.EquivariantCoherentRestriction
