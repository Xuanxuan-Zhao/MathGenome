import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.EquivariantPointGlobalSections

open CharacterDescent (Character)
open EquivariantAffineModules
open FlagCohomology (sectionsFunctor structureModule)

/-- The global sections of the equivariant direct image of the trivial
structure line at a rational fixed closed point carry the trivial character.
The weight equation uses the full product with the torus, including over
finite ground fields. -/
def PointGlobalSections : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} (_hT : IsSplitTorus T)
    {X : SchemeOver k} {a : ModObj T.X X} (x : 𝟙_ (SchemeOver k) ⟶ X)
    [IsClosedImmersion x.left]
    (H : EquivariantCoherent (ModObj.trivialAction T.X (𝟙_ (SchemeOver k))))
    (_ : H.sheaf ≅ structureModule (𝟙_ (SchemeOver k) : SchemeOver k).left)
    (F : EquivariantCoherent a)
    (e : F.sheaf ≅ (Scheme.Modules.pushforward x.left).obj H.sheaf),
    H.lin.iso.hom = (pullCongr H.sheaf
      (rfl : snd T.X (𝟙_ (SchemeOver k)) = (ModObj.trivialAction T.X (𝟙_ (SchemeOver k))).smul)).hom →
    IsEquivariantPushforward x H F e →
    Nonempty ((sectionsFunctor X).obj F.sheaf ≅ ModuleCat.of k k) ∧
      ∀ (s : Γ(F.sheaf, ⊤)) (χ : Character T),
        HasSectionWeight F.lin s χ ↔ χ = 1 ∨ s = 0

end LinearAlgebraicGroups.Specs.EquivariantPointGlobalSections
