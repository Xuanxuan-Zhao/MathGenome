import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.TorusSections

open EquivariantUnipotentSeries (IsSplitTorus)
open Unipotent (IsUnipotent closedSubgroupAlgebraicGroup)

/-- A faithfully flat extension of a split torus by a smooth connected
unipotent group over a perfect field admits a group-scheme section.
Every two group-scheme sections are conjugate by a rational point of
the kernel. The monoidal unit of schemes over `k` is `Spec k`. -/
def SplitTorusExtension : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (G T : AffineAlgebraicGroup k)
    (U : ClosedSubgroup G.val) (p : G.val ⟶ T.val),
    IsSchemeKernel p U →
    Flat p.hom.hom.left → Surjective p.hom.hom.left →
    IsSplitTorus T.val →
    Smooth U.group.X.hom → ConnectedSpace U.group.X.left →
    IsUnipotent (closedSubgroupAlgebraicGroup U) →
    (∃ s : T.val ⟶ G.val, s ≫ p = 𝟙 T.val) ∧
    ∀ s₁ s₂ : T.val ⟶ G.val, s₁ ≫ p = 𝟙 T.val → s₂ ≫ p = 𝟙 T.val →
      ∃ a : 𝟙_ (SchemeOver k) ⟶ U.group.X,
        let g : T.val.X ⟶ G.val.X := toUnit T.val.X ≫ a ≫ U.inclusion.hom.hom
        s₂.hom.hom = g * s₁.hom.hom * g⁻¹

end LinearAlgebraicGroups.Specs.TorusSections
