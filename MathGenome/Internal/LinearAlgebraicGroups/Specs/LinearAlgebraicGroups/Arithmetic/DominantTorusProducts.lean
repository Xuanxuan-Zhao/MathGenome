import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.DominantTorusProducts

open GeometricRadicals (IsSemisimple IsTorus)

noncomputable section

/-- Multiplication of the subgroup factors in the order of their finite index. -/
def orderedSubgroupProduct {k : Type u} [Field k] {m : ℕ} {G : AffineAlgebraicGroup k}
    (T : Fin m → ClosedSubgroup G.val) :
    (∏ᶜ fun i => (T i).group.X) ⟶ G.val.X :=
  (List.ofFn (fun i => Pi.π (fun j => (T j).group.X) i ≫ (T i).inclusion.hom.hom)).prod

/-- A finite ordered product of rational tori maps dominantly to the group. -/
def DominantOrderedTorusProducts : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k), IsSemisimple G →
    ∃ (m : ℕ) (T : Fin m → ClosedSubgroup G.val),
      (∀ i, IsTorus (T i).group) ∧ IsDominant (orderedSubgroupProduct T).left

end

end LinearAlgebraicGroups.Specs.DominantTorusProducts
