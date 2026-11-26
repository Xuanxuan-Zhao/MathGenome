import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.DimensionConventions

open scoped TensorProduct
open IsLocalRing
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)

namespace CommutativeAlgebraNotes.Intersection.UnramifiedIntersection.Specs

open IsolatedIntersectionEuler.Specs (intersectionEuler)

universe u v w

/-- The dimension bound, strict-inequality vanishing, and equality positivity
for isolated intersections over an unramified mixed-characteristic regular
local ring. -/
def unramifiedIntersectionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [CharZero R]
    (p d : ℕ) (_ : p.Prime) [CharP (ResidueField R) p],
    ringKrullDim R = (d : WithBot ℕ∞) →
    (p : R) ∉ maximalIdeal R ^ 2 →
    ∀ (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
      [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N],
      IsFiniteLength R (M ⊗[R] N) →
        let s := moduleDimensionValue R M + moduleDimensionValue R N
        s ≤ (d : WithBot ℕ∞) ∧
          (s < (d : WithBot ℕ∞) → intersectionEuler M N = 0) ∧
          (s = (d : WithBot ℕ∞) → 0 < intersectionEuler M N)

end CommutativeAlgebraNotes.Intersection.UnramifiedIntersection.Specs
