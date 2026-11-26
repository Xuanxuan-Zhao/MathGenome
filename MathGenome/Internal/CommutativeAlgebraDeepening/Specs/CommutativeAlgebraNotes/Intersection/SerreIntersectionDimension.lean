import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.DimensionConventions
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.RegularLocalRing.Defs

open scoped TensorProduct
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)

namespace CommutativeAlgebraNotes.Intersection.SerreIntersectionDimension.Specs

universe u v w

/-- Serre's dimension bound for an isolated intersection over a regular local ring. -/
def dimensionBoundType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N],
    IsFiniteLength R (M ⊗[R] N) →
      moduleDimensionValue R M + moduleDimensionValue R N ≤ ringKrullDim R

/-- The height bound at a prime minimal over the sum of two prime ideals. -/
def heightBoundType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (p q r : Ideal R) [p.IsPrime] [q.IsPrime],
    r ∈ (p + q).minimalPrimes → r.height ≤ p.height + q.height

end CommutativeAlgebraNotes.Intersection.SerreIntersectionDimension.Specs
