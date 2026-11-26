import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.DimensionConventions
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs

open scoped TensorProduct
open IsLocalRing
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)

namespace CommutativeAlgebraNotes.Intersection.RamifiedIntersectionDimension.Specs

universe u v w

/-- Serre's dimension bound for nonzero finite modules with finite-length
tensor product over a ramified mixed-characteristic regular local ring. -/
def ramifiedIntersectionDimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [CharZero R]
    (p d : ℕ) (_ : p.Prime) [CharP (ResidueField R) p],
    ringKrullDim R = (d : WithBot ℕ∞) →
    (p : R) ∈ maximalIdeal R ^ 2 →
    ∀ (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
      [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N],
      IsFiniteLength R (M ⊗[R] N) →
        moduleDimensionValue R M + moduleDimensionValue R N ≤ (d : WithBot ℕ∞)

end CommutativeAlgebraNotes.Intersection.RamifiedIntersectionDimension.Specs
