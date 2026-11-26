import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.Definitions
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! Projective dimension bounds at an isolated intersection (Corollary 7.15). -/

open CategoryTheory
open scoped TensorProduct

namespace CommutativeAlgebraNotes.Intersection.ProjectiveDimensionWithIsolatedSupport.Specs

universe u v w

/-- Finite projective dimension bounds the depth of the other module. -/
def depthBoundType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{max u v} R) (N : ModuleCat.{max u w} R)
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N],
    IsFiniteLength R (M ⊗[R] N) → projectiveDimension M ≠ ⊤ →
    (AdvCommAlg.Depth.depth R N : WithBot ℕ∞) ≤ projectiveDimension M

/-- The dimension bound for a Cohen–Macaulay coefficient module. The equality
of depth and dimension expresses local Cohen–Macaulayness for nonzero finite
modules, as in `AdvCommAlg.CohenMacaulay.localCohenMacaulay_iff_sourceDepth`. -/
def cohenMacaulayDimensionBoundType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{max u v} R) (N : ModuleCat.{max u w} R)
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N],
    IsFiniteLength R (M ⊗[R] N) → projectiveDimension M ≠ ⊤ →
    (AdvCommAlg.Depth.depth R N : WithBot ℕ∞) = Module.supportDim R N →
    Module.supportDim R N ≤ projectiveDimension M

/-- Over a regular local ring the dimension bound holds for every such pair. -/
def regularLocalDimensionBoundType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{max u v} R) (N : ModuleCat.{max u w} R)
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N],
    IsFiniteLength R (M ⊗[R] N) →
    Module.supportDim R N ≤ projectiveDimension M

end CommutativeAlgebraNotes.Intersection.ProjectiveDimensionWithIsolatedSupport.Specs
