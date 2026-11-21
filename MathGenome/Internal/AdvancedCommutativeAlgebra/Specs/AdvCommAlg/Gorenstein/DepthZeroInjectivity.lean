import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.Algebra.Category.ModuleCat.Ext.Baer

/-! Independent specification of the last assertion of GC-05.
Depth is the source's regular-length depth. Finiteness of injective
 dimension means that the categorical dimension is not infinity; this
includes the zero module, whose dimension is bottom. -/

universe u
open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Gorenstein.DepthZeroInjectivity.Specs

def injective_of_depth_zero_of_finite_injectiveDimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R],
    AdvCommAlg.Depth.Specs.depthValue R R = 0 →
    ∀ (N : ModuleCat.{u} R) [Module.Finite R N],
      injectiveDimension N ≠ ⊤ → Injective N

end AdvCommAlg.Gorenstein.DepthZeroInjectivity.Specs
