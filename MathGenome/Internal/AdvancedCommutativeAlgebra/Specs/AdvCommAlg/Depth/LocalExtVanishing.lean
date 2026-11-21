import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.Depth.Basic
import Mathlib.RingTheory.KrullDimension.Module

/-! Independent statement of the local assertion in DP-11,
paper.tex:3026–3030, with proof at 3042–3047.

Ext degrees are natural numbers. For nonzero finite modules over a Noetherian
local ring the depth and support dimension are finite nonnegative integers.
Thus `i + dim Supp N < depth M` is precisely the source range
`0 ≤ i < depth M - dim Supp N` in integer arithmetic. It also retains the
vacuous case when the difference is nonpositive. `Subsingleton` expresses
vanishing of the actual Ext group in the category of all modules.
-/

universe u
open CategoryTheory CategoryTheory.Abelian
namespace AdvCommAlg.Depth.Specs

def ext_subsingleton_of_add_supportDim_lt_depthType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (N M : ModuleCat.{u} R) [Module.Finite R N] [Module.Finite R M]
    [Nontrivial N] [Nontrivial M] (i : ℕ),
    (i : WithBot ℕ∞) + Module.supportDim R N < (depthValue R M : WithBot ℕ∞) →
      Subsingleton (Ext N M i)

end AdvCommAlg.Depth.Specs
