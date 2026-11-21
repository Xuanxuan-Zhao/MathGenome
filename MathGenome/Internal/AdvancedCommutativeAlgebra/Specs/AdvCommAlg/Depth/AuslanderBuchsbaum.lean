import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.Noetherian.Defs

/-! Independent statement of paper.tex DP-13, equality (3109–3115).
Projective dimension uses Mathlib's categorical invariant, with the zero
object in degree minus infinity. The natural number e expresses exactly
finite projective dimension for the nonzero module in the statement.
Depth is the source's regular-length invariant from DP-01. -/

universe u
open CategoryTheory
namespace AdvCommAlg.Depth.Specs

def auslanderBuchsbaumType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (e : ℕ), projectiveDimension M = (e : WithBot ℕ∞) →
      (e : ℕ∞) + depthValue R M = depthValue R R

end AdvCommAlg.Depth.Specs
