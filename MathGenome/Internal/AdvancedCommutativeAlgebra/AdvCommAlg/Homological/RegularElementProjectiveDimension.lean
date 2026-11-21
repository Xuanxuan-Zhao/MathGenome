import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Homological.RegularElementProjectiveDimension
import Mathlib.RingTheory.Regular.ProjectiveDimension

/-! Same-ring regular-element quotient assertion of paper.tex, DP-13.
Mathlib's result uses the exact sequence M --x--> M --> M/xM and
finite Ext modules with Nakayama. It assumes injectivity only on M. -/

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

universe u

namespace AdvCommAlg

/-- For x regular on M in the maximal ideal, pd_R(M/xM) = pd_R(M) + 1.
This finite-dimension formulation retains the nonzero hypothesis of DP-13. -/
theorem projectiveDimension_quotient_regularElement
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (e : ℕ) (he : projectiveDimension M = (e : WithBot ℕ∞))
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : Function.Injective (fun m : M => x • m)) :
    projectiveDimension (ModuleCat.of R (M ⧸ x • (⊤ : Submodule R M))) =
      ((e + 1 : ℕ) : WithBot ℕ∞) := by
  have reg : IsSMulRegular M x := hreg
  simpa only [he, Nat.cast_add, Nat.cast_one] using
    ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular M x reg hx

end AdvCommAlg
