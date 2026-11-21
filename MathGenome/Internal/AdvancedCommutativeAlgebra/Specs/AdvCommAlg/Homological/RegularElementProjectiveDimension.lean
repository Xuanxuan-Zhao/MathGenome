import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.QuotSMulTop

/-! Independent statement of the same-ring quotient assertion in paper.tex,
Theorem DP-13, lines 3116–3117. The quotient is by the image xM of scalar
multiplication, and projective dimension is taken over R on both sides.
There is no regularity hypothesis on x acting on R. -/

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

universe u

namespace Specs.AdvCommAlg

/-- Quotienting a nonzero finite module of projective dimension e by an
injective scalar in the maximal ideal raises its projective dimension by one,
including when e = 0. -/
def projectiveDimension_quotient_regularElement : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (e : ℕ), projectiveDimension M = (e : WithBot ℕ∞) →
    ∀ (x : R), x ∈ IsLocalRing.maximalIdeal R →
      Function.Injective (fun m : M => x • m) →
      projectiveDimension (ModuleCat.of R (M ⧸ x • (⊤ : Submodule R M))) =
        ((e + 1 : ℕ) : WithBot ℕ∞)

end Specs.AdvCommAlg
