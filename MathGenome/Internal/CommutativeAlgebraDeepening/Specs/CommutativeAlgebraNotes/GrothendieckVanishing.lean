import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Noetherian.Basic

open CategoryTheory CategoryTheory.Limits

namespace Specs.CommutativeAlgebraNotes.GrothendieckVanishing

universe u

/-- The zero module has zero local cohomology in every integer degree. -/
def zeroModuleType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : ModuleCat.{u} R), Subsingleton M → ∀ q : ℤ,
    IsZero ((IdealTorsion.localCohomology I q).obj M)

/-- Grothendieck vanishing. The bound on the support dimension is by a finite
natural number strictly below the degree, with a separate clause for empty support
(which has dimension `⊥`). -/
def vanishingType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (q : ℤ),
    (Module.supportDim R M = ⊥ ∨
      ∃ d : ℕ, Module.supportDim R M ≤ (d : WithBot ℕ∞) ∧ (d : ℤ) < q) →
    IsZero ((IdealTorsion.localCohomology I q).obj M)

end Specs.CommutativeAlgebraNotes.GrothendieckVanishing
