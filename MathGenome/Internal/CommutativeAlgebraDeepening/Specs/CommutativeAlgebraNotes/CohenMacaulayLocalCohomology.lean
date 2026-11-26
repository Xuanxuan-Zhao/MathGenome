import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Definitions

open CategoryTheory.Limits

namespace Specs.CommutativeAlgebraNotes.CohenMacaulayLocalCohomology

universe u

/-- For a nonzero finite module over a Noetherian local ring, top local cohomology
is nonzero, and vanishing in every other degree is equivalent to Cohen–Macaulayness. -/
def moduleCriterionType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M],
    ∃ d : ℕ, Module.supportDim R M = (d : WithBot ℕ∞) ∧
      Nontrivial ((IdealTorsion.localCohomology (IsLocalRing.maximalIdeal R) (d : ℤ)).obj M) ∧
      (AdvCommAlg.CohenMacaulay.LocalCohenMacaulay R M ↔
        ∀ q : ℤ, q ≠ (d : ℤ) →
          IsZero ((IdealTorsion.localCohomology (IsLocalRing.maximalIdeal R) q).obj M))

/-- The criterion for a Noetherian local ring as a module over itself. -/
def ringCriterionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) ∧
      Nontrivial
        ((IdealTorsion.localCohomology (IsLocalRing.maximalIdeal R) (d : ℤ)).obj
          (ModuleCat.of R R)) ∧
      (AdvCommAlg.CohenMacaulay.LocalCohenMacaulay R R ↔
        ∀ q : ℤ, q ≠ (d : ℤ) →
          IsZero ((IdealTorsion.localCohomology (IsLocalRing.maximalIdeal R) q).obj
            (ModuleCat.of R R)))

end Specs.CommutativeAlgebraNotes.CohenMacaulayLocalCohomology
