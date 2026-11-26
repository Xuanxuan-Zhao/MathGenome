import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open Specs.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement
open Specs.CommutativeAlgebraNotes.IdealTorsion

namespace Specs.CommutativeAlgebraNotes.LocalCohomologyOfComplement

universe u

/-- The coefficient module identifies with the sections on the whole spectrum.
Compose this identification with restriction to the open complement. -/
noncomputable abbrev complementRestriction (R : CommRingCat.{u}) (I : Ideal R) :
    𝟭 (ModuleCat.{u} R) ⟶ tilde.functor R ⋙ sections R (complement R I) :=
  toSections R ⊤ ≫ whiskerLeft (tilde.functor R)
    (restrict R (le_top : complement R I ≤ ⊤))

/-- The natural exact sequence for the open complement. The first arrow is the
torsion inclusion under the canonical comparison with zeroth derived torsion. -/
def ComplementExactSequence : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R),
    ∃ (e : idealTorsionFunctor I ≅ localCohomology.{u} I 0)
      (δ : tilde.functor R ⋙ sections R (complement R I) ⟶ localCohomology.{u} I 1),
      e.hom = (idealTorsionFunctor I).toRightDerivedZero ∧
      ∀ M : ModuleCat.{u} R,
        let a := (e.inv ≫ idealTorsionInclusion I).app M
        let b := (complementRestriction R I).app M
        Function.Injective a ∧ Function.Exact a b ∧
          Function.Exact b (δ.app M) ∧ Function.Surjective (δ.app M)

attribute [local instance] HasDerivedCategory.standard

/-- Positive cohomology of the associated sheaf on the open complement is
naturally the next degree of local cohomology. Derived sections retain the
action of the base ring, so these isomorphisms are R-linear. -/
def ComplementHigherCohomology : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R) (q : ℤ), 1 ≤ q →
    Nonempty ((derivedSections R (complement R I) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} R) q) ≅
        localCohomology.{u} I (q + 1))

end Specs.CommutativeAlgebraNotes.LocalCohomologyOfComplement
