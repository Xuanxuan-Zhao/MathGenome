import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.AugmentedCechComplex
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

open CategoryTheory HomologicalComplex

namespace Specs.CommutativeAlgebraNotes.DerivedCechComparison

universe u w

/-- The actual Čech tensor functor descends to the bounded-below derived category,
where it is naturally isomorphic to the right derived torsion functor. The
first isomorphism identifies the descended functor on all bounded-below
complexes with the localization of their Čech tensor products. -/
def DerivedComparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (rs : List R), Ideal.span {r | r ∈ rs} = I →
    ∃ T : DerivedCategory.Plus (ModuleCat.{u} R) ⥤ DerivedCategory.Plus (ModuleCat.{u} R),
      Nonempty (((DerivedCategory.Plus.Q ⋙ T) ⋙ DerivedCategory.Plus.ι) ≅
        (CochainComplex.Plus.ι (ModuleCat.{u} R) ⋙
          AugmentedCechComplex.tensorFunctor R rs) ⋙ DerivedCategory.Q) ∧
      Nonempty ((IdealTorsion.idealTorsionFunctor I).rightDerivedFunctorPlus ≅ T)

/-- Local cohomology and cohomology of the Čech complex with module coefficients
are naturally isomorphic as module-valued functors in every integer degree. -/
def ModuleComparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (rs : List R), Ideal.span {r | r ∈ rs} = I →
    ∀ q : ℤ, Nonempty (IdealTorsion.localCohomology.{u} I q ≅
      (single (ModuleCat.{u} R) (.up ℤ) 0 ⋙ AugmentedCechComplex.tensorFunctor R rs) ⋙
        homologyFunctor (ModuleCat.{u} R) (.up ℤ) q)

end Specs.CommutativeAlgebraNotes.DerivedCechComparison
