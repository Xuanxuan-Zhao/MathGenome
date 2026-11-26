import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DerivedCechComparison

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Specs.CommutativeAlgebraNotes.CechGeneratorIndependence

universe u v w

open IdealTorsion

/-- Cohomology of the augmented Čech complex with module coefficients. -/
noncomputable abbrev cechCohomology {R : Type u} [CommRing R] (rs : List R) (q : ℤ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (single (ModuleCat.{u} R) (.up ℤ) 0 ⋙ AugmentedCechComplex.tensorFunctor R rs) ⋙
    homologyFunctor (ModuleCat.{u} R) (.up ℤ) q

/-- The comparison that identifies a derived functor with Čech tensor on complexes. -/
noncomputable abbrev cechDescentIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (rs : List R)
    (T : DerivedCategory.Plus (ModuleCat.{u} R) ⥤ DerivedCategory.Plus (ModuleCat.{u} R)) :=
  ((DerivedCategory.Plus.Q ⋙ T) ⋙ DerivedCategory.Plus.ι) ≅
    (CochainComplex.Plus.ι (ModuleCat.{u} R) ⋙
      AugmentedCechComplex.tensorFunctor R rs) ⋙ DerivedCategory.Q

/-- Derived ideal torsion on bounded-below complexes depends only on the radical. -/
def DerivedRadicalInvariance : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] {I J : Ideal R},
    I.radical = J.radical →
    Nonempty ((idealTorsionFunctor I).rightDerivedFunctorPlus ≅
      (idealTorsionFunctor J).rightDerivedFunctorPlus)

/-- Lists that generate the same radical compute the same derived functor,
with natural comparisons to Čech tensor for each list. -/
def DerivedCechIndependence : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : Ideal R) (rs ts : List R),
    I.radical = (Ideal.span {r | r ∈ rs}).radical →
    I.radical = (Ideal.span {r | r ∈ ts}).radical →
    ∃ T : DerivedCategory.Plus (ModuleCat.{u} R) ⥤ DerivedCategory.Plus (ModuleCat.{u} R),
      Nonempty ((idealTorsionFunctor I).rightDerivedFunctorPlus ≅ T) ∧
      Nonempty (cechDescentIso rs T) ∧ Nonempty (cechDescentIso ts T)

/-- Local cohomology in each integer degree is naturally invariant under equality of radicals. -/
def RadicalInvariance : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R] {I J : Ideal R},
    I.radical = J.radical → ∀ q : ℤ,
    Nonempty (localCohomology.{v} I q ≅ localCohomology.{v} J q)

/-- A list generating an ideal with the same radical as `I` computes local cohomology at `I`. -/
def CechComparisonOfRadicalEq : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (rs : List R),
    I.radical = (Ideal.span {r | r ∈ rs}).radical → ∀ q : ℤ,
    Nonempty (localCohomology.{u} I q ≅ cechCohomology rs q)

/-- The Čech cohomology functors from two lists generating the same radical
are naturally isomorphic. -/
def CechIndependence : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (rs ts : List R),
    (Ideal.span {r | r ∈ rs}).radical = (Ideal.span {r | r ∈ ts}).radical →
    ∀ q : ℤ, Nonempty (cechCohomology rs q ≅ cechCohomology ts q)

/-- Local cohomology vanishes above the length of a list generating the same radical. -/
def VanishingAboveLength : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (rs : List R),
    I.radical = (Ideal.span {r | r ∈ rs}).radical →
    ∀ q : ℤ, (rs.length : ℤ) < q → IsZero (localCohomology.{u} I q)

/-- Degree-zero local cohomology at the zero ideal is naturally the identity. -/
def BotDegreeZero : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R],
    Nonempty (localCohomology.{v} (⊥ : Ideal R) 0 ≅ 𝟭 (ModuleCat.{v} R))

/-- Local cohomology at the zero ideal vanishes away from degree zero. -/
def BotVanishing : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R],
    ∀ q : ℤ, q ≠ 0 → IsZero (localCohomology.{u} (⊥ : Ideal R) q)

/-- Local cohomology at the unit ideal vanishes in all degrees. -/
def TopVanishing : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R],
    ∀ q : ℤ, IsZero (localCohomology.{v} (⊤ : Ideal R) q)

end Specs.CommutativeAlgebraNotes.CechGeneratorIndependence
