import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DualizingComplexHomothety

open CategoryTheory
open CochainComplex
open IsLocalRing (ResidueField maximalIdeal)
open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel
open Specs.CommutativeAlgebraNotes.DualizingComplexHomothety

namespace Specs.CommutativeAlgebraNotes.NormalizedDualizingComplex

universe u w

/-- The dualizing object is represented by coinduction on a bounded injective
resolution of (S[n]). Every such resolution gives the stated properties. -/
def NormalizedDualizingComplexType : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsRegularLocalRing S]
    [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal S) S]
    [IsAdicComplete (maximalIdeal R) R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (f : S →+* R) [IsLocalHom f], Function.Surjective f →
    ∀ {n : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) →
    Nonempty (ShiftedRingResolution S n) ∧
      ∀ (J : ShiftedRingResolution S n),
        let D := dualizingComplex f J.complex
        ((∀ i, Injective (D.X i)) ∧ D.IsStrictlyGE J.lower ∧
          D.IsStrictlyLE J.upper ∧ D.IsKInjective) ∧
        (∀ q, Module.Finite R (D.homology q)) ∧
        IsIso (derivedHomothety f J) ∧
        Nonempty (DerivedCategory.Q.obj
          (linearHomComplex R (stalk R 0 (ModuleCat.of R (ResidueField R))) D) ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R (ResidueField R)))

end Specs.CommutativeAlgebraNotes.NormalizedDualizingComplex
