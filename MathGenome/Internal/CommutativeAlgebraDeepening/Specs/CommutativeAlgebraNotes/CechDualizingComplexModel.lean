import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExactDualCochainCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalRing (maximalIdeal)
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs (residueFieldEnvelopeValue)
open _root_.CommutativeAlgebraNotes.ExactDualCochainCohomologySpecs (dualComplexValue)

namespace Specs.CommutativeAlgebraNotes.CechDualizingComplexModel

open RegularCoverDualizingModel (Complex ShiftedRingResolution dualizingComplex dualizingObject)

universe u w

/-- The augmented Čech complex dualized into the chosen residue hull in degree zero. -/
abbrev cechDual {R : Type u} [CommRing R] [IsLocalRing R]
    (E : residueFieldEnvelopeValue R) (rs : List R) : Complex R :=
  (dualComplexValue E).obj (op (AugmentedCechComplex.complex R rs))

abbrev CechDualType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R],
    residueFieldEnvelopeValue R → List R → Complex R

/-- The Čech dual is a bounded injective target for derived Hom. -/
def BoundedInjectiveCechDual : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    (E : residueFieldEnvelopeValue R) (rs : List R),
    (∀ i : ℤ, Injective ((cechDual E rs).X i)) ∧
    (cechDual E rs).IsStrictlyGE (-(rs.length : ℤ)) ∧
    (cechDual E rs).IsStrictlyLE (0 : ℤ) ∧
    (cechDual E rs).IsKInjective

/-- Over the complete regular cover the Čech dual itself can resolve the
translated ring. The resolution includes its quasi-isomorphism from the ring. -/
def CechDualResolution : Prop :=
  ∀ {S : Type u} [CommRing S] [IsRegularLocalRing S]
    [IsAdicComplete (maximalIdeal S) S] {n : ℕ},
    ringKrullDim S = (n : WithBot ℕ∞) →
    ∀ (E : residueFieldEnvelopeValue S) (ss : List S),
      Ideal.span {s | s ∈ ss} = maximalIdeal S →
      ∃ J : ShiftedRingResolution S n, J.complex = cechDual E ss

/-- For descended generators the comparison is an isomorphism of complexes
over the quotient, with the precomposition action on the coinduced side. -/
def DescendedCechDualComparison : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R]
    [IsNoetherianRing S] [IsNoetherianRing R] (f : S →+* R) [IsLocalHom f],
    Function.Surjective f →
    ∀ (E : residueFieldEnvelopeValue S) (F : residueFieldEnvelopeValue R) (ss : List S),
      Ideal.span {s | s ∈ ss} = maximalIdeal S →
      Nonempty (dualizingComplex f (cechDual E ss) ≅ cechDual F (ss.map f))

/-- Dualizing the Čech complex of either generating list gives the same
object up to isomorphism in the derived category. -/
def CechDualGeneratorIndependence : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (E : residueFieldEnvelopeValue R) (rs ts : List R),
    Ideal.span {r | r ∈ rs} = maximalIdeal R →
    Ideal.span {r | r ∈ ts} = maximalIdeal R →
    Nonempty (DerivedCategory.Q.obj (cechDual E rs) ≅
      DerivedCategory.Q.obj (cechDual E ts))

/-- For any chosen maximal-ideal generators and hull, the Čech dual
represents the regular-cover dualizing object. -/
def CechDualRepresentsDualizingObject : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsRegularLocalRing S]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal S) S] [IsAdicComplete (maximalIdeal R) R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (f : S →+* R) [IsLocalHom f], Function.Surjective f →
    ∀ {n : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) →
    ∀ (J : ShiftedRingResolution S n) (F : residueFieldEnvelopeValue R) (rs : List R),
      Ideal.span {r | r ∈ rs} = maximalIdeal R →
      Nonempty (DerivedCategory.Q.obj (cechDual F rs) ≅ dualizingObject f J)

/-- The regular-cover dualizing objects from two specified covers are
isomorphic in the derived category of the target ring. -/
def RegularCoverIndependence : Prop :=
  ∀ {S T R : Type u} [CommRing S] [CommRing T] [CommRing R]
    [IsRegularLocalRing S] [IsRegularLocalRing T] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal S) S] [IsAdicComplete (maximalIdeal T) T]
    [IsAdicComplete (maximalIdeal R) R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (f : S →+* R) (g : T →+* R) [IsLocalHom f] [IsLocalHom g],
    Function.Surjective f → Function.Surjective g →
    ∀ {n m : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) →
    ringKrullDim T = (m : WithBot ℕ∞) →
    ∀ (J : ShiftedRingResolution S n) (K : ShiftedRingResolution T m),
      Nonempty (dualizingObject f J ≅ dualizingObject g K)

end Specs.CommutativeAlgebraNotes.CechDualizingComplexModel
