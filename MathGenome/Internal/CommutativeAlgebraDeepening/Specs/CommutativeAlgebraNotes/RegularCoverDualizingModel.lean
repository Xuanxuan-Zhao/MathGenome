import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalQuotientAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex HomComplex
open IsLocalRing (ResidueField maximalIdeal)

namespace Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel

universe u w

abbrev Complex (R : Type u) [CommRing R] := CochainComplex (ModuleCat.{u} R) ℤ

abbrev stalk (R : Type u) [CommRing R] (i : ℤ) (M : ModuleCat.{u} R) : Complex R :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) i).obj M

/-- A bounded, termwise injective model of a complex, with its resolution map. -/
structure BoundedInjectiveResolution {S : Type u} [CommRing S] (K : Complex S) where
  complex : Complex S
  ι : K ⟶ complex
  quasiIso : QuasiIso ι
  injective : ∀ i, Injective (complex.X i)
  lower : ℤ
  upper : ℤ
  isStrictlyGE : complex.IsStrictlyGE lower
  isStrictlyLE : complex.IsStrictlyLE upper

abbrev shiftedRing (S : Type u) [CommRing S] (n : ℕ) : Complex S :=
  (stalk S 0 (ModuleCat.of S S))⟦(n : ℤ)⟧

abbrev ShiftedRingResolution (S : Type u) [CommRing S] (n : ℕ) :=
  BoundedInjectiveResolution (shiftedRing S n)

/-- Apply `Hom_S(R,-)` with its argument action and its induced differentials. -/
abbrev dualizingComplex {S R : Type u} [CommRing S] [CommRing R]
    (f : S →+* R) (J : Complex S) : Complex R :=
  LocalQuotientAdjunction.CoinducedComplex f J

def DualizingComplexType :=
  ∀ {S R : Type u} [CommRing S] [CommRing R], (S →+* R) → Complex S → Complex R

/-- The object represented by coinduction on the bounded injective resolution. -/
def dualizingObject {S R : Type u} [CommRing S] [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (f : S →+* R) {n : ℕ}
    (J : ShiftedRingResolution S n) : DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Q.obj (dualizingComplex f J.complex)

set_option linter.checkUnivs false in
def DualizingObjectType :=
  ∀ {S R : Type u} [CommRing S] [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (_f : S →+* R) {n : ℕ},
    ShiftedRingResolution S n → DerivedCategory (ModuleCat.{u} R)

/-- Existence with terms in the shifted injective-dimension interval. -/
def ShiftedRingResolutionExists : Prop :=
  ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S] (n : ℕ),
    ringKrullDim S = (n : WithBot ℕ∞) →
    ∃ J : ShiftedRingResolution S n, J.lower = -(n : ℤ) ∧ J.upper = 0

def CoinducedBoundedInjective : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] (f : S →+* R)
    {K : Complex S} (J : BoundedInjectiveResolution K),
    (∀ i, Injective ((dualizingComplex f J.complex).X i)) ∧
    (dualizingComplex f J.complex).IsStrictlyGE J.lower ∧
    (dualizingComplex f J.complex).IsStrictlyLE J.upper ∧
    (dualizingComplex f J.complex).IsKInjective

/-- Comparison of two resolutions, including compatibility with the augmentations
in the homotopy category. -/
def ResolutionIndependence : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] (f : S →+* R)
    {K : Complex S} (J J' : BoundedInjectiveResolution K),
    letI := (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
    let F := (ModuleCat.coextendScalars f).mapHomologicalComplex (.up ℤ)
    ∃ e : HomotopyEquiv J.complex J'.complex,
      Nonempty (Homotopy (J.ι ≫ e.hom) J'.ι) ∧
      ∃ e' : HomotopyEquiv (dualizingComplex f J.complex) (dualizingComplex f J'.complex),
        e'.hom = F.map e.hom ∧ e'.inv = F.map e.inv

/-- The map induced by precomposition with a quasi-isomorphism of arbitrary
source complexes is a quasi-isomorphism for a K-injective target. -/
def DerivedHomPrecomposition : Prop :=
  ∀ {R : Type u} [CommRing R] {U V I : Complex R} (α : U ⟶ V),
    QuasiIso α → I.IsKInjective →
    ∃ g : linearHomComplex R V I ⟶ linearHomComplex R U I,
      QuasiIso g ∧
      ∀ (a : ℤ) (z : Cochain V I a) (p q : ℤ) (h : p + a = q),
        (show Cochain U I a from g.f a z).v p q h = α.f p ≫ z.v p q h

/-- For every source complex the two Hom models are related by the actual
coinduction adjunction. Applying `Q` to this chain isomorphism gives the
derived Hom isomorphism with the precomposition action of `R`. -/
def DerivedAdjunction : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] (f : S →+* R)
    {K : Complex S} (J : BoundedInjectiveResolution K) (U : Complex R),
    ∃ e : linearHomComplex R U (dualizingComplex f J.complex) ≅
          LocalQuotientAdjunction.restrictedHomComplex f U J.complex,
      ∀ (a : ℤ) (z : Cochain U (dualizingComplex f J.complex) a)
        (p q : ℤ) (h : p + a = q),
        (show Cochain (LocalQuotientAdjunction.RestrictedComplex f U) J.complex a
          from e.hom.f a z).v p q h =
            LocalQuotientAdjunction.adjunction f (U.X p) (J.complex.X q) (z.v p q h)

def FiniteCohomology : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsRegularLocalRing S]
    [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal S) S]
    [IsAdicComplete (maximalIdeal R) R] (f : S →+* R) [IsLocalHom f],
    Function.Surjective f → ∀ {n : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) →
    ∀ (J : ShiftedRingResolution S n) (q : ℤ),
      Module.Finite R ((dualizingComplex f J.complex).homology q)

def Normalization : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsRegularLocalRing S]
    [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal S) S]
    [IsAdicComplete (maximalIdeal R) R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (f : S →+* R) [IsLocalHom f], Function.Surjective f →
    ∀ {n : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) → ∀ (J : ShiftedRingResolution S n),
    Nonempty (DerivedCategory.Q.obj
      (linearHomComplex R (stalk R 0 (ModuleCat.of R (ResidueField R)))
        (dualizingComplex f J.complex)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (ResidueField R)))

end Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel
