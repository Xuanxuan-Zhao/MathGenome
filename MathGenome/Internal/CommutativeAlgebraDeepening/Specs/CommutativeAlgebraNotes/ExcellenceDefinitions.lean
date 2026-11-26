import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.PrimeChains
import MathGenome.Internal.AlgebraCore.P103.Ch07.CompletedNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Flat

/-! Shared definitions from Definition 5.1. Finite extensions and finite-type
algebras admit representatives in the universe of their base ring. -/

universe u v w
open scoped TensorProduct

namespace CommutativeAlgebraNotes.Excellence.Specs

def RegularRingType := ∀ (R : Type u) [CommRing R], Prop

/-- Regularity at every prime, for an arbitrary commutative ring. -/
def RegularRingValue : RegularRingType.{u} := fun R _ =>
  ∀ (p : Ideal R) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p)

set_option linter.checkUnivs false in
def GeometricallyRegularType :=
  ∀ (k : Type u) (T : Type v) [Field k] [CommRing T] [Algebra k T], Prop

/-- Every finite field extension, including the identity extension, gives a
Noetherian regular scalar extension. -/
def GeometricallyRegularValue : GeometricallyRegularType.{u,v} := fun k T _ _ _ =>
  ∀ (L : Type u) [Field L] [Algebra k L] [Module.Finite k L],
    IsNoetherianRing (L ⊗[k] T) ∧ RegularRingValue (L ⊗[k] T)

set_option linter.checkUnivs false in
def RegularMapType :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B], (A →+* B) → Prop

/-- The algebra structure on the target is the one given by the map. -/
def RegularMapValue : RegularMapType.{u,v} := fun A B _ _ _ _ f =>
  f.Flat ∧
    (letI : Algebra A B := f.toAlgebra
     ∀ (p : Ideal A) [p.IsPrime], GeometricallyRegularValue p.ResidueField (p.Fiber B))

def FormalFiberType :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (p : Ideal A) [p.IsPrime], Type u

/-- The fibre of the maximal-ideal adic completion at the prime `p`. -/
abbrev FormalFiberValue : FormalFiberType.{u} := fun A _ _ _ p _ =>
  p.Fiber (AdicCompletion (IsLocalRing.maximalIdeal A) A)

def IsGRingType := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R], Prop

def IsGRingValue : IsGRingType.{u} := fun R _ _ =>
  ∀ (p : Ideal R) [p.IsPrime],
    let A := Localization.AtPrime p
    let B := AdicCompletion (IsLocalRing.maximalIdeal A) A
    letI : IsNoetherianRing B :=
      P103.Ch07.CompletedNoetherian.completed_noetherian A (IsLocalRing.maximalIdeal A)
    RegularMapValue A B (algebraMap A B)

def regularLocusType := ∀ (R : Type u) [CommRing R], Set (PrimeSpectrum R)

def regularLocusValue : regularLocusType.{u} := fun R _ =>
  {p : PrimeSpectrum R | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

def J2Type := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R], Prop

def J2Value : J2Type.{u} := fun R _ _ =>
  ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.FiniteType R B],
    IsOpen (regularLocusValue B)

def CatenaryType := ∀ (R : Type u) [CommRing R], Prop

/-- Saturation uses covering relations in the whole prime spectrum. Length
counts inclusions, so singleton chains have length zero. -/
def CatenaryValue : CatenaryType.{u} := fun R _ =>
  ∀ (p q : PrimeSpectrum R), p ≤ q →
    ∀ c d : AdvCommAlg.CohenMacaulay.Specs.PrimeChain R,
      c.head = p → c.last = q → d.head = p → d.last = q → c.length = d.length

def UniversallyCatenaryType := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R], Prop

def UniversallyCatenaryValue : UniversallyCatenaryType.{u} := fun R _ _ =>
  ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], CatenaryValue B

def QuasiExcellentType := ∀ (R : Type u) [CommRing R], Prop

def QuasiExcellentValue : QuasiExcellentType.{u} := fun R _ =>
  ∃ h : IsNoetherianRing R, @IsGRingValue R _ h ∧ @J2Value R _ h

def ExcellentType := ∀ (R : Type u) [CommRing R], Prop

def ExcellentValue : ExcellentType.{u} := fun R _ =>
  ∃ h : IsNoetherianRing R, @IsGRingValue R _ h ∧
    @J2Value R _ h ∧ @UniversallyCatenaryValue R _ h

def regularRing_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R], RegularRingValue R ↔ IsRegularRing R

def regularMap_algebraMap_iffType : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B],
    RegularMapValue A B (algebraMap A B) ↔ Module.Flat A B ∧
      ∀ (p : Ideal A) [p.IsPrime], GeometricallyRegularValue p.ResidueField (p.Fiber B)

def catenary_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    CatenaryValue R ↔ AdvCommAlg.CohenMacaulay.Specs.CatenaryValue R

def universallyCatenary_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    UniversallyCatenaryValue R ↔
      ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.FiniteType R B],
        AdvCommAlg.CohenMacaulay.Specs.CatenaryValue B

def geometricallyRegular_regular_tensorProductType : Prop :=
  ∀ {k : Type u} {T : Type v} [Field k] [CommRing T] [Algebra k T],
    GeometricallyRegularValue k T →
      ∀ (L : Type w) [Field L] [Algebra k L] [Module.Finite k L],
        IsNoetherianRing (L ⊗[k] T) ∧ RegularRingValue (L ⊗[k] T)

def j2_isOpen_regularLocusType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R], J2Value R →
    ∀ (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B],
      IsOpen (regularLocusValue B)

def universallyCatenary_catenaryType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R], UniversallyCatenaryValue R →
    ∀ (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], CatenaryValue B

end CommutativeAlgebraNotes.Excellence.Specs
