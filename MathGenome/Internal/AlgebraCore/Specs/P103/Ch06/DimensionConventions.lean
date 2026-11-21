import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.AssociatedPrimesInterface
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Support

/-!
Independent interface for paper.tex:1037 and the global conventions at lines 42–50.
Dimensions take values in `WithBot ℕ∞`: bottom is −∞ and top is +∞.
`LTSeries.length` counts strict inclusions, so a one-prime chain has length zero.
Primes are proper by their `PrimeSpectrum` type. No Noetherian assumption is made.
The quotient definition of module dimension also makes sense for arbitrary modules;
the identification with support below is asserted for finite modules.
-/
namespace P103.Specs.Ch06.DimensionConventions

universe u v
open P103.Specs.Ch05.AssociatedPrimesInterface

def RingDimensionType := ∀ (R : Type u) [CommRing R], WithBot ℕ∞

noncomputable def ringDimensionValue : RingDimensionType.{u} :=
  fun R _ => ringKrullDim R

def PrimeHeightType := ∀ (R : Type u) [CommRing R], PrimeSpectrum R → ℕ∞

noncomputable def primeHeightValue : PrimeHeightType.{u} :=
  fun _ _ p => p.asIdeal.height

def ModuleDimensionType :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], WithBot ℕ∞

noncomputable def moduleDimensionValue : ModuleDimensionType.{u,v} :=
  fun R _ M _ _ => ringDimensionValue (R ⧸ Module.annihilator R M)

noncomputable def supportDimensionValue : ModuleDimensionType.{u,v} :=
  fun R _ M _ _ => Order.krullDim (supportValue R M)

def ringDimension_chainsType : Prop :=
  ∀ (R : Type u) [CommRing R],
    ringDimensionValue R = ⨆ (c : LTSeries (PrimeSpectrum R)), (c.length : WithBot ℕ∞)

def ringDimension_emptyType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsEmpty (PrimeSpectrum R)], ringDimensionValue R = ⊥

def ringDimension_zeroRingType : Prop :=
  ∀ (R : Type u) [CommRing R] [Subsingleton R], ringDimensionValue R = ⊥

/-- Height is the supremum of lengths of prime chains ending at the given prime. -/
def primeHeight_chainsType : Prop :=
  ∀ (R : Type u) [CommRing R] (p : PrimeSpectrum R),
    primeHeightValue R p = ⨆ (c : LTSeries (PrimeSpectrum R)) (_ : c.last = p),
      (c.length : ℕ∞)

def primeHeight_localizationType : Prop :=
  ∀ (R : Type u) [CommRing R] (p : PrimeSpectrum R),
    (primeHeightValue R p : WithBot ℕ∞) =
      ringDimensionValue (Localization.AtPrime p.asIdeal)

/-- The source's localization-defined support, over any commutative ring. -/
def finite_support_eq_zeroLocusType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M],
    supportValue R M = PrimeSpectrum.zeroLocus (Module.annihilator R M : Set R)

def moduleDimension_eq_supportDimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M], moduleDimensionValue R M = supportDimensionValue R M

/-- Every zero module has dimension −∞, even without specifying finiteness. -/
def moduleDimension_zeroType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Subsingleton M], moduleDimensionValue R M = ⊥

end P103.Specs.Ch06.DimensionConventions
