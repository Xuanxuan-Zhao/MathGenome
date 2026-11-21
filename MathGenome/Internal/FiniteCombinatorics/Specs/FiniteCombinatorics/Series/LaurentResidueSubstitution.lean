import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.Substitution

/-! Laurent series in p204:W18. `LaurentSeries R` is the ring of integer-indexed
series with support bounded below. The inner series is parametrized by a unit
of `R[[X]]`, so no domain or nontriviality assumption is made on `R`. -/
noncomputable section
universe u
namespace Specs.FiniteCombinatorics.Series.LaurentResidueSubstitution
open scoped BigOperators

/-- The residue is the coefficient of exponent -1. -/
def residueValue {R : Type u} [CommRing R] (L : LaurentSeries R) : R := L.coeff (-1)
def residueType : Type (u+1) := ∀ {R : Type u} [CommRing R], LaurentSeries R → R

/-- Integer powers of `X U`: the unit part has all integer powers in `R[[X]]`. -/
def powerValue {R : Type u} [CommRing R] (U : (PowerSeries R)ˣ) (k : ℤ) :
    LaurentSeries R := HahnSeries.single k 1 * ((↑(U ^ k) : PowerSeries R) : LaurentSeries R)
def powerType : Type (u+1) := ∀ {R : Type u} [CommRing R],
  (PowerSeries R)ˣ → ℤ → LaurentSeries R

/-- A coefficientwise formal substitution. Its bounded support and finite
coefficient expansion are separate obligations, rather than assumptions. -/
def composeValue {R : Type u} [CommRing R] (L : LaurentSeries R)
    (U : (PowerSeries R)ˣ) : LaurentSeries R :=
  HahnSeries.ofSuppBddBelow
    (fun n => ∑ k ∈ Finset.Icc L.order n, L.coeff k * (powerValue U k).coeff n) (by
      refine ⟨L.order, ?_⟩
      intro n hn
      by_contra h
      have hlt : n < L.order := lt_of_not_ge h
      have he : Finset.Icc L.order n = ∅ := Finset.Icc_eq_empty_of_lt hlt
      exact hn (by simp [he]))
def composeType : Type (u+1) := ∀ {R : Type u} [CommRing R],
  LaurentSeries R → (PowerSeries R)ˣ → LaurentSeries R

def ResidueDerivative : Prop := ∀ {R : Type u} [CommRing R] (L : LaurentSeries R),
  residueValue (LaurentSeries.derivative R L) = 0

def PowerAddition : Prop := ∀ {R : Type u} [CommRing R] (U : (PowerSeries R)ˣ) (k l : ℤ),
  powerValue U (k+l) = powerValue U k * powerValue U l

def PowerZero : Prop := ∀ {R : Type u} [CommRing R] (U : (PowerSeries R)ˣ),
  powerValue U 0 = 1

def PowerOne : Prop := ∀ {R : Type u} [CommRing R] (U : (PowerSeries R)ˣ),
  powerValue U 1 = ((PowerSeries.X * (U : PowerSeries R) : PowerSeries R) : LaurentSeries R)

def PowerLowerBound : Prop := ∀ {R : Type u} [CommRing R] (U : (PowerSeries R)ˣ)
  (k n : ℤ), n < k → (powerValue U k).coeff n = 0

def CompositionCoefficients : Prop := ∀ {R : Type u} [CommRing R] (L : LaurentSeries R)
  (U : (PowerSeries R)ˣ) (n : ℤ),
  (composeValue L U).coeff n =
    ∑ k ∈ Finset.Icc L.order n, L.coeff k * (powerValue U k).coeff n

def CompositionMonomial : Prop := ∀ {R : Type u} [CommRing R] (U : (PowerSeries R)ˣ)
  (k : ℤ) (r : R), composeValue (HahnSeries.single k r) U = r • powerValue U k

def CompositionPowerSeries : Prop := ∀ {R : Type u} [CommRing R] (A : PowerSeries R)
  (U : (PowerSeries R)ˣ),
  composeValue (A : LaurentSeries R) U =
    ((Specs.FiniteCombinatorics.Series.Substitution.composeValue A
      (PowerSeries.X * (U : PowerSeries R))) : LaurentSeries R)

def PowerDerivative : Prop := ∀ {R : Type u} [CommRing R] (U : (PowerSeries R)ˣ) (k : ℤ),
  LaurentSeries.derivative R (powerValue U k) =
    k • (powerValue U (k-1) *
      ((PowerSeries.derivative (PowerSeries.X * (U : PowerSeries R))) : LaurentSeries R))

def ResidueSubstitution : Prop := ∀ {R : Type u} [CommRing R] [Algebra ℚ R]
  (L : LaurentSeries R) (U : (PowerSeries R)ˣ),
  residueValue (composeValue L U *
    ((PowerSeries.derivative (PowerSeries.X * (U : PowerSeries R))) : LaurentSeries R)) =
  residueValue L

/-- Every unit constant term gives an admissible unit part; this connects the
unit parameterization to the source hypothesis `U(0)` is a unit. -/
def UnitParameterization : Prop := ∀ {R : Type u} [CommRing R] (U : PowerSeries R),
  IsUnit (PowerSeries.constantCoeff U) ↔ ∃ v : (PowerSeries R)ˣ, (v : PowerSeries R) = U
/-- The coefficient formula fixes the formal derivative on the complete Laurent ring. -/
def DerivativeCoefficients : Prop := ∀ {R : Type u} [CommRing R] (L : LaurentSeries R) (n : ℤ),
  (LaurentSeries.derivative R L).coeff n = (n+1) • L.coeff (n+1)

def PowerInverse : Prop := ∀ {R : Type u} [CommRing R] (U : (PowerSeries R)ˣ) (k : ℤ),
  powerValue U k * powerValue U (-k) = 1 ∧ powerValue U (-k) * powerValue U k = 1

def CompositionShift : Prop := ∀ {R : Type u} [CommRing R] (L : LaurentSeries R)
  (U : (PowerSeries R)ˣ) (j : ℤ),
  composeValue (HahnSeries.single j 1 * L) U = powerValue U j * composeValue L U

def CompositionMul : Prop := ∀ {R : Type u} [CommRing R] (L M : LaurentSeries R)
  (U : (PowerSeries R)ˣ), composeValue (L*M) U = composeValue L U * composeValue M U

/-- Any common lower bound may be used in the finite coefficient sum. -/
def CompositionLowerBoundCoefficients : Prop := ∀ {R : Type u} [CommRing R] (L : LaurentSeries R)
  (U : (PowerSeries R)ˣ) (b : ℤ), (∀ k : ℤ, k < b → L.coeff k = 0) → ∀ n : ℤ,
  (composeValue L U).coeff n = ∑ k ∈ Finset.Icc b n, L.coeff k * (powerValue U k).coeff n

def CompositionFiniteDependence : Prop := ∀ {R : Type u} [CommRing R] (L M : LaurentSeries R)
  (U : (PowerSeries R)ˣ) (b n : ℤ),
  (∀ k : ℤ, k < b → L.coeff k = 0) →
  (∀ k : ℤ, k < b → M.coeff k = 0) →
  (∀ k : ℤ, b ≤ k → k ≤ n → L.coeff k = M.coeff k) →
  (composeValue L U).coeff n = (composeValue M U).coeff n

/-- The residue identity with exactly the source's hypothesis on an ordinary
series U. The canonical unit choice introduces no extra mathematical hypothesis. -/
def ResidueSubstitutionUnitConstant : Prop := ∀ {R : Type u} [CommRing R] [Algebra ℚ R]
  (L : LaurentSeries R) (U : PowerSeries R) (hU : IsUnit (PowerSeries.constantCoeff U)),
  residueValue (composeValue L (PowerSeries.isUnit_iff_constantCoeff.mpr hU).unit *
    ((PowerSeries.derivative (PowerSeries.X * U)) : LaurentSeries R)) = residueValue L

end Specs.FiniteCombinatorics.Series.LaurentResidueSubstitution
