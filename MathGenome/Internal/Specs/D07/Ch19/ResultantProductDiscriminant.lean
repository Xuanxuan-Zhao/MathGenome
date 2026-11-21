import MathGenome.Internal.Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant
import Mathlib.Data.ZMod.Basic

/-!
Independent specifications for paper.tex:5419–5490.
The canonical determinant, root multiset, root discriminant, and universal
integer polynomial are those in the prerequisite Specs. The propositions below
retain their complete quantifiers; no theorem is postulated here. In particular,
all root statements allow repeated roots in a single specified splitting extension,
and the derivative bound is n-1, independently of the characteristic.
-/
universe u v
noncomputable section
namespace Specs.D07.Ch19.ResultantProductDiscriminant
open Polynomial
open Specs.D07.Ch19.ResultantDefinition
open Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant

def PaddedRootProduct : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.PaddedRootProduct.{u,v}

def RootMultiplicityCount : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.RootMultiplicityCount.{u,v}

def IndexedRootProduct : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.IndexedRootProduct.{u,v}

def MonicRootProduct : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.MonicRootProduct.{u,v}

def FixedResultantScaling : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.FixedResultantScaling.{u}

def MonicNormalization : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.MonicNormalization.{u}

def RootProductEqualsDiscriminant : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.RootProductEqualsDiscriminant.{u,v}

def PermutationInvariance : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.PermutationInvariance.{u}

def NumberingIndependence : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.NumberingIndependence.{u,v}

def VanishingIffRepeatedEntries : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.VanishingIffRepeatedEntries.{u}

def VanishingIffRepeatedRoot : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.VanishingIffRepeatedRoot.{u,v}

def DiscriminantResultantIdentity : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.DiscriminantResultantIdentity.{u,v}

def UniversalSpecialization : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.UniversalSpecialization.{u}

def UniversalRootSpecialization : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.UniversalRootSpecialization.{u,v}

def UniversalResultantDivision : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.UniversalResultantDivision

def DegreeOne : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.DegreeOne.{u}

def ZeroDerivative : Prop :=
  Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.ZeroDerivative.{u}

/-- Differentiation at a chosen indexed root, also for repeated entries. -/
def DerivativeAtRoot : Prop :=
  ∀ (L : Type u) [Field L] (f : L[X]) (n : ℕ) (α : Fin n → L),
    f.Splits → (List.ofFn α : Multiset L) = f.roots →
    ∀ i : Fin n, f.derivative.eval (α i) =
      f.leadingCoeff * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), (α i - α j)

/-- Pairing the two orientations of every pair supplies precisely this sign. -/
def DerivativeProduct : Prop :=
  ∀ (L : Type u) [Field L] (f : L[X]) (n : ℕ) (α : Fin n → L),
    f.Splits → (List.ofFn α : Multiset L) = f.roots →
    (∏ i, f.derivative.eval (α i)) =
      (-1 : L) ^ (n * (n-1) / 2) * f.leadingCoeff ^ n * rootDifferenceProduct α

/-- The fixed determinant identity over the coefficient ring itself. -/
def CoefficientResultantIdentity : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R[X]) (n : ℕ),
    f.natDegree = n → 1 ≤ n →
    fixedResultant f f.derivative n (n-1) =
      (-1 : R) ^ (n * (n-1) / 2) * f.leadingCoeff * f.discr

/-- Exact correction when the derivative's actual degree is used instead. -/
def DerivativePaddingAdjustment : Prop :=
  ∀ (F : Type u) [Field F] (f : F[X]) (n : ℕ),
    f ≠ 0 → f.natDegree = n → 1 ≤ n →
    fixedResultant f f.derivative n (n-1) =
      f.leadingCoeff ^ (n-1-f.derivative.natDegree) * ordinaryResultant f f.derivative

/-- For monic polynomials this correction is one, in every characteristic. -/
def MonicDerivativePadding : Prop :=
  ∀ (F : Type u) [Field F] (f : F[X]) (n : ℕ),
    f.Monic → f.natDegree = n → 1 ≤ n →
    fixedResultant f f.derivative n (n-1) = ordinaryResultant f f.derivative

/-- Monic discriminants are integer polynomials in the n nonleading coefficients.
The same polynomial works over every ring; no inversion or division by n! occurs. -/
def MonicCoefficientPolynomial : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ D : MvPolynomial (Fin n) ℤ,
    ∀ (R : Type u) [CommRing R] (f : R[X]),
      f.Monic → f.natDegree = n →
      MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i : Fin n => f.coeff i) D = f.discr

/-- The division is in the universal integer polynomial ring before specialization. -/
def UniversalDivisibility : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    MvPolynomial.X (Fin.last n) ∣
      fixedResultant (universalPolynomial n) (universalPolynomial n).derivative n (n-1)

/-- Setting the leading variable to zero annihilates the fixed determinant. -/
def UniversalLeadingZero : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (R : Type u) [CommRing R] (c : Fin (n+1) → R),
    c (Fin.last n) = 0 →
    MvPolynomial.eval₂Hom (Int.castRingHom R) c
      (fixedResultant (universalPolynomial n) (universalPolynomial n).derivative n (n-1)) = 0

/-- An explicit positive-characteristic degree drop invalidates the unadjusted formula. -/
def DegreeDropCounterexample : Prop :=
  let f : (ZMod 3)[X] := C 2 * X^3 + X^2 + 1
  f.natDegree = 3 ∧ f.derivative.natDegree = 1 ∧
    fixedResultant f f.derivative 3 2 = 2 ∧ ordinaryResultant f f.derivative = 1 ∧
    f.discr ≠ (-1 : ZMod 3) ^ (3 * (3-1) / 2) * f.leadingCoeff⁻¹ *
      ordinaryResultant f f.derivative

end Specs.D07.Ch19.ResultantProductDiscriminant
