import MathGenome.Internal.Specs.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
K07.19.resultant_product_discriminant, paper.tex:5454–5490.
The discriminant is the indicated product over an indexed list of all roots,
with repetitions. The two resultant bounds remain n and n-1 in all characteristics.
The universal coefficient polynomial has n+1 integer coefficient variables,
indexed in ascending coefficient order. Its construction uses the modified
Sylvester determinant, so no inverse or field of fractions occurs in it.
-/
universe u v
noncomputable section
namespace Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant
open Polynomial
open Specs.D07.Ch19.ResultantDefinition

/-- The square of the product of pairwise root differences. -/
def rootDifferenceProduct {R : Type u} [CommRing R] {n : ℕ} (α : Fin n → R) : R :=
  ∏ i, ∏ j ∈ Finset.Ioi i, (α i - α j) ^ 2

/-- The paper's root definition, including its exact leading coefficient power. -/
def rootDiscriminant {R : Type u} [CommRing R] {n : ℕ} (a : R) (α : Fin n → R) : R :=
  a ^ (2 * n - 2) * rootDifferenceProduct α

/-- Generic degree-n polynomial over the integer coefficient polynomial ring. -/
def universalPolynomial (n : ℕ) : Polynomial (MvPolynomial (Fin (n + 1)) ℤ) :=
  Polynomial.ofFn (n + 1) (fun i => MvPolynomial.X i)

/-- An explicit integer coefficient polynomial, defined by a modified determinant. -/
def universalDiscriminant (n : ℕ) : MvPolynomial (Fin (n + 1)) ℤ :=
  (universalPolynomial n).discr

def RootProductEqualsDiscriminant : Prop :=
  ∀ (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
    (f : F[X]) (n : ℕ) (α : Fin n → L),
    f ≠ 0 → f.natDegree = n → 1 ≤ n →
    (f.map (algebraMap F L)).Splits →
    (List.ofFn α : Multiset L) = (f.map (algebraMap F L)).roots →
    rootDiscriminant (algebraMap F L f.leadingCoeff) α = algebraMap F L f.discr

def PermutationInvariance : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (α : Fin n → R) (σ : Equiv.Perm (Fin n)),
    rootDifferenceProduct (α ∘ σ) = rootDifferenceProduct α

def NumberingIndependence : Prop :=
  ∀ (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
    (f : F[X]) (n : ℕ) (α β : Fin n → L),
    f ≠ 0 → f.natDegree = n → 1 ≤ n →
    (f.map (algebraMap F L)).Splits →
    (List.ofFn α : Multiset L) = (f.map (algebraMap F L)).roots →
    (List.ofFn β : Multiset L) = (f.map (algebraMap F L)).roots →
    rootDiscriminant (algebraMap F L f.leadingCoeff) α =
      rootDiscriminant (algebraMap F L f.leadingCoeff) β

def VanishingIffRepeatedEntries : Prop :=
  ∀ (L : Type u) [Field L] (n : ℕ) (a : L) (α : Fin n → L), a ≠ 0 →
    (rootDiscriminant a α = 0 ↔ ∃ i j : Fin n, i < j ∧ α i = α j)

def VanishingIffRepeatedRoot : Prop :=
  ∀ (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
    (f : F[X]) (n : ℕ) (α : Fin n → L),
    f ≠ 0 → f.natDegree = n → 1 ≤ n →
    (f.map (algebraMap F L)).Splits →
    (List.ofFn α : Multiset L) = (f.map (algebraMap F L)).roots →
    (rootDiscriminant (algebraMap F L f.leadingCoeff) α = 0 ↔
      ∃ x : L, 2 ≤ (f.map (algebraMap F L)).rootMultiplicity x)

def DiscriminantResultantIdentity : Prop :=
  ∀ (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
    (f : F[X]) (n : ℕ) (α : Fin n → L),
    f ≠ 0 → f.natDegree = n → 1 ≤ n →
    (f.map (algebraMap F L)).Splits →
    (List.ofFn α : Multiset L) = (f.map (algebraMap F L)).roots →
    rootDiscriminant (algebraMap F L f.leadingCoeff) α =
      (-1 : L) ^ (n * (n - 1) / 2) * (algebraMap F L f.leadingCoeff)⁻¹ *
        algebraMap F L (fixedResultant f f.derivative n (n - 1))

/-- Specialization to every commutative ring when the stated degree survives. -/
def UniversalSpecialization : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R[X]) (n : ℕ), f.natDegree = n →
    MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i : Fin (n + 1) => f.coeff i)
      (universalDiscriminant n) = f.discr

/-- In particular the universal polynomial specializes to the source root formula. -/
def UniversalRootSpecialization : Prop :=
  ∀ (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
    (f : F[X]) (n : ℕ) (α : Fin n → L),
    f ≠ 0 → f.natDegree = n → 1 ≤ n →
    (f.map (algebraMap F L)).Splits →
    (List.ofFn α : Multiset L) = (f.map (algebraMap F L)).roots →
    algebraMap F L (MvPolynomial.eval₂Hom (Int.castRingHom F)
      (fun i : Fin (n + 1) => f.coeff i) (universalDiscriminant n)) =
      rootDiscriminant (algebraMap F L f.leadingCoeff) α

/-- Divisibility takes place before specialization, in the integer polynomial ring. -/
def UniversalResultantDivision : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    fixedResultant (universalPolynomial n) (universalPolynomial n).derivative n (n - 1) =
      (-1 : MvPolynomial (Fin (n + 1)) ℤ) ^ (n * (n - 1) / 2) *
        MvPolynomial.X (Fin.last n) * universalDiscriminant n

def DegreeOne : Prop :=
  ∀ (L : Type u) [Field L] (a : L) (α : Fin 1 → L), rootDiscriminant a α = 1

def ZeroDerivative : Prop :=
  ∀ (F : Type u) [Field F] (f : F[X]) (n : ℕ),
    f ≠ 0 → f.natDegree = n → 1 < n → f.derivative = 0 →
    fixedResultant f f.derivative n (n - 1) = 0 ∧ f.discr = 0

end Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant
