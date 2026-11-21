import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CycleTypes
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Literal commuting polynomial alphabets for FR Chapter 3, lines 850–860 and
879–883. Coordinates use `Fin r`, so printed coordinate i is internal i-1.
The constructions also extend to r=0 with the stipulated empty products. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

abbrev Alphabet (r : ℕ) := MvPolynomial (Fin r) ℂ
def AlphabetType := ℕ → Type

def powerSum (r j : ℕ) : Alphabet r := ∑ i : Fin r, MvPolynomial.X i ^ j
def powerSumType := (r j : ℕ) → Alphabet r

/-- The finite support of the multiplicities implements the product over j≥1.
Partition parts are positive, and absent sizes contribute one. -/
def partitionPowerSum {n : ℕ} (r : ℕ) (ν : Partition n) : Alphabet r :=
  ∏ j ∈ ν.parts.toFinset, powerSum r j ^ cycleMultiplicity ν j
def partitionPowerSumType := {n : ℕ} → (r : ℕ) → Partition n → Alphabet r

/-- The z-factor is the previously established cycle centralizer factor. -/
abbrev zFactor {n : ℕ} (ν : Partition n) : ℕ := centralizerFactor ν
def zFactorType := {n : ℕ} → Partition n → ℕ

def staircase (r : ℕ) (j : Fin r) : ℕ := r - 1 - j.val
def staircaseType := (r : ℕ) → Fin r → ℕ

def alternant {r : ℕ} (b : Fin r → ℕ) : Alphabet r :=
  Matrix.det (Matrix.of fun i j : Fin r => (MvPolynomial.X i : Alphabet r) ^ b j)
def alternantType := {r : ℕ} → (Fin r → ℕ) → Alphabet r

def vandermonde (r : ℕ) : Alphabet r := alternant (staircase r)
def vandermondeType := (r : ℕ) → Alphabet r

/-- Ordinary polynomial coefficient, with a vector of natural exponents. -/
def naturalCoefficient {r : ℕ} (b : Fin r → ℕ) (p : Alphabet r) : ℂ :=
  p.coeff (Finsupp.equivFunOnFinite.symm b)
def naturalCoefficientType := {r : ℕ} → (Fin r → ℕ) → Alphabet r → ℂ

/-- The source convention for coefficient extraction at integer exponents. -/
def coefficient {r : ℕ} (b : Fin r → ℤ) (p : Alphabet r) : ℂ :=
  if ∀ i, 0 ≤ b i then naturalCoefficient (fun i => (b i).toNat) p else 0
def coefficientType := {r : ℕ} → (Fin r → ℤ) → Alphabet r → ℂ

def vandermonde_productType : Prop := ∀ r,
  vandermonde r = ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
    ((MvPolynomial.X i : Alphabet r) - MvPolynomial.X j)

def coefficient_of_negativeType : Prop := ∀ {r} (b : Fin r → ℤ) (p : Alphabet r),
  (∃ i, b i < 0) → coefficient b p = 0

def coefficient_of_nonnegativeType : Prop := ∀ {r} (b : Fin r → ℤ) (p : Alphabet r),
  (∀ i, 0 ≤ b i) → coefficient b p = naturalCoefficient (fun i => (b i).toNat) p

def coefficient_natCastType : Prop := ∀ {r} (b : Fin r → ℕ) (p : Alphabet r),
  coefficient (fun i => (b i : ℤ)) p = naturalCoefficient b p

def powerSum_isHomogeneousType : Prop := ∀ r j, (powerSum r j).IsHomogeneous j

def partitionPowerSum_isHomogeneousType : Prop := ∀ {n} r (ν : Partition n),
  (partitionPowerSum r ν).IsHomogeneous n

def empty_partitionPowerSumType : Prop := ∀ r,
  partitionPowerSum r emptyPartition = 1

def zero_alternantType : Prop := ∀ b : Fin 0 → ℕ, alternant b = 1

def zero_vandermondeType : Prop := vandermonde 0 = 1

def zero_powerSumType : Prop := ∀ j, powerSum 0 j = 0

end Specs.AdvancedFiniteGroupRepresentations
