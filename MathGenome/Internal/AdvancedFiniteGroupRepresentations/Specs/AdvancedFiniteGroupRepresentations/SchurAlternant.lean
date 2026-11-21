import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.AlternatingCauchyKernel
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SymmetricPolynomialData
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-! FR-C04, source lines 981–1008. The polynomial quotient is selected in
`MvPolynomial`, not in its fraction field. Existence and uniqueness are
separate obligations. Indices in the Jacobi–Trudi matrix are integers;
subtracting the two zero-based row/column labels gives the printed index. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Canonical polynomial quotient, extended by zero outside the row cutoff.
`epsilon` makes the definition independent of a proof of divisibility. -/
def schurPolynomial {n : ℕ} (p : Partition n) (r : ℕ) : Alphabet r :=
  if length p ≤ r then
    Classical.epsilon (fun q : Alphabet r => vandermonde r * q = partitionAlternant r p)
  else 0

def jacobiTrudiMatrix {n : ℕ} (p : Partition n) (r : ℕ) :
    Matrix (Fin r) (Fin r) (PolynomialRing r) :=
  Matrix.of fun i j => h r ((rowLength p i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ))

def jacobiTrudi {n : ℕ} (p : Partition n) (r : ℕ) : PolynomialRing r :=
  (jacobiTrudiMatrix p r).det

def schurPolynomialType := {n : ℕ} → Partition n → (r : ℕ) → Alphabet r

def jacobiTrudiMatrixType := {n : ℕ} → Partition n → (r : ℕ) →
  Matrix (Fin r) (Fin r) (PolynomialRing r)

def jacobiTrudiType := {n : ℕ} → Partition n → (r : ℕ) → PolynomialRing r

def vandermonde_ne_zeroType : Prop := ∀ r : ℕ, vandermonde r ≠ 0

def vandermonde_dvd_partitionAlternantType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r : ℕ), vandermonde r ∣ partitionAlternant r p

def schurPolynomial_characterizationType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r : ℕ), length p ≤ r →
    vandermonde r * schurPolynomial p r = partitionAlternant r p

def schurPolynomial_uniqueType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r : ℕ), length p ≤ r →
    ∀ q : Alphabet r, vandermonde r * q = partitionAlternant r p →
      q = schurPolynomial p r

def schurPolynomial_isSymmetricType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r : ℕ), (schurPolynomial p r).IsSymmetric

def schurPolynomial_eq_jacobiTrudiType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r : ℕ), length p ≤ r →
    schurPolynomial p r = jacobiTrudi p r

def schurPolynomial_eq_zero_of_length_gtType : Prop :=
  ∀ {n r : ℕ} (p : Partition n), r < length p → schurPolynomial p r = 0

def empty_schurPolynomialType : Prop :=
  ∀ r : ℕ, schurPolynomial emptyPartition r = 1

def schurPolynomial_no_variablesType : Prop :=
  ∀ {n : ℕ} (p : Partition n), schurPolynomial p 0 = if n = 0 then 1 else 0

end Specs.AdvancedFiniteGroupRepresentations
