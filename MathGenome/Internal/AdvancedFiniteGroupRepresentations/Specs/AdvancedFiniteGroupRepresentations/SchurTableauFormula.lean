import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SchurAlternant

/-! FR-C04, original source lines 981–1045. The number `m` of matrix rows
is independent of the alphabet size `r`. The cutoff assertion requires
`length p ≤ m`; truncating a tall partition to only `r` rows would be false. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Jacobi–Trudi with `m` padded rows in an alphabet of size `r`. -/
def paddedJacobiTrudiMatrix {n : ℕ} (p : Partition n) (r m : ℕ) :
    Matrix (Fin m) (Fin m) (PolynomialRing r) :=
  Matrix.of fun i j => h r ((rowLength p i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ))

def paddedJacobiTrudi {n : ℕ} (p : Partition n) (r m : ℕ) : PolynomialRing r :=
  (paddedJacobiTrudiMatrix p r m).det

def paddedJacobiTrudiMatrixType := {n : ℕ} → (p : Partition n) → (r m : ℕ) →
  Matrix (Fin m) (Fin m) (PolynomialRing r)
def paddedJacobiTrudiType := {n : ℕ} → (p : Partition n) → (r m : ℕ) → PolynomialRing r

def paddedJacobiTrudi_same_sizeType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r : ℕ), paddedJacobiTrudi p r r = jacobiTrudi p r

def paddedJacobiTrudi_succType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r m : ℕ), length p ≤ m →
    paddedJacobiTrudi p r (m + 1) = paddedJacobiTrudi p r m

def paddedJacobiTrudi_stableType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r m k : ℕ), length p ≤ m → m ≤ k →
    paddedJacobiTrudi p r k = paddedJacobiTrudi p r m

def paddedJacobiTrudi_eq_schurPolynomial_of_length_leType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r m : ℕ), length p ≤ m → length p ≤ r →
    paddedJacobiTrudi p r m = schurPolynomial p r

def empty_paddedJacobiTrudiType : Prop :=
  ∀ r m : ℕ, paddedJacobiTrudi emptyPartition r m = 1

def paddedJacobiTrudi_no_variablesType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (m : ℕ), length p ≤ m →
    paddedJacobiTrudi p 0 m = if n = 0 then 1 else 0

def tableauSum_no_variablesType : Prop :=
  ∀ {n : ℕ} (p : Partition n), tableauSum p 0 = if n = 0 then 1 else 0

/-- The substantial remaining identity, including all alphabet cutoffs. -/
def paddedJacobiTrudi_eq_tableauSumType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r m : ℕ), length p ≤ m →
    paddedJacobiTrudi p r m = tableauSum p r

def schurPolynomial_eq_tableauSumType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r : ℕ), schurPolynomial p r = tableauSum p r

def paddedJacobiTrudi_eq_schurPolynomialType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r m : ℕ), length p ≤ m →
    paddedJacobiTrudi p r m = schurPolynomial p r

def paddedJacobiTrudi_eq_zero_of_length_gtType : Prop :=
  ∀ {n r : ℕ} (p : Partition n) (m : ℕ), length p ≤ m → r < length p →
    paddedJacobiTrudi p r m = 0

/-- All three expressions in the original theorem, with the polynomial
quotient expressed through its uniquely characterizing product identity. -/
def schur_three_formulasType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r : ℕ), length p ≤ r →
    vandermonde r * schurPolynomial p r = partitionAlternant r p ∧
    schurPolynomial p r = jacobiTrudi p r ∧
    schurPolynomial p r = tableauSum p r

/-- The source's cutoff statement, with an adequate determinant row count. -/
def schur_length_cutoffType : Prop :=
  ∀ {n r : ℕ} (p : Partition n) (m : ℕ), length p ≤ m → r < length p →
    schurPolynomial p r = 0 ∧ paddedJacobiTrudi p r m = 0 ∧ tableauSum p r = 0

def empty_schur_three_formulasType : Prop :=
  ∀ r m : ℕ, schurPolynomial emptyPartition r = 1 ∧
    paddedJacobiTrudi emptyPartition r m = 1 ∧ tableauSum emptyPartition r = 1

end Specs.AdvancedFiniteGroupRepresentations
