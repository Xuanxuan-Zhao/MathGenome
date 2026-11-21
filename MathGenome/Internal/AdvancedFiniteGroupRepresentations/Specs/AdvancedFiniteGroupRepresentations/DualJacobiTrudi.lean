import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SchurTableauFormula

/-! FR-C09, source lines 1231–1269. The alphabet size and padded
matrix size are independent; integer degrees preserve the zero convention. -/
noncomputable section
namespace Specs.AdvancedFiniteGroupRepresentations

def dualJacobiTrudiMatrix {n : ℕ} (p : Partition n) (r q : ℕ) :
    Matrix (Fin q) (Fin q) (PolynomialRing r) :=
  Matrix.of fun i j => e r ((rowLength (transpose p) i.val : ℤ) - i.val + j.val)

def dualJacobiTrudi {n : ℕ} (p : Partition n) (r q : ℕ) : PolynomialRing r :=
  (dualJacobiTrudiMatrix p r q).det

def dualJacobiTrudiMatrixType := {n : ℕ} → (p : Partition n) → (r q : ℕ) →
  Matrix (Fin q) (Fin q) (PolynomialRing r)
def dualJacobiTrudiType := {n : ℕ} → (p : Partition n) → (r q : ℕ) → PolynomialRing r

def dualJacobiTrudi_succType : Prop := ∀ {n} (p : Partition n) r q,
  rowLength p 0 ≤ q → dualJacobiTrudi p r (q+1) = dualJacobiTrudi p r q

def empty_dualJacobiTrudiType : Prop := ∀ r q,
  dualJacobiTrudi emptyPartition r q = 1

def dualJacobiTrudi_no_variablesType : Prop := ∀ {n} (p : Partition n) q,
  rowLength p 0 ≤ q → dualJacobiTrudi p 0 q = if n = 0 then 1 else 0

def dual_jacobi_trudiType : Prop := ∀ {n} (p : Partition n) (r q : ℕ),
  rowLength p 0 ≤ q → schurPolynomial p r = dualJacobiTrudi p r q

end Specs.AdvancedFiniteGroupRepresentations
