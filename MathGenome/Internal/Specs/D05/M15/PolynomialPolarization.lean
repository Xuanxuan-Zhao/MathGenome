import MathGenome.Internal.Specs.D05.M15.PolynomialBridge
import MathGenome.Internal.Specs.D05.M15.MultilinearDimension
import MathGenome.Internal.Specs.D05.M15.PolynomialPolarization.SubsetIdentity

/-! K05.15.polynomial_polarization, paper.tex:3212–3226.
Formal homogeneous polynomials, rather than merely homogeneous functions, are
used. A finite basis represents the finite-dimensional hypothesis without
excluding dimension zero. The raw diagonal and symmetry are the upstream ones.
-/
noncomputable section
namespace Specs.D05.M15.PolynomialPolarization
open scoped BigOperators
open _root_.D05.M15.PolynomialPolarization

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Coordinate expansion of the raw diagonal of any multilinear form. -/
def diagonalPolynomial {n p : ℕ} (b : Module.Basis (Fin n) K V)
    (B : MultilinearMap K (fun _ : Fin p => V) K) : MvPolynomial (Fin n) K := by
  classical
  exact ∑ r : Fin p → Fin n, MvPolynomial.C (B (fun i => b (r i))) *
    ∏ i, MvPolynomial.X (r i)

/-- The average of products of functionals over all permutations of slots. -/
def averagedProduct {p : ℕ} (φ : Fin p → Module.Dual K V) :
    MultilinearMap K (fun _ : Fin p => V) K :=
  (p.factorial : K)⁻¹ • ∑ σ : Equiv.Perm (Fin p),
    ((MultilinearMap.mkPiRing K (Fin p) 1).compLinearMap φ).domDomCongr σ

def diagonalPolynomial_type := ∀ {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] {n p : ℕ} (b : Module.Basis (Fin n) K V),
    MultilinearMap K (fun _ : Fin p => V) K → MvPolynomial (Fin n) K

def diagonalPolynomial_value : diagonalPolynomial_type := @diagonalPolynomial

def averagedProduct_type := ∀ {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] {p : ℕ}, (Fin p → Module.Dual K V) →
    MultilinearMap K (fun _ : Fin p => V) K

def averagedProduct_value : averagedProduct_type := @averagedProduct

/-- Expansion is homogeneous of the specified degree, including the zero polynomial. -/
def diagonal_polynomial_homogeneous : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n p : ℕ}
    (b : Module.Basis (Fin n) K V) (B : MultilinearMap K (fun _ : Fin p => V) K),
    (diagonalPolynomial b B).IsHomogeneous p

/-- Evaluation is the actual upstream coordinate evaluation on V. -/
def diagonal_polynomial_evaluation : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n p : ℕ}
    (b : Module.Basis (Fin n) K V) (B : MultilinearMap K (fun _ : Fin p => V) K),
    PolynomialBridge.coordinateEvaluation b (diagonalPolynomial b B) = rawDiagonal B

/-- The monomial preimage is the explicit formula in the manuscript. -/
def averaged_product_formula : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {p : ℕ}
    (φ : Fin p → Module.Dual K V) (v : Fin p → V),
    averagedProduct φ v = (p.factorial : K)⁻¹ *
      ∑ σ : Equiv.Perm (Fin p), ∏ i, φ i (v (σ i))

def averaged_product_symmetric : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {p : ℕ}
    (φ : Fin p → Module.Dual K V), IsSymmetric (averagedProduct φ)

def averaged_product_diagonal : Prop :=
  ∀ {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {p : ℕ}
    (φ : Fin p → Module.Dual K V) (v : V),
    rawDiagonal (averagedProduct φ) v = ∏ i, φ i v

/-- Existence and uniqueness for every homogeneous formal polynomial.
No representation or decomposition certificate is assumed. -/
def homogeneous_polynomial_form : Prop :=
  ∀ {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n p : ℕ}
    (b : Module.Basis (Fin n) K V) (P : MvPolynomial (Fin n) K),
    P.IsHomogeneous p → ∃! B : MultilinearMap K (fun _ : Fin p => V) K,
      IsSymmetric B ∧ rawDiagonal B = PolynomialBridge.coordinateEvaluation b P

/-- Both directions of the correspondence for functions on the original space. -/
def diagonal_iff_polynomial : Prop :=
  ∀ {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n p : ℕ}
    (b : Module.Basis (Fin n) K V) (q : V → K),
    (∃ B : MultilinearMap K (fun _ : Fin p => V) K, IsSymmetric B ∧ rawDiagonal B = q) ↔
    ∃ P : MvPolynomial (Fin n) K, P.IsHomogeneous p ∧ PolynomialBridge.coordinateEvaluation b P = q

/-- Formal uniqueness uses the infinite-field consequence of characteristic zero. -/
def unique_formal_polynomial : Prop :=
  ∀ {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n p : ℕ}
    (b : Module.Basis (Fin n) K V) (B : MultilinearMap K (fun _ : Fin p => V) K),
    ∃! P : MvPolynomial (Fin n) K,
      P.IsHomogeneous p ∧ PolynomialBridge.coordinateEvaluation b P = rawDiagonal B

/-- The inverse subset formula, for these same raw diagonals and all arities. -/
def polarization_formula : Prop :=
  ∀ {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] (p : ℕ)
    (B : MultilinearMap K (fun _ : Fin p => V) K), IsSymmetric B →
    ∀ v : Fin p → V, B v = (p.factorial : K)⁻¹ *
      ∑ S : Finset (Fin p), (-1 : K) ^ (p - S.card) * rawDiagonal B (∑ i ∈ S, v i)

/-- Constants, including arbitrary scalar constants, are exactly the nullary case. -/
def degree_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Module.Basis (Fin n) K V) (B : MultilinearMap K (fun _ : Fin 0 => V) K),
    diagonalPolynomial b B = MvPolynomial.C (B (fun i => Fin.elim0 i)) ∧
    ∀ v : V, rawDiagonal B v = B (fun i => Fin.elim0 i)

end Specs.D05.M15.PolynomialPolarization
