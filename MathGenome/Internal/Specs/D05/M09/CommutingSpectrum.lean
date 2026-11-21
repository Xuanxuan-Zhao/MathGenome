import MathGenome.Internal.Specs.D05.M08.Charpoly
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-! K05.09.commuting_spectrum, paper.tex:1347–1350.
The four characteristic-polynomial identities retain algebraic multiplicities.
The same ordered basis supplies both lists; the index type may be empty.
Polynomial spectral mapping is assigned separately to PolynomialMapping. -/

noncomputable section
open Polynomial
namespace Specs.D05.M09.CommutingSpectrum

/-- Full paired conclusion in a specified common triangular basis. -/
def PairedSpectrum {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    (S T : Module.End K V) : Prop :=
  let A := LinearMap.toMatrix b b S
  let B := LinearMap.toMatrix b b T
  A.IsUpperTriangular ∧ B.IsUpperTriangular ∧
  (∀ i, LinearMap.toMatrix b b (S + T) i i = A i i + B i i) ∧
  (∀ i, LinearMap.toMatrix b b (S * T) i i = A i i * B i i) ∧
  S.charpoly = ∏ i, (X - C (A i i)) ∧
  T.charpoly = ∏ i, (X - C (B i i)) ∧
  (S + T).charpoly = ∏ i, (X - C (A i i + B i i)) ∧
  (S * T).charpoly = ∏ i, (X - C (A i i * B i i)) ∧
  (∀ μ, S.HasEigenvalue μ ↔ ∃ i, μ = A i i) ∧
  (∀ μ, T.HasEigenvalue μ ↔ ∃ i, μ = B i i) ∧
  (∀ μ, (S + T).HasEigenvalue μ ↔ ∃ i, μ = A i i + B i i) ∧
  (∀ μ, (S * T).HasEigenvalue μ ↔ ∃ i, μ = A i i * B i i)

/-- The matrix calculation works over any named field once a common basis
is given; no diagonalizability assumption is needed. -/
def paired_in_basis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    (S T : Module.End K V),
    (LinearMap.toMatrix b b S).IsUpperTriangular →
    (LinearMap.toMatrix b b T).IsUpperTriangular → PairedSpectrum b S T

/-- Complex commuting operators admit a common pairing, with multiplicity. -/
def commuting_spectrum : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (S T : Module.End ℂ V), Commute S T →
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ V), PairedSpectrum b S T

/-- The paper's concrete diagonal operator on ℂ². -/
def diagonalExample : Module.End ℂ (Fin 2 → ℂ) :=
  Matrix.toLin' (Matrix.diagonal (fun i : Fin 2 => (i.val : ℂ)))

/-- Even when S = T, a Cartesian choice of eigenvalues need not be paired:
0 and 1 occur individually, but their sum 1 does not occur in S + S. -/
def arbitrary_pairing_counterexample : Prop :=
  Commute diagonalExample diagonalExample ∧
  diagonalExample.HasEigenvalue 0 ∧ diagonalExample.HasEigenvalue 1 ∧
  ¬ (diagonalExample + diagonalExample).HasEigenvalue (0 + 1)

end Specs.D05.M09.CommutingSpectrum
