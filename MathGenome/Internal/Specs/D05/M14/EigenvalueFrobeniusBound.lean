import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M13.Normal
import MathGenome.Internal.Specs.D05.M14.Frobenius
import Mathlib.Algebra.Polynomial.Roots

/-! K05.14.eigenvalue_frobenius_bound, paper.tex:2648–2663.
`charpoly.roots` is a multiset, so eigenvalues are counted with algebraic
multiplicity. All statements include dimension zero. The matrix normality
condition is with respect to the standard complex inner product. -/
noncomputable section
namespace Specs.D05.M14.EigenvalueFrobeniusBound

universe u

def operator_bound : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V),
    (T.charpoly.roots.map (fun z : ℂ => ‖z‖ ^ 2)).sum ≤
      _root_.D05.frobeniusNorm T ^ 2

def operator_equality_iff : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V),
    (T.charpoly.roots.map (fun z : ℂ => ‖z‖ ^ 2)).sum =
      _root_.D05.frobeniusNorm T ^ 2 ↔ _root_.D05.normalOperator T

def matrix_bound : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
    (A.charpoly.roots.map (fun z : ℂ => ‖z‖ ^ 2)).sum ≤
      ∑ i, ∑ j, ‖A i j‖ ^ 2

def matrix_equality_iff : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
    (A.charpoly.roots.map (fun z : ℂ => ‖z‖ ^ 2)).sum =
      (∑ i, ∑ j, ‖A i j‖ ^ 2) ↔ A * A.conjTranspose = A.conjTranspose * A

/-- An arbitrary indexed eigenvalue list, with the multiplicities specified
by equality to the characteristic polynomial's root multiset. -/
def listed_eigenvalues : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ),
    (List.ofFn μ : Multiset ℂ) = A.charpoly.roots →
    (∑ i, ‖μ i‖ ^ 2) ≤ (∑ i, ∑ j, ‖A i j‖ ^ 2) ∧
      ((∑ i, ‖μ i‖ ^ 2) = (∑ i, ∑ j, ‖A i j‖ ^ 2) ↔
        A * A.conjTranspose = A.conjTranspose * A)

/-- Every matrix admits such a full list; no splitting premise is imposed. -/
def exists_eigenvalue_list : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
    ∃ μ : Fin n → ℂ, (List.ofFn μ : Multiset ℂ) = A.charpoly.roots

end Specs.D05.M14.EigenvalueFrobeniusBound
