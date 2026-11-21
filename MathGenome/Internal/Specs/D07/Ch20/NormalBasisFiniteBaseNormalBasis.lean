import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
Independent statement of the finite-base branch of K07.20.normal_basis,
paper.tex:5989. The extension is the specified `Algebra K L` between arbitrary
finite fields, not a chosen model of a field of a given cardinality.

The operator acts by the cardinality of K, not merely its characteristic.
Its minimal polynomial is taken in `Module.End K L`, whose multiplication
is composition. Both the cyclic-vector assertion and the actual ordered
basis are retained. No separability, normality, or invertibility of the
extension degree is assumed.
-/

noncomputable section
universe u v
namespace Specs.D07.Ch20.NormalBasisFiniteBaseNormalBasis

open Polynomial

/-- The K-linear relative Frobenius, with a canonical choice of finite enumeration. -/
def frobeniusOperator (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [Finite K] : Module.End K L := by
  letI := Fintype.ofFinite K
  exact (FiniteField.frobeniusAlgHom K L).toLinearMap

/-- The operator minimal polynomial and cyclic basis for every finite-field extension.
`n ≥ 1` is a conclusion, so the degree-one case is included without an extra premise. -/
def FiniteBaseNormalBasis : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [Finite L] (q n : ℕ),
    Nat.card K = q → Module.finrank K L = n →
      1 ≤ n ∧
      (∀ x : L, frobeniusOperator K L x = x ^ q) ∧
      minpoly K (frobeniusOperator K L) = X ^ n - 1 ∧
      (frobeniusOperator K L).charpoly = X ^ n - 1 ∧
      ∃ (a : L) (b : Module.Basis (Fin n) K L),
        Submodule.span K (Set.range (fun j : ℕ => (frobeniusOperator K L ^ j) a)) = ⊤ ∧
        (∀ i : Fin n, b i = (frobeniusOperator K L ^ (i : ℕ)) a) ∧
        (∀ i : Fin n, b i = a ^ (q ^ (i : ℕ)))

end Specs.D07.Ch20.NormalBasisFiniteBaseNormalBasis
