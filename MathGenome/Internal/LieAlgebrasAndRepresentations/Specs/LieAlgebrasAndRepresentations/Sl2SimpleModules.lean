import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2Model
import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Independent statements for LA-C01, source lines 1123–1184.
The matrix Lie algebra and its generators are the canonical upstream objects.
The finite basis is extended by zero at its upper boundary; the coefficient of
the lower boundary is zero. All natural-number parameters include zero.
-/

noncomputable section

universe u v w

namespace Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules

open Sl2Model Module

def basisVector {k : Type u} {M : Type v} [Field k] [AddCommGroup M] [Module k M]
    {n : ℕ} (b : Basis (Fin (n + 1)) k M) (j : ℕ) : M :=
  if hj : j < n + 1 then b ⟨j, hj⟩ else 0

/-- The full displayed formulas (3.1), including both endpoints. -/
def IsStandardBasis {k : Type u} {M : Type v} [Field k] [AddCommGroup M]
    [Module k M] [LieRingModule (Model k) M] [LieModule k (Model k) M]
    {n : ℕ} (b : Basis (Fin (n + 1)) k M) : Prop :=
  ∀ j : Fin (n + 1),
    ⁅H k, b j⁆ = ((n : k) - 2 * (j.val : k)) • b j ∧
    ⁅F k, b j⁆ = basisVector b (j.val + 1) ∧
    ⁅E k, b j⁆ = ((j.val : k) * ((n : k) - (j.val : k) + 1)) •
      basisVector b (j.val - 1)

/-- Exhaustion and uniqueness of the nonnegative integer parameter. -/
def classificationExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (M : Type v) [AddCommGroup M] [Module k M]
    [LieRingModule (Model k) M] [LieModule k (Model k) M]
    [Nontrivial M] [FiniteDimensional k M] [LieModule.IsIrreducible k (Model k) M],
    ∃! n : ℕ, ∃ b : Basis (Fin (n + 1)) k M, IsStandardBasis b

/-- Existence of each standard module on the coefficient space of dimension n+1.
The action formulas refer to the actual coordinate basis, not to an assumed
representation certificate. The representation structures are conclusions. -/
def modelsExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] (n : ℕ),
    ∃ (a : LieRingModule (Model k) (Fin (n + 1) → k))
      (c : @LieModule k (Model k) (Fin (n + 1) → k) _ _ _ _ _ a),
      letI := a
      letI := c
      IsStandardBasis (Pi.basisFun k (Fin (n + 1))) ∧
        LieModule.IsIrreducible k (Model k) (Fin (n + 1) → k)

/-- Equal parameters yield a Lie-module isomorphism carrying the displayed bases
to one another. This identifies every classified module with the standard model. -/
def equivalenceExpected : Prop :=
  ∀ (k : Type u) [Field k] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module k M] [LieRingModule (Model k) M] [LieModule k (Model k) M]
    [AddCommGroup N] [Module k N] [LieRingModule (Model k) N] [LieModule k (Model k) N]
    (n : ℕ) (b : Basis (Fin (n + 1)) k M) (c : Basis (Fin (n + 1)) k N),
    IsStandardBasis b → IsStandardBasis c →
      ∃ φ : M ≃ₗ⁅k, Model k⁆ N, ∀ j, φ (b j) = c j

/-- Distinct parameters give nonisomorphic modules, without irreducibility
being an extra assumption. -/
def distinctExpected : Prop :=
  ∀ (k : Type u) [Field k] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module k M] [LieRingModule (Model k) M] [LieModule k (Model k) M]
    [AddCommGroup N] [Module k N] [LieRingModule (Model k) N] [LieModule k (Model k) N]
    (n m : ℕ) (_b : Basis (Fin (n + 1)) k M) (_c : Basis (Fin (m + 1)) k N),
    n ≠ m → IsEmpty (M ≃ₗ⁅k, Model k⁆ N)

abbrev Homogeneous (k : Type u) [Field k] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) k n

/-- The specified normalization n!/(n-j)! X^(n-j) Y^j in the actual
two-variable polynomial algebra, with X=X 0 and Y=X 1. -/
def normalizedMonomial (k : Type u) [Field k] (n : ℕ) (j : Fin (n + 1)) :
    MvPolynomial (Fin 2) k :=
  ((n.factorial : k) / ((n - j.val).factorial : k)) •
    (MvPolynomial.X 0 ^ (n - j.val) * MvPolynomial.X 1 ^ j.val)

/-- The polynomial realization, all three differential operators, the
normalized basis, and simplicity. This includes the trivial one-dimensional
representation at n=0. -/
def polynomialExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] (n : ℕ),
    ∃ (a : LieRingModule (Model k) (Homogeneous k n))
      (c : @LieModule k (Model k) (Homogeneous k n) _ _ _ _ _ a),
      letI := a
      letI := c
      ∃ b : Basis (Fin (n + 1)) k (Homogeneous k n),
        IsStandardBasis b ∧
        (∀ j, (b j).val = normalizedMonomial k n j) ∧
        (∀ p : Homogeneous k n,
          (⁅E k, p⁆ : Homogeneous k n).val = (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) * MvPolynomial.pderiv 1 p.val ∧
          (⁅F k, p⁆ : Homogeneous k n).val = (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) * MvPolynomial.pderiv 0 p.val ∧
          (⁅H k, p⁆ : Homogeneous k n).val = (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) * MvPolynomial.pderiv 0 p.val -
            (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) * MvPolynomial.pderiv 1 p.val) ∧
        LieModule.IsIrreducible k (Model k) (Homogeneous k n)

/-- The identification sends the displayed basis of any standard model to the
specified normalized monomials and intertwines the actual differential action. -/
def realizationExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (M : Type v) [AddCommGroup M] [Module k M]
    [LieRingModule (Model k) M] [LieModule k (Model k) M]
    (n : ℕ) (b : Basis (Fin (n + 1)) k M), IsStandardBasis b →
    ∃ (a : LieRingModule (Model k) (Homogeneous k n))
      (c : @LieModule k (Model k) (Homogeneous k n) _ _ _ _ _ a),
      letI := a
      letI := c
      ∃ φ : M ≃ₗ⁅k, Model k⁆ ↥(Homogeneous k n),
        (∀ j, (φ (b j)).val = normalizedMonomial k n j) ∧
        ∀ p : Homogeneous k n,
          (⁅E k, p⁆ : Homogeneous k n).val = (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) * MvPolynomial.pderiv 1 p.val ∧
          (⁅F k, p⁆ : Homogeneous k n).val = (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) * MvPolynomial.pderiv 0 p.val ∧
          (⁅H k, p⁆ : Homogeneous k n).val = (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) * MvPolynomial.pderiv 0 p.val -
            (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) * MvPolynomial.pderiv 1 p.val

end Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules
