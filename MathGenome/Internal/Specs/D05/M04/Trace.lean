import MathGenome.Internal.Specs.D05.M04.ChangeBasis
import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.ZMod.Basic

/-!
Independent specifications for K05.04.trace, paper.tex:681–703.
Matrix and endomorphism traces are the canonical Mathlib definitions.
Finite index types include every ordered size `Fin n`, including zero.
The matrix identities hold over commutative rings. The final statements
also retain the entry's theorem on trace functionals and commutators.
-/
namespace Specs.D05.M04.Trace

open scoped BigOperators
open MatrixOfMap

/-- The trace is the finite sum of diagonal entries. -/
def trace_definition : Prop :=
  ∀ {R ι : Type*} [CommRing R] [Fintype ι] (A : Matrix ι ι R),
    Matrix.trace A = ∑ i, A i i

/-- The explicit double sum, with independent row and column sizes. -/
def trace_mul_expansion : Prop :=
  ∀ {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
    (A : Matrix ι κ R) (B : Matrix κ ι R),
    Matrix.trace (A * B) = ∑ i, ∑ j, A i j * B j i

def trace_mul_comm : Prop :=
  ∀ {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
    (A : Matrix ι κ R) (B : Matrix κ ι R),
    Matrix.trace (A * B) = Matrix.trace (B * A)

/-- Conjugation using an explicitly supplied inverse, over a ring. -/
def trace_conjugate : Prop :=
  ∀ {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A P Q : Matrix ι ι R), Q * P = 1 → P * Q = 1 →
      Matrix.trace (Q * A * P) = Matrix.trace A

/-- The inverse in the displayed formula is only used on an invertible matrix. -/
def trace_nonsingular_conjugate : Prop :=
  ∀ {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι R), IsUnit P →
      Matrix.trace (P⁻¹ * A * P) = Matrix.trace A

/-- The canonical endomorphism trace agrees with the paper's basis formula. -/
def trace_matrix_of_map : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    (T : V →ₗ[K] V),
    LinearMap.trace K V T = Matrix.trace (matrixOfMap_value b b T)

/-- Independence includes bases with separately specified finite ordered sizes. -/
def basis_trace_invariant : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {n m : ℕ} (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R V)
    (T : V →ₗ[R] V),
    Matrix.trace (matrixOfMap_value b b T) = Matrix.trace (matrixOfMap_value c c T)

/-- The accepted change-of-basis matrices preserve trace. -/
def change_basis_trace : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {n : ℕ} (b c : Module.Basis (Fin n) R V) (T : V →ₗ[R] V),
    Matrix.trace (matrixOfMap_value c c T) =
      Matrix.trace ((ChangeBasis.changeMatrix_value b c)⁻¹ *
        matrixOfMap_value b b T * ChangeBasis.changeMatrix_value b c) ∧
    Matrix.trace (matrixOfMap_value c c T) = Matrix.trace (matrixOfMap_value b b T)

def trace_linear_combination : Prop :=
  ∀ {R ι : Type*} [CommRing R] [Fintype ι]
    (a b : R) (A B : Matrix ι ι R),
    Matrix.trace (a • A + b • B) = a * Matrix.trace A + b * Matrix.trace B

def operator_trace_linear_combination : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (a b : K) (S T : V →ₗ[K] V),
    LinearMap.trace K V (a • S + b • T) =
      a * LinearMap.trace K V S + b * LinearMap.trace K V T

def trace_empty : Prop :=
  ∀ {R ι : Type*} [CommRing R] [Fintype ι] [IsEmpty ι]
    (A : Matrix ι ι R), Matrix.trace A = 0

def operator_trace_zero_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V),
    Module.finrank K V = 0 → LinearMap.trace K V T = 0

/-- This is the span of commutators, without an assertion about single commutators.
No positivity assumption on `n` is needed for this identity. -/
def commutator_span_eq_ker : Prop :=
  ∀ {K : Type*} [Field K] (n : ℕ),
    Submodule.span K {C : Matrix (Fin n) (Fin n) K |
      ∃ A B : Matrix (Fin n) (Fin n) K, C = A * B - B * A} =
      LinearMap.ker (Matrix.traceLinearMap (Fin n) K K)

/-- The scalar is unique only in positive dimension, over every field. -/
def cyclic_functional_iff : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ}, 0 < n →
    ∀ f : Matrix (Fin n) (Fin n) K →ₗ[K] K,
    (∀ A B : Matrix (Fin n) (Fin n) K, f (A * B) = f (B * A)) ↔
      ∃! c : K, f = c • Matrix.traceLinearMap (Fin n) K K

/-- Normalization determines trace only when the dimension is nonzero in the field. -/
def normalized_cyclic_functional : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ}, 0 < n →
    ∀ f : Matrix (Fin n) (Fin n) K →ₗ[K] K,
    (∀ A B : Matrix (Fin n) (Fin n) K, f (A * B) = f (B * A)) →
    f 1 = (n : K) → (n : K) ≠ 0 →
      f = Matrix.traceLinearMap (Fin n) K K

/-- In size zero there is only the zero functional; scalar uniqueness fails. -/
def empty_functional : Prop :=
  ∀ {K : Type*} [Field K]
    (f : Matrix (Fin 0) (Fin 0) K →ₗ[K] K),
    f = 0 ∧ ∀ c : K, c • Matrix.traceLinearMap (Fin 0) K K = 0

/-- The source's characteristic-two example shows why normalization needs its hypothesis. -/
def normalization_counterexample : Prop :=
  let f : Matrix (Fin 2) (Fin 2) (ZMod 2) →ₗ[ZMod 2] ZMod 2 := 0
  (∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), f (A * B) = f (B * A)) ∧
    f 1 = (2 : ZMod 2) ∧ f ≠ Matrix.traceLinearMap (Fin 2) (ZMod 2) (ZMod 2)

end Specs.D05.M04.Trace
