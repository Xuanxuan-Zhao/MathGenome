import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ZMod.Basic

/-!
Independent statements for K05.04.trace, paper.tex:687–703.

Matrices, linear functionals, span, kernel, and trace use the canonical Mathlib
objects. Scalar uniqueness requires a positive matrix size; the span identity
also includes size zero. The normalization hypothesis explicitly retains the
nonvanishing of the dimension in the field.
-/

namespace Specs.D05.M04.Trace.Commutators

/-- The linear span of all matrix commutators is exactly the trace kernel.
This includes size zero and asserts a span equality, not single-commutator
representability. -/
def commutator_span_eq_ker : Prop :=
  ∀ {K : Type*} [Field K] (n : ℕ),
    Submodule.span K {C : Matrix (Fin n) (Fin n) K |
      ∃ A B : Matrix (Fin n) (Fin n) K, C = A * B - B * A} =
      LinearMap.ker (Matrix.traceLinearMap (Fin n) K K)

/-- In positive size, cyclic linear functionals are exactly the scalar
multiples of trace, with a unique scalar, over an arbitrary field. -/
def cyclic_functional_iff : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ}, 0 < n →
    ∀ f : Matrix (Fin n) (Fin n) K →ₗ[K] K,
      (∀ A B : Matrix (Fin n) (Fin n) K, f (A * B) = f (B * A)) ↔
        ∃! c : K, f = c • Matrix.traceLinearMap (Fin n) K K

/-- The value at the identity determines trace when the dimension is nonzero
as a field element. No characteristic-zero assumption is imposed. -/
def normalized_cyclic_functional : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ}, 0 < n →
    ∀ f : Matrix (Fin n) (Fin n) K →ₗ[K] K,
      (∀ A B : Matrix (Fin n) (Fin n) K, f (A * B) = f (B * A)) →
      f 1 = (n : K) → (n : K) ≠ 0 →
        f = Matrix.traceLinearMap (Fin n) K K

/-- At size zero every functional is zero, and every scalar multiple of trace
is zero; hence the scalar cannot be unique. -/
def empty_functional : Prop :=
  ∀ {K : Type*} [Field K]
    (f : Matrix (Fin 0) (Fin 0) K →ₗ[K] K),
    f = 0 ∧ ∀ c : K, c • Matrix.traceLinearMap (Fin 0) K K = 0

/-- In characteristic two and size two, the zero functional is cyclic and has
the required value at the identity but differs from trace. -/
def normalization_counterexample : Prop :=
  let f : Matrix (Fin 2) (Fin 2) (ZMod 2) →ₗ[ZMod 2] ZMod 2 := 0
  (∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), f (A * B) = f (B * A)) ∧
    f 1 = (2 : ZMod 2) ∧ f ≠ Matrix.traceLinearMap (Fin 2) (ZMod 2) (ZMod 2)

end Specs.D05.M04.Trace.Commutators
