import MathGenome.Internal.Specs.D05.M15.TensorCoordinates

/-!
Independent statements for paper.tex:2751–2759, the trace and determinant
part of K05.15.tensor_coordinates. The tensor map and product basis are the
shared algebraic constructions. Finite dimension is the only dimension
hypothesis; no nonzero-dimension, invertibility, splitting, or characteristic
assumption is imposed.
-/

namespace Specs.D05.M15.TensorCoordinates.TraceDeterminant

open scoped TensorProduct BigOperators

/-- The intrinsic trace identity over any field. -/
def trace_tensor : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Module.End K V) (T : Module.End K W),
    LinearMap.trace K (V ⊗[K] W) (TensorProduct.map S T) =
      LinearMap.trace K V S * LinearMap.trace K W T

/-- The intermediate diagonal sum in the displayed formula, in specified
finite bases. `Fin 0` is allowed for either index. -/
def trace_diagonal_sum : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W)
    (S : Module.End K V) (T : Module.End K W),
    LinearMap.trace K (V ⊗[K] W) (TensorProduct.map S T) =
      ∑ i, ∑ j, LinearMap.toMatrix e e S i i * LinearMap.toMatrix f f T j j

/-- The exponents are the dimensions of the other factor. This includes
singular maps and zero-dimensional spaces. -/
def det_tensor : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Module.End K V) (T : Module.End K W),
    LinearMap.det (TensorProduct.map S T) =
      LinearMap.det S ^ Module.finrank K W * LinearMap.det T ^ Module.finrank K V

/-- Either zero-dimensional factor makes the tensor trace zero and its
empty determinant one. The dimension hypotheses make `finrank = 0`
express the zero space, rather than an infinite-dimensional space. -/
def zero_dimension : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Module.End K V) (T : Module.End K W),
    (Module.finrank K V = 0 ∨ Module.finrank K W = 0) →
      LinearMap.trace K (V ⊗[K] W) (TensorProduct.map S T) = 0 ∧
      LinearMap.det (TensorProduct.map S T) = 1

/-- The conventions used by the boundary cases, explicitly including 0^0. -/
def empty_conventions : Prop :=
  ∀ {K : Type*} [Field K] (A : Matrix (Fin 0) (Fin 0) K) (a : K),
    Matrix.det A = 1 ∧ Matrix.trace A = 0 ∧ a ^ (0 : ℕ) = 1

end Specs.D05.M15.TensorCoordinates.TraceDeterminant
