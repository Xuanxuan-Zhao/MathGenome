import MathGenome.Internal.Specs.D05.M04.ChangeBasis
import MathGenome.Internal.Specs.D05.M15.TensorBasis
import MathGenome.Internal.Specs.D05.M15.TensorMaps
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant

/-!
Independent statements for K05.15.tensor_coordinates. Coordinates always
refer to the specified product basis. P and Q have NEW basis vectors as
columns in the OLD bases. No nonempty-index or characteristic assumption
is imposed. General coordinates have finite support; matrix multiplication
and ordinary inverses here use finite ordered bases, including empty ones.
-/
namespace Specs.D05.M15.TensorCoordinates

open scoped TensorProduct Kronecker
open Matrix

universe u v w x y

def coefficients_type :=
  ∀ {K : Type u} {V : Type v} {W : Type w} {I : Type x} {J : Type y}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    Module.Basis I K V → Module.Basis J K W → (V ⊗[K] W) → Matrix I J K

noncomputable def coefficients_value : coefficients_type.{u,v,w,x,y} :=
  fun e f t i j => (e.tensorProduct f).repr t (i,j)

def coefficient_tmul : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : Module.Basis I K V)
    (f : Module.Basis J K W) (v : V) (w : W) (i : I) (j : J),
    coefficients_value e f (v ⊗ₜ[K] w) i j = e.repr v i * f.repr w j

/-- Arbitrary-dimensional matrix entries, expressed as basis coordinates. -/
def general_map_entry : Prop :=
  ∀ {K V W U Z I J I' J' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup U] [Module K U] [AddCommGroup Z] [Module K Z]
    (e : Module.Basis I K V) (f : Module.Basis J K W)
    (u : Module.Basis I' K U) (v : Module.Basis J' K Z)
    (S : V →ₗ[K] U) (T : W →ₗ[K] Z) (k : I') (l : J') (i : I) (j : J),
    coefficients_value u v (TensorProduct.map S T (e i ⊗ₜ[K] f j)) k l =
      u.repr (S (e i)) k * v.repr (T (f j)) l

/-- Basis change in arbitrary dimension: only the finite support of the
new tensor coordinates is summed. Reversing the bases gives its inverse. -/
def basis_change_finsupp : Prop :=
  ∀ {K V W I J I' J' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : Module.Basis I K V) (f : Module.Basis J K W)
    (e' : Module.Basis I' K V) (f' : Module.Basis J' K W)
    (t : V ⊗[K] W) (i : I) (j : J),
    coefficients_value e f t i j =
      ∑ p ∈ ((e'.tensorProduct f').repr t).support,
        coefficients_value e' f' t p.1 p.2 * e.repr (e' p.1) i * f.repr (f' p.2) j

/-- Actual finite-support reconstruction, even for infinite bases. -/
def reconstruction : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : Module.Basis I K V)
    (f : Module.Basis J K W) (t : V ⊗[K] W),
    (∑ p ∈ ((e.tensorProduct f).repr t).support,
      coefficients_value e f t p.1 p.2 • (e p.1 ⊗ₜ[K] f p.2)) = t

def finite_reconstruction : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W)
    (t : V ⊗[K] W),
    t = ∑ i, ∑ j, coefficients_value e f t i j • (e i ⊗ₜ[K] f j)

/-- The matrix is the Kronecker product, with the first factor index first. -/
def kronecker_matrix : Prop :=
  ∀ {K V W U Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [AddCommGroup Z] [Module K Z] {n m r s : ℕ}
    (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W)
    (u : Module.Basis (Fin r) K U) (v : Module.Basis (Fin s) K Z)
    (S : V →ₗ[K] U) (T : W →ₗ[K] Z),
    LinearMap.toMatrix (e.tensorProduct f) (u.tensorProduct v) (TensorProduct.map S T) =
      (LinearMap.toMatrix e u S) ⊗ₖ (LinearMap.toMatrix f v T)

def kronecker_entry : Prop :=
  ∀ {K V W U Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [AddCommGroup Z] [Module K Z] {n m r s : ℕ}
    (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W)
    (u : Module.Basis (Fin r) K U) (v : Module.Basis (Fin s) K Z)
    (S : V →ₗ[K] U) (T : W →ₗ[K] Z)
    (k : Fin r) (l : Fin s) (i : Fin n) (j : Fin m),
    LinearMap.toMatrix (e.tensorProduct f) (u.tensorProduct v)
      (TensorProduct.map S T) (k,l) (i,j) =
      LinearMap.toMatrix e u S k i * LinearMap.toMatrix f v T l j

/-- The expansion stated in the manuscript, rather than only a matrix name. -/
def map_basis_expansion : Prop :=
  ∀ {K V W U Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [AddCommGroup Z] [Module K Z] {n m r s : ℕ}
    (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W)
    (u : Module.Basis (Fin r) K U) (v : Module.Basis (Fin s) K Z)
    (S : V →ₗ[K] U) (T : W →ₗ[K] Z) (i : Fin n) (j : Fin m),
    TensorProduct.map S T (e i ⊗ₜ[K] f j) =
      ∑ k, ∑ l, (LinearMap.toMatrix e u S k i * LinearMap.toMatrix f v T l j) •
        (u k ⊗ₜ[K] v l)

/-- General coefficient transformation under two linear maps. -/
def map_coefficients : Prop :=
  ∀ {K V W U Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [AddCommGroup Z] [Module K Z] {n m r s : ℕ}
    (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W)
    (u : Module.Basis (Fin r) K U) (v : Module.Basis (Fin s) K Z)
    (S : V →ₗ[K] U) (T : W →ₗ[K] Z) (t : V ⊗[K] W),
    coefficients_value u v (TensorProduct.map S T t) =
      LinearMap.toMatrix e u S * coefficients_value e f t * (LinearMap.toMatrix f v T)ᵀ

/-- C_old = P C_new Q^t, with P and Q the accepted coordinate conversions. -/
def basis_change_old : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (e e' : Module.Basis (Fin n) K V) (f f' : Module.Basis (Fin m) K W)
    (t : V ⊗[K] W),
    coefficients_value e f t =
      Specs.D05.M04.ChangeBasis.changeMatrix_value e e' * coefficients_value e' f' t *
        (Specs.D05.M04.ChangeBasis.changeMatrix_value f f')ᵀ

/-- C_new = P^-1 C_old (Q^-1)^t; invertibility is proved upstream. -/
def basis_change_new : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (e e' : Module.Basis (Fin n) K V) (f f' : Module.Basis (Fin m) K W)
    (t : V ⊗[K] W),
    coefficients_value e' f' t =
      (Specs.D05.M04.ChangeBasis.changeMatrix_value e e')⁻¹ * coefficients_value e f t *
        ((Specs.D05.M04.ChangeBasis.changeMatrix_value f f')⁻¹)ᵀ

/-- The flattened index is j + m*i, so the second index runs fastest. -/
def lexicographic_entry : Prop :=
  ∀ {K V W U Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [AddCommGroup Z] [Module K Z] {n m r s : ℕ}
    (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W)
    (u : Module.Basis (Fin r) K U) (v : Module.Basis (Fin s) K Z)
    (S : V →ₗ[K] U) (T : W →ₗ[K] Z)
    (k : Fin r) (l : Fin s) (i : Fin n) (j : Fin m),
    LinearMap.toMatrix ((e.tensorProduct f).reindex finProdFinEquiv)
      ((u.tensorProduct v).reindex finProdFinEquiv) (TensorProduct.map S T)
        (finProdFinEquiv (k,l)) (finProdFinEquiv (i,j)) =
      LinearMap.toMatrix e u S k i * LinearMap.toMatrix f v T l j

/-- Bridge between the conversion matrix and the displayed basis equations. -/
def basis_columns : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e e' : Module.Basis (Fin n) K V) (a : Fin n),
    e' a = ∑ i, Specs.D05.M04.ChangeBasis.changeMatrix_value e e' i a • e i

/-! The separately headed trace/determinant and zero-factor supplement. -/
def trace_tensor : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Module.End K V) (T : Module.End K W),
    LinearMap.trace K (V ⊗[K] W) (TensorProduct.map S T) =
      LinearMap.trace K V S * LinearMap.trace K W T

def det_tensor : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Module.End K V) (T : Module.End K W),
    LinearMap.det (TensorProduct.map S T) =
      LinearMap.det S ^ Module.finrank K W * LinearMap.det T ^ Module.finrank K V

/-- X ↦ A X B, using composition in the existing endomorphism algebra. -/
def sandwich {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A B : Module.End K V) : Module.End K (Module.End K V) :=
  (LinearMap.mulLeft K A).comp (LinearMap.mulRight K B)

/-- The canonical tensor-Hom identification intertwines the two actions. -/
def sandwich_tensor_bridge : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : Module.End K V),
    (sandwich A B).comp (dualTensorHomEquiv K V V).toLinearMap =
      (dualTensorHomEquiv K V V).toLinearMap.comp (TensorProduct.map B.dualMap A)

def trace_sandwich : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : Module.End K V),
    LinearMap.trace K (Module.End K V) (sandwich A B) =
      LinearMap.trace K V A * LinearMap.trace K V B

def det_sandwich : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : Module.End K V),
    LinearMap.det (sandwich A B) =
      (LinearMap.det A * LinearMap.det B) ^ Module.finrank K V

/-- The forward implication holds for zero factors as well. -/
def injective_tensor : Prop :=
  ∀ {K V W U Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [AddCommGroup Z] [Module K Z] (S : V →ₗ[K] U) (T : W →ₗ[K] Z),
    Function.Injective S → Function.Injective T → Function.Injective (TensorProduct.map S T)

/-- The converse requires both DOMAIN spaces to be nonzero, in arbitrary dimension. -/
def injective_factors : Prop :=
  ∀ {K V W U Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [AddCommGroup Z] [Module K Z] [Nontrivial V] [Nontrivial W]
    (S : V →ₗ[K] U) (T : W →ₗ[K] Z),
    Function.Injective (TensorProduct.map S T) → Function.Injective S ∧ Function.Injective T

/-- Invertible iff both factors are invertible, for positive factor dimensions. -/
def invertible_factors : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    [Nontrivial V] [Nontrivial W] (S : Module.End K V) (T : Module.End K W),
    IsUnit (TensorProduct.map S T) ↔ IsUnit S ∧ IsUnit T

/-- With a zero factor the tensor endomorphism is always invertible, has
trace zero and determinant one, regardless of the other factor. -/
def zero_factor : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Module.End K V) (T : Module.End K W),
    (Subsingleton V ∨ Subsingleton W) →
      IsUnit (TensorProduct.map S T) ∧
      LinearMap.trace K (V ⊗[K] W) (TensorProduct.map S T) = 0 ∧
      LinearMap.det (TensorProduct.map S T) = 1

end Specs.D05.M15.TensorCoordinates
