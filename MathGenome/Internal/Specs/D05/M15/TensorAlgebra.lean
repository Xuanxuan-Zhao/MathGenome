import MathGenome.Internal.Specs.D05.M06.ExternalSum
import MathGenome.Internal.Specs.D05.M15.AssociativitySymmetry
import MathGenome.Internal.Specs.D05.M15.TensorUniversal
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

/-!
Independent statements for K05.15.tensor_algebra, paper.tex:2886–2887.

The canonical tensor algebra is compared by an actual algebra isomorphism with
the external, finitely supported sum of the canonical finite tensor products.
Degree zero is identified with K by the normalized nullary equivalence: the
empty elementary tensor maps to 1. This is the same nullary convention as in
TensorUniversal, rather than an arbitrary one-dimensional identification.

Products of lists below are ordered products, so targets may be noncommutative.
All vector spaces have arbitrary dimension and K has arbitrary characteristic.
The algebra target may even be the zero algebra; no nontriviality is assumed.
-/

namespace Specs.D05.M15.TensorAlgebra

open scoped TensorProduct DirectSum
universe u v w

def tensorAlgebra_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Type (max u v)

def tensorAlgebra_value : tensorAlgebra_type.{u,v} :=
  fun K V _ _ _ => _root_.TensorAlgebra K V

def generator_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    (V →ₗ[K] _root_.TensorAlgebra K V)

def generator_value : generator_type.{u,v} :=
  fun K V _ _ _ => _root_.TensorAlgebra.ι K (M := V)

def homogeneousInclusion_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    (p : ℕ) → (TensorPower K p V →ₗ[K] _root_.TensorAlgebra K V)

def homogeneousInclusion_value : homogeneousInclusion_type.{u,v} :=
  fun _ _ _ _ _ _ => TensorPower.toTensorAlgebra

def directSumEquiv_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    (_root_.TensorAlgebra K V ≃ₐ[K] ⨁ p : ℕ, TensorPower K p V)

def directSumEquiv_value : directSumEquiv_type.{u,v} :=
  fun _ _ _ _ _ => _root_.TensorAlgebra.equivDirectSum

def extend_type :=
  (K : Type u) → (V : Type v) → (A : Type w) → [Field K] →
    [AddCommGroup V] → [Module K V] → [Ring A] → [Algebra K A] →
    (V →ₗ[K] A) → (_root_.TensorAlgebra K V →ₐ[K] A)

def extend_value : extend_type.{u,v,w} :=
  fun K _ _ _ _ _ _ _ f => _root_.TensorAlgebra.lift K f

section VectorSpace

/-- The degree-zero power is the scalar field, with its distinguished unit fixed. -/
def degree_zero : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∃ e : TensorPower K 0 V ≃ₗ[K] K,
    (∀ x : Fin 0 → V, e (PiTensorProduct.tprod K x) = 1) ∧
    (∀ a : K, e.symm a = TensorPower.algebraMap₀ a) ∧
    (∀ a : K, TensorPower.toTensorAlgebra (e.symm a) =
      algebraMap K (_root_.TensorAlgebra K V) a)

/-- The isomorphism carries every homogeneous tensor to its single component. -/
def direct_sum_inclusion : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (p : ℕ) (t : TensorPower K p V),
    _root_.TensorAlgebra.equivDirectSum (TensorPower.toTensorAlgebra t) =
      DirectSum.lof K ℕ (fun n => TensorPower K n V) p t

/-- The inverse map includes the given tensor, with no choice of coordinates. -/
def direct_sum_inverse : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (p : ℕ) (t : TensorPower K p V),
    (_root_.TensorAlgebra.equivDirectSum (R := K) (M := V)).symm
      (DirectSum.lof K ℕ (fun n => TensorPower K n V) p t) =
      TensorPower.toTensorAlgebra t

def homogeneous_injective : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ p : ℕ, Function.Injective
    (TensorPower.toTensorAlgebra : TensorPower K p V → _root_.TensorAlgebra K V)

/-- The components of every element have finite support. -/
def finite_support : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ x : _root_.TensorAlgebra K V,
    Set.Finite {p : ℕ | _root_.TensorAlgebra.equivDirectSum x p ≠ 0}

/-- Every finite-support tuple occurs, uniquely; this excludes a product model. -/
def component_characterization : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ c : (p : ℕ) → TensorPower K p V,
    (∃! x : _root_.TensorAlgebra K V,
      ∀ p, _root_.TensorAlgebra.equivDirectSum x p = c p) ↔
        Set.Finite {p | c p ≠ 0}

/-- Finite reconstruction by the homogeneous inclusion maps. -/
def reconstruction : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ x : _root_.TensorAlgebra K V,
    ∃ s : Finset ℕ,
      (∀ p ∉ s, _root_.TensorAlgebra.equivDirectSum x p = 0) ∧
      x = ∑ p ∈ s, TensorPower.toTensorAlgebra
        (_root_.TensorAlgebra.equivDirectSum x p)

/-- The elementary tensor inclusion is precisely the ordered generator word. -/
def elementary_word : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (p : ℕ) (x : Fin p → V),
    TensorPower.toTensorAlgebra (PiTensorProduct.tprod K x) =
      (List.ofFn (fun i => _root_.TensorAlgebra.ι K (x i))).prod

/-- Multiplication respects degree and is the canonical tensor concatenation. -/
def homogeneous_multiplication : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (p q : ℕ) (x : TensorPower K p V) (y : TensorPower K q V),
    TensorPower.toTensorAlgebra x * TensorPower.toTensorAlgebra y =
      TensorPower.toTensorAlgebra (TensorPower.mulEquiv (x ⊗ₜ[K] y))

/-- On elementary tensors this is word concatenation, including empty words. -/
def elementary_concatenation : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (p q : ℕ) (x : Fin p → V) (y : Fin q → V),
    TensorPower.toTensorAlgebra (PiTensorProduct.tprod K x) *
      TensorPower.toTensorAlgebra (PiTensorProduct.tprod K y) =
    TensorPower.toTensorAlgebra (PiTensorProduct.tprod K (Fin.append x y))

/-- Associative, bilinear multiplication on all finite sums; the empty word is 1. -/
def algebra_laws : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  (∀ x y z : _root_.TensorAlgebra K V, (x * y) * z = x * (y * z)) ∧
  (∀ x : _root_.TensorAlgebra K V, 1 * x = x ∧ x * 1 = x) ∧
  (∀ (a : K) (x y z : _root_.TensorAlgebra K V),
    (x + y) * z = x * z + y * z ∧ x * (y + z) = x * y + x * z ∧
      (a • x) * y = a • (x * y) ∧ x * (a • y) = a • (x * y)) ∧
  (∀ x : Fin 0 → V, TensorPower.toTensorAlgebra (PiTensorProduct.tprod K x) = 1)

/-- The generators together with the scalar unit generate the entire algebra. -/
def generated_by_vectors : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  Algebra.adjoin K (Set.range (_root_.TensorAlgebra.ι K (M := V))) = ⊤

end VectorSpace

section TargetAlgebra

/-- Existence and uniqueness for every linear map into any associative unital algebra. -/
def universal_property : Prop :=
  ∀ {K : Type u} {V : Type v} {A : Type w}
    [Field K] [AddCommGroup V] [Module K V] [Ring A] [Algebra K A],
  ∀ f : V →ₗ[K] A, ∃! F : _root_.TensorAlgebra K V →ₐ[K] A,
    ∀ v, F (_root_.TensorAlgebra.ι K v) = f v

def extend_generator : Prop :=
  ∀ {K : Type u} {V : Type v} {A : Type w}
    [Field K] [AddCommGroup V] [Module K V] [Ring A] [Algebra K A],
  ∀ (f : V →ₗ[K] A) v, _root_.TensorAlgebra.lift K f (_root_.TensorAlgebra.ι K v) = f v

/-- Scalars are sent to scalar multiples of the target unit. -/
def extend_scalar : Prop :=
  ∀ {K : Type u} {V : Type v} {A : Type w}
    [Field K] [AddCommGroup V] [Module K V] [Ring A] [Algebra K A],
  ∀ (f : V →ₗ[K] A) (a : K),
    _root_.TensorAlgebra.lift K f (algebraMap K (_root_.TensorAlgebra K V) a) = a • (1 : A)

/-- Each homogeneous restriction is the multilinear product linearization. -/
def extend_homogeneous : Prop :=
  ∀ {K : Type u} {V : Type v} {A : Type w}
    [Field K] [AddCommGroup V] [Module K V] [Ring A] [Algebra K A],
  ∀ (f : V →ₗ[K] A) (p : ℕ),
    ∃ L : TensorPower K p V →ₗ[K] A,
      (∀ x : Fin p → V, L (PiTensorProduct.tprod K x) =
        (List.ofFn (fun i => f (x i))).prod) ∧
      (∀ t, _root_.TensorAlgebra.lift K f (TensorPower.toTensorAlgebra t) = L t)

/-- The lift on an arbitrary element is the finite sum of its homogeneous maps. -/
def extend_finite_sum : Prop :=
  ∀ {K : Type u} {V : Type v} {A : Type w}
    [Field K] [AddCommGroup V] [Module K V] [Ring A] [Algebra K A],
  ∀ (f : V →ₗ[K] A) (s : Finset ℕ) (c : (p : ℕ) → TensorPower K p V),
    _root_.TensorAlgebra.lift K f (∑ p ∈ s, TensorPower.toTensorAlgebra (c p)) =
      ∑ p ∈ s, ((_root_.TensorAlgebra.lift K f).toLinearMap.comp
        (TensorPower.toTensorAlgebra : TensorPower K p V →ₗ[K] _root_.TensorAlgebra K V)) (c p)

/-- Any extending homomorphism has the same ordered word formula. -/
def extending_hom_word : Prop :=
  ∀ {K : Type u} {V : Type v} {A : Type w}
    [Field K] [AddCommGroup V] [Module K V] [Ring A] [Algebra K A],
  ∀ (f : V →ₗ[K] A) (F : _root_.TensorAlgebra K V →ₐ[K] A),
    (∀ v, F (_root_.TensorAlgebra.ι K v) = f v) →
    ∀ (p : ℕ) (x : Fin p → V),
      F (TensorPower.toTensorAlgebra (PiTensorProduct.tprod K x)) =
        (List.ofFn (fun i => f (x i))).prod

def hom_ext : Prop :=
  ∀ {K : Type u} {V : Type v} {A : Type w}
    [Field K] [AddCommGroup V] [Module K V] [Ring A] [Algebra K A],
  ∀ F G : _root_.TensorAlgebra K V →ₐ[K] A,
    (∀ v, F (_root_.TensorAlgebra.ι K v) = G (_root_.TensorAlgebra.ι K v)) → F = G

end TargetAlgebra
end Specs.D05.M15.TensorAlgebra
