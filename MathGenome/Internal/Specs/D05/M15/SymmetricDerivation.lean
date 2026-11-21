import MathGenome.Internal.Specs.D05.M15.Symmetric
import MathGenome.Internal.Specs.D05.M15.TensorDerivation
import MathGenome.Internal.Specs.D05.M15.Normalization.DividedPowers

/-! Independent objects for K05.15.symmetric_derivation, paper.tex:3192–3199.
The algebra and homogeneous images are the accepted symmetric quotient, with
no dimension or characteristic restriction. The first-order construction below
is a raw linear map; its derivation, extension, and grading properties are not
assumed. Divided powers retain the upstream factorial normalization. -/
noncomputable section
namespace Specs.D05.M15.SymmetricDerivation
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

abbrev S := _root_.SymmetricAlgebra K V

def firstOrderGenerator (f : V →ₗ[K] S (K := K) (V := V)) :
    V →ₗ[K] TrivSqZeroExt (S (K := K) (V := V)) (S (K := K) (V := V)) where
  toFun v := (_root_.SymmetricAlgebra.ι K V v, f v)
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · change _root_.SymmetricAlgebra.ι K V (x + y) = _root_.SymmetricAlgebra.ι K V x + _root_.SymmetricAlgebra.ι K V y
      exact map_add _ x y
    · change f (x + y) = f x + f y
      exact map_add _ x y
  map_smul' a x := by
    apply TrivSqZeroExt.ext
    · change _root_.SymmetricAlgebra.ι K V (a • x) = a • _root_.SymmetricAlgebra.ι K V x
      exact map_smul _ a x
    · change f (a • x) = a • f x
      exact map_smul _ a x

/-- The second component of the universal first-order algebra map. -/
def extend (f : V →ₗ[K] S (K := K) (V := V)) : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V) where
  toFun x := (_root_.SymmetricAlgebra.lift (firstOrderGenerator f) x).snd
  map_add' x y := by simp
  map_smul' a x := by simp

def contraction (φ : Module.Dual K V) : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V) :=
  extend ((Algebra.linearMap K (S (K := K) (V := V))).comp φ)

def induced (A : V →ₗ[K] V) : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V) :=
  extend ((_root_.SymmetricAlgebra.ι K V).comp A)

/-- Ordinary Leibniz rule, with no graded sign. -/
def IsDerivation (D : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V)) : Prop :=
  ∀ x y, D (x * y) = D x * y + x * D y

/-- Products of generators; the empty product is 1. -/
def word (p : ℕ) (x : Fin p → V) : S (K := K) (V := V) :=
  ∏ i, _root_.SymmetricAlgebra.ι K V (x i)

/-- Degree p is the canonical image of the degree-p tensor power in the quotient. -/
abbrev homogeneous (p : ℕ) : Submodule K (S (K := K) (V := V)) :=
  LinearMap.range (Symmetric.homogeneousMap K V p)


/-! Expected definition types and values. -/

def extend_type := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  (V →ₗ[K] S (K := K) (V := V)) → (S (K := K) (V := V) →ₗ[K] S (K := K) (V := V))
def extend_value : extend_type.{u,v} := @extend

def contraction_type := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  Module.Dual K V → (S (K := K) (V := V) →ₗ[K] S (K := K) (V := V))
def contraction_value : contraction_type.{u,v} := @contraction

def induced_type := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  (V →ₗ[K] V) → (S (K := K) (V := V) →ₗ[K] S (K := K) (V := V))
def induced_value : induced_type.{u,v} := @induced

def IsDerivation_type := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  (S (K := K) (V := V) →ₗ[K] S (K := K) (V := V)) → Prop
def IsDerivation_value : IsDerivation_type.{u,v} := @IsDerivation

def word_type := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  (p : ℕ) → (Fin p → V) → S (K := K) (V := V)
def word_value : word_type.{u,v} := @word

def homogeneous_type := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ℕ → Submodule K (S (K := K) (V := V))
def homogeneous_value : homogeneous_type.{u,v} := @homogeneous

/-! Independent theorem statements. -/

def extend_generator : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (f : V →ₗ[K] S (K := K) (V := V)) (v : V),
    extend f (_root_.SymmetricAlgebra.ι K V v) = f v

def extend_one : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (f : V →ₗ[K] S (K := K) (V := V)),
    extend f 1 = 0

def extend_mul : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (f : V →ₗ[K] S (K := K) (V := V)) (x y : S (K := K) (V := V)),
    extend f (x * y) = extend f x * y + x * extend f y

def one_of_leibniz : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (D : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V))
    (hD : IsDerivation D),
    D 1 = 0

def derivation_ext : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (D E : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V))
    (hD : IsDerivation D) (hE : IsDerivation E)
    (h : ∀ v, D (_root_.SymmetricAlgebra.ι K V v) = E (_root_.SymmetricAlgebra.ι K V v)),
    D = E

def extend_unique : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (f : V →ₗ[K] S (K := K) (V := V))
    (D : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V))
    (hD : IsDerivation D) (h : ∀ v, D (_root_.SymmetricAlgebra.ι K V v) = f v),
    D = extend f

def unique_extension : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (f : V →ₗ[K] S (K := K) (V := V)),
    ∃! D : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V),
      IsDerivation D ∧ ∀ v, D (_root_.SymmetricAlgebra.ι K V v) = f v

def contraction_generator : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (φ : Module.Dual K V) (v : V),
    contraction φ (_root_.SymmetricAlgebra.ι K V v) = algebraMap K _ (φ v)

def contraction_one : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (φ : Module.Dual K V),
    contraction φ 1 = 0

def contraction_mul : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (φ : Module.Dual K V) (x y : S (K := K) (V := V)),
    contraction φ (x * y) = contraction φ x * y + x * contraction φ y

def contraction_scalar : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (φ : Module.Dual K V) (a : K),
    contraction φ (algebraMap K _ a) = 0

def induced_generator : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (v : V),
    induced A (_root_.SymmetricAlgebra.ι K V v) = _root_.SymmetricAlgebra.ι K V (A v)

def induced_one : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V),
    induced A 1 = 0

def induced_mul : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (x y : S (K := K) (V := V)),
    induced A (x * y) = induced A x * y + x * induced A y

def induced_scalar : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (a : K),
    induced A (algebraMap K _ a) = 0

def contraction_word : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (φ : Module.Dual K V) (p : ℕ) (x : Fin p → V),
    contraction φ (word p x) =
      ∑ j : Fin p, φ (x j) • ∏ i ∈ (Finset.univ.erase j), _root_.SymmetricAlgebra.ι K V (x i)

def tensor_descent : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (t : _root_.TensorAlgebra K V),
    induced A (_root_.SymmetricAlgebra.algHom K V t) =
      _root_.SymmetricAlgebra.algHom K V (Specs.D05.M15.TensorDerivation.induced A t)

def ideal_invariant : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (t : _root_.TensorAlgebra K V)
    (ht : t ∈ Specs.D05.M15.Symmetric.commutatorIdeal K V),
    Specs.D05.M15.TensorDerivation.induced A t ∈ Specs.D05.M15.Symmetric.commutatorIdeal K V

def commutator_formula : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (u v : V),
    Specs.D05.M15.TensorDerivation.induced A
      (_root_.TensorAlgebra.ι K u * _root_.TensorAlgebra.ι K v -
        _root_.TensorAlgebra.ι K v * _root_.TensorAlgebra.ι K u) =
      (_root_.TensorAlgebra.ι K (A u) * _root_.TensorAlgebra.ι K v -
        _root_.TensorAlgebra.ι K v * _root_.TensorAlgebra.ι K (A u)) +
      (_root_.TensorAlgebra.ι K u * _root_.TensorAlgebra.ι K (A v) -
        _root_.TensorAlgebra.ι K (A v) * _root_.TensorAlgebra.ι K u)

def word_eq_homogeneousMap : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (p : ℕ) (x : Fin p → V),
    word p x = Specs.D05.M15.Symmetric.homogeneousMap K V p (PiTensorProduct.tprod K x)

def induced_word : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (p : ℕ) (x : Fin p → V),
    induced A (word p x) = ∑ j : Fin p, word p (Function.update x j (A (x j)))

def word_symmetric : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (p : ℕ) (x : Fin p → V) (σ : Equiv.Perm (Fin p)),
    word (K := K) p (x ∘ σ) = word p x

def contraction_power_factor : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (φ : Module.Dual K V) (p : ℕ),
    ∃! L : Specs.D05.M15.Symmetric.symmetricPower K V p →ₗ[K] S (K := K) (V := V),
      ∀ x, L (Specs.D05.M15.Symmetric.elementary K V p x) =
        ∑ j : Fin p, φ (x j) • ∏ i ∈ (Finset.univ.erase j), _root_.SymmetricAlgebra.ι K V (x i)

def induced_power_factor : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (p : ℕ),
    ∃! L : Specs.D05.M15.Symmetric.symmetricPower K V p →ₗ[K] S (K := K) (V := V),
      ∀ x, L (Specs.D05.M15.Symmetric.elementary K V p x) =
        ∑ j : Fin p, word p (Function.update x j (A (x j)))

def contraction_homogeneous_zero : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (φ : Module.Dual K V) (y : S (K := K) (V := V))
    (hy : y ∈ homogeneous (K := K) (V := V) 0),
    contraction φ y = 0

def contraction_homogeneous : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (φ : Module.Dual K V) (p : ℕ) (y : S (K := K) (V := V))
    (hy : y ∈ homogeneous (K := K) (V := V) (p + 1)),
    contraction φ y ∈ homogeneous (K := K) (V := V) p

def induced_homogeneous : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (p : ℕ) (t : TensorPower K p V),
    induced A (Specs.D05.M15.Symmetric.homogeneousMap K V p t) =
      Specs.D05.M15.Symmetric.homogeneousMap K V p (Specs.D05.M15.TensorDerivation.onPower A p t)

def induced_degree : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (p : ℕ) (y : S (K := K) (V := V))
    (hy : y ∈ homogeneous (K := K) (V := V) p),
    induced A y ∈ homogeneous (K := K) (V := V) p

def contraction_pow : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (φ : Module.Dual K V) (v : V) (p : ℕ),
    contraction φ ((_root_.SymmetricAlgebra.ι K V v) ^ p) =
      ((p : K) * φ v) • (_root_.SymmetricAlgebra.ι K V v) ^ (p - 1)

def contraction_dividedPower : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ [CharZero K] (φ : Module.Dual K V) (v : V) (p : ℕ),
    contraction φ (D05.Specs.M15.Normalization.DividedPowers.dividedPowerValue K (S (K := K) (V := V))
      (_root_.SymmetricAlgebra.ι K V v) (p + 1)) =
      φ v • D05.Specs.M15.Normalization.DividedPowers.dividedPowerValue K (S (K := K) (V := V))
        (_root_.SymmetricAlgebra.ι K V v) p

end Specs.D05.M15.SymmetricDerivation
