import MathGenome.Internal.Specs.D05.M15.TensorAlgebra
import MathGenome.Internal.Specs.D05.M15.TensorMaps
import Mathlib.LinearAlgebra.PiTensorProduct.Dual

/-! K05.15.tensor_derivation. All spaces have arbitrary dimension and the field
has arbitrary characteristic. The algebra is associative, not commutative.
The square-zero construction below is a definition, with no assumed Leibniz,
extension, or grading certificate. These properties are separate obligations. -/
namespace Specs.D05.M15.TensorDerivation
open scoped TensorProduct
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- Encode the value and its first variation in the regular bimodule. -/
def firstOrderGenerator (A : V →ₗ[K] V) :
    V →ₗ[K] TrivSqZeroExt (_root_.TensorAlgebra K V) (_root_.TensorAlgebra K V) where
  toFun v := (_root_.TensorAlgebra.ι K v, _root_.TensorAlgebra.ι K (A v))
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · change _root_.TensorAlgebra.ι K (x + y) = _root_.TensorAlgebra.ι K x + _root_.TensorAlgebra.ι K y
      exact map_add _ x y
    · change _root_.TensorAlgebra.ι K (A (x + y)) =
        _root_.TensorAlgebra.ι K (A x) + _root_.TensorAlgebra.ι K (A y)
      simp
  map_smul' a x := by
    apply TrivSqZeroExt.ext
    · change _root_.TensorAlgebra.ι K (a • x) = a • _root_.TensorAlgebra.ι K x
      exact map_smul _ a x
    · change _root_.TensorAlgebra.ι K (A (a • x)) = a • _root_.TensorAlgebra.ι K (A x)
      simp

/-- Candidate induced linear operator, to be proved a derivation. -/
def induced (A : V →ₗ[K] V) :
    _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V where
  toFun x := (_root_.TensorAlgebra.lift K (firstOrderGenerator A) x).snd
  map_add' x y := by simp
  map_smul' a x := by simp

/-- Sum of single-slot maps on the canonical degree-p tensor power. -/
noncomputable def onPower (A : V →ₗ[K] V) (p : ℕ) :
    TensorPower K p V →ₗ[K] TensorPower K p V :=
  ∑ j : Fin p, PiTensorProduct.map (Function.update (fun _ => LinearMap.id) j A)

/-- Leibniz uses right multiplication on the first term. In particular it is
not the commutative-algebra convention `x * D y + y * D x`. -/
def IsDerivation (D : _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V) : Prop :=
  ∀ x y, D (x * y) = D x * y + x * D y

-- Independent obligations. These definitions contain full proposition types only.

def induced_type :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    (V →ₗ[K] V) → (_root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V)

def induced_value : induced_type.{u,v} := @induced

def onPower_type :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    (V →ₗ[K] V) → (p : ℕ) → (TensorPower K p V →ₗ[K] TensorPower K p V)

noncomputable def onPower_value : onPower_type.{u,v} := @onPower

def induced_generator : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (v : V),
    induced A (_root_.TensorAlgebra.ι K v) = _root_.TensorAlgebra.ι K (A v)

def induced_one : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V),
    induced A 1 = 0

def induced_leibniz : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V),
    IsDerivation (induced A)

def induced_mul : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (x y : _root_.TensorAlgebra K V),
    induced A (x * y) = induced A x * y + x * induced A y

def one_of_leibniz : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (D : _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V)
    (hD : IsDerivation D),
    D 1 = 0

def derivation_ext : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (D E : _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V)
    (hD : IsDerivation D) (hE : IsDerivation E)
    (h : ∀ v, D (_root_.TensorAlgebra.ι K v) = E (_root_.TensorAlgebra.ι K v)),
    D = E

def induced_unique : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V)
    (D : _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V)
    (hD : IsDerivation D)
    (h : ∀ v, D (_root_.TensorAlgebra.ι K v) = _root_.TensorAlgebra.ι K (A v)),
    D = induced A

def induced_word : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (p : ℕ) (x : Fin p → V),
    induced A (_root_.TensorAlgebra.tprod K V p x) =
      ∑ j : Fin p, _root_.TensorAlgebra.tprod K V p (Function.update x j (A (x j)))

def onPower_tprod : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (p : ℕ) (x : Fin p → V),
    onPower A p (PiTensorProduct.tprod K x) =
      ∑ j : Fin p, PiTensorProduct.tprod K (Function.update x j (A (x j)))

def induced_homogeneous : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (p : ℕ) (t : TensorPower K p V),
    induced A (TensorPower.toTensorAlgebra t) =
      TensorPower.toTensorAlgebra (onPower A p t)

def slot_sum_multilinear : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (p : ℕ),
    ∃ m : MultilinearMap K (fun _ : Fin p => V) (TensorPower K p V),
      ∀ x, m x = ∑ j : Fin p, PiTensorProduct.tprod K (Function.update x j (A (x j)))

def induced_add : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A B : V →ₗ[K] V),
    induced (A + B) = induced A + induced B

def induced_smul : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (a : K) (A : V →ₗ[K] V),
    induced (a • A) = a • induced A

def commutator_leibniz : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (D E : _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V)
    (hD : IsDerivation D) (hE : IsDerivation E),
    IsDerivation (D.comp E - E.comp D)

def induced_commutator : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A B : V →ₗ[K] V),
    (induced A).comp (induced B) - (induced B).comp (induced A) =
      induced (A.comp B - B.comp A)

def onPower_zero : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V),
    onPower A 0 = 0

def induced_scalar : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (a : K),
    induced A (algebraMap K (_root_.TensorAlgebra K V) a) = 0

def induced_finite_sum : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (s : Finset ℕ)
    (c : (p : ℕ) → TensorPower K p V),
    induced A (∑ p ∈ s, TensorPower.toTensorAlgebra (c p)) =
      ∑ p ∈ s, TensorPower.toTensorAlgebra (onPower A p (c p))

def unique_extension : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V),
    ∃! D : _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V,
      IsDerivation D ∧ ∀ v, D (_root_.TensorAlgebra.ι K v) = _root_.TensorAlgebra.ι K (A v)

def homomorphism_word : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (p : ℕ) (x : Fin p → V),
    _root_.TensorAlgebra.lift K ((_root_.TensorAlgebra.ι K).comp A)
      (TensorPower.toTensorAlgebra (PiTensorProduct.tprod K x)) =
        TensorPower.toTensorAlgebra (PiTensorProduct.tprod K (fun i => A (x i)))

def homomorphism_one : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V),
    _root_.TensorAlgebra.lift K ((_root_.TensorAlgebra.ι K).comp A) 1 = 1

def derivation_ne_homomorphism : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V),
    induced A ≠ (_root_.TensorAlgebra.lift K ((_root_.TensorAlgebra.ι K).comp A)).toLinearMap

def tensor_duality : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (p : ℕ)
    (α : TensorPower K p (Module.Dual K V)) (t : TensorPower K p V),
    PiTensorProduct.dualDistrib (onPower A.dualMap p α) t =
      PiTensorProduct.dualDistrib α (onPower A p t)

def onPower_unique : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (p : ℕ)
    (L : TensorPower K p V →ₗ[K] TensorPower K p V)
    (hL : ∀ x : Fin p → V,
      L (PiTensorProduct.tprod K x) =
        ∑ j : Fin p, PiTensorProduct.tprod K (Function.update x j (A (x j)))),
    L = onPower A p

def onPower_leibniz : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A : V →ₗ[K] V) (p q : ℕ)
    (x : TensorPower K p V) (y : TensorPower K q V),
    onPower A (p + q) (TensorPower.mulEquiv (x ⊗ₜ[K] y)) =
      TensorPower.mulEquiv (onPower A p x ⊗ₜ[K] y) +
        TensorPower.mulEquiv (x ⊗ₜ[K] onPower A q y)

def onPower_commutator : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  ∀ (A B : V →ₗ[K] V) (p : ℕ) (t : TensorPower K p V),
    onPower A p (onPower B p t) - onPower B p (onPower A p t) =
      onPower (A.comp B - B.comp A) p t

end Specs.D05.M15.TensorDerivation
