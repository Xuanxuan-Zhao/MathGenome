import MathGenome.Internal.Specs.D05.M15.TensorDerivation
import MathGenome.Internal.Specs.D05.M15.ExteriorBasis
import MathGenome.Internal.Specs.D05.M15.WedgeSign
import MathGenome.Internal.Specs.D05.M04.Trace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-! The first-order square-zero lift defines a linear operator without assuming
Leibniz, grading, quotient descent, trace, or naturality. These are obligations below.
All constructions use arbitrary fields, with no finite-dimensional hypothesis until trace. -/
noncomputable section
namespace Specs.D05.M15.ExteriorDerivation
universe u v w
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- Value and variation on the generators, in the regular bimodule. -/
def firstOrderGenerator (A : V →ₗ[K] V) :
    V →ₗ[K] TrivSqZeroExt (_root_.ExteriorAlgebra K V) (_root_.ExteriorAlgebra K V) :=
  ((_root_.ExteriorAlgebra.ι K).prod ((_root_.ExteriorAlgebra.ι K).comp A))

/-- This relation is precisely what makes the first-order lift well-defined. -/
theorem firstOrderGenerator_square (A : V →ₗ[K] V) (v : V) :
    firstOrderGenerator A v * firstOrderGenerator A v = 0 := by
  apply TrivSqZeroExt.ext
  · exact _root_.ExteriorAlgebra.ι_sq_zero v
  · exact _root_.ExteriorAlgebra.ι_add_mul_swap v (A v)

def firstOrderLift (A : V →ₗ[K] V) :=
  _root_.ExteriorAlgebra.lift K ⟨firstOrderGenerator A, firstOrderGenerator_square A⟩

def induced (A : V →ₗ[K] V) :
    _root_.ExteriorAlgebra K V →ₗ[K] _root_.ExteriorAlgebra K V where
  toFun x := (firstOrderLift A x).snd
  map_add' x y := by simp
  map_smul' a x := by simp

def IsDerivation (D : _root_.ExteriorAlgebra K V →ₗ[K] _root_.ExteriorAlgebra K V) : Prop :=
  ∀ x y, D (x * y) = D x * y + x * D y

-- Independent full proposition types.
def induced_type := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
  (V →ₗ[K] V) → (_root_.ExteriorAlgebra K V →ₗ[K] _root_.ExteriorAlgebra K V)
def induced_value : induced_type.{u,v} := @induced

def induced_generator : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ (A : V →ₗ[K] V) (v : V),
  induced A (_root_.ExteriorAlgebra.ι K v) = _root_.ExteriorAlgebra.ι K (A v)
def induced_one : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ A : V →ₗ[K] V, induced A 1 = 0

def induced_leibniz : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ A : V →ₗ[K] V, IsDerivation (induced A)

def unique_extension : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ A : V →ₗ[K] V,
  ∃! D : _root_.ExteriorAlgebra K V →ₗ[K] _root_.ExteriorAlgebra K V,
    IsDerivation D ∧ ∀ v, D (_root_.ExteriorAlgebra.ι K v) = _root_.ExteriorAlgebra.ι K (A v)

def square_derivative : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ (A : V →ₗ[K] V) (v : V),
  TensorDerivation.induced A (_root_.TensorAlgebra.ι K v * _root_.TensorAlgebra.ι K v) =
    _root_.TensorAlgebra.ι K (A v) * _root_.TensorAlgebra.ι K v +
      _root_.TensorAlgebra.ι K v * _root_.TensorAlgebra.ι K (A v)

def quotient_descent : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ (A : V →ₗ[K] V) (t : _root_.TensorAlgebra K V),
  induced A (_root_.TensorAlgebra.toExterior t) =
    _root_.TensorAlgebra.toExterior (TensorDerivation.induced A t)

def ideal_preserved : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ (A : V →ₗ[K] V) (t : _root_.TensorAlgebra K V),
  t ∈ Exterior.definingIdeal_value K V →
    TensorDerivation.induced A t ∈ Exterior.definingIdeal_value K V

def induced_word : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ (A : V →ₗ[K] V) (p : ℕ) (x : Fin p → V),
  induced A (_root_.ExteriorAlgebra.ιMulti K p x) =
    ∑ j : Fin p, _root_.ExteriorAlgebra.ιMulti K p (Function.update x j (A (x j)))

def degree_preserved : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ (A : V →ₗ[K] V) (p : ℕ)
  (x : _root_.ExteriorAlgebra K V), x ∈ ⋀[K]^p V → induced A x ∈ ⋀[K]^p V

/-- Degree restrictions exist on the actual homogeneous submodules. -/
def power_restriction : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ (A : V →ₗ[K] V) (p : ℕ),
  ∃! D : (⋀[K]^p V) →ₗ[K] (⋀[K]^p V),
    ∀ x, (D x : _root_.ExteriorAlgebra K V) = induced A x

def top_basis_trace : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ (n : ℕ) (b : Module.Basis (Fin n) K V)
  (A : V →ₗ[K] V),
  induced A (_root_.ExteriorAlgebra.ιMulti K n b) =
    (∑ j : Fin n, b.repr (A (b j)) j) • _root_.ExteriorAlgebra.ιMulti K n b

def top_trace : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V],
  ∀ (A : V →ₗ[K] V) (x : ⋀[K]^(Module.finrank K V) V),
    induced A x = LinearMap.trace K V A • (x : _root_.ExteriorAlgebra K V)

def top_determinant : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V],
  ∀ (A : V →ₗ[K] V) (x : ⋀[K]^(Module.finrank K V) V),
    _root_.ExteriorAlgebra.map A x = LinearMap.det A • (x : _root_.ExteriorAlgebra K V)

def homomorphism_one : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ A : V →ₗ[K] V,
    _root_.ExteriorAlgebra.map A 1 = 1

def degree_zero : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ (A : V →ₗ[K] V) (x : ⋀[K]^0 V),
    induced A x = 0

def naturality : Prop := ∀ {K : Type u} {V : Type v} {W : Type w}
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (A : V →ₗ[K] V) (B : W →ₗ[K] W) (f : V →ₗ[K] W), B.comp f = f.comp A →
    ∀ x, induced B (_root_.ExteriorAlgebra.map f x) =
      _root_.ExteriorAlgebra.map f (induced A x)

def tensor_naturality : Prop := ∀ {K : Type u} {V : Type v} {W : Type w}
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (A : V →ₗ[K] V) (B : W →ₗ[K] W) (f : V →ₗ[K] W), B.comp f = f.comp A →
    ∀ x, TensorDerivation.induced B (WedgeSign.tensorMap_value f x) =
      WedgeSign.tensorMap_value f (TensorDerivation.induced A x)

/-- The analogous first variation in the ordinary commutative symmetric algebra. -/
def symmetricFirstOrderGenerator (A : V →ₗ[K] V) :
    V →ₗ[K] TrivSqZeroExt (SymmetricAlgebra K V) (SymmetricAlgebra K V) :=
  (SymmetricAlgebra.ι K V).prod ((SymmetricAlgebra.ι K V).comp A)

def symmetricInduced (A : V →ₗ[K] V) :
    SymmetricAlgebra K V →ₗ[K] SymmetricAlgebra K V where
  toFun x := (SymmetricAlgebra.lift (symmetricFirstOrderGenerator A) x).snd
  map_add' x y := by simp
  map_smul' a x := by simp

def symmetricInduced_type := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V],
  (V →ₗ[K] V) → (SymmetricAlgebra K V →ₗ[K] SymmetricAlgebra K V)
def symmetricInduced_value : symmetricInduced_type.{u,v} := @symmetricInduced

def symmetric_generator : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ (A : V →ₗ[K] V) (v : V),
    symmetricInduced A (SymmetricAlgebra.ι K V v) = SymmetricAlgebra.ι K V (A v)

def symmetric_leibniz : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V], ∀ (A : V →ₗ[K] V) (x y : SymmetricAlgebra K V),
    symmetricInduced A (x * y) = symmetricInduced A x * y + x * symmetricInduced A y

def symmetric_naturality : Prop := ∀ {K : Type u} {V : Type v} {W : Type w}
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (A : V →ₗ[K] V) (B : W →ₗ[K] W) (f : V →ₗ[K] W), B.comp f = f.comp A →
    ∀ x, symmetricInduced B (SymmetricAlgebra.lift ((SymmetricAlgebra.ι K W).comp f) x) =
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι K W).comp f) (symmetricInduced A x)

end Specs.D05.M15.ExteriorDerivation
