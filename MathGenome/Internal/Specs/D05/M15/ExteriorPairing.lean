import MathGenome.Internal.Specs.D05.M15.ExteriorBasis
import MathGenome.Internal.Specs.D05.M15.WedgeSign
import MathGenome.Internal.Specs.D05.M07.DualMap
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.Dual.Basis

/-! K05.15.exterior_pairing, paper.tex:3081–3098.
The exterior powers are the canonical homogeneous submodules of the square
quotient. The determinant pairing is defined without division. The normalized
tensor alternation is a separate map, and its comparison theorems explicitly
require the factorial to be nonzero in the field. All degrees include zero.
-/

noncomputable section
namespace Specs.D05.M15.ExteriorPairing

universe u v w

abbrev pairing_type := (K : Type u) → (V : Type v) →
  [Field K] → [AddCommGroup V] → [Module K V] → (p : ℕ) →
  (⋀[K]^p (Module.Dual K V)) →ₗ[K] Module.Dual K (⋀[K]^p V)

abbrev pairing_value : pairing_type := fun K V _ _ _ p => exteriorPower.pairingDual K V p

/-- Ordinary tensor evaluation: elementary tensors evaluate by a product. -/
abbrev tensorEvaluation_type := (K : Type u) → (V : Type v) →
  [Field K] → [AddCommGroup V] → [Module K V] → (p : ℕ) →
  TensorPower K p (Module.Dual K V) →ₗ[K] Module.Dual K (TensorPower K p V)

abbrev tensorEvaluation_value : tensorEvaluation_type :=
  fun K V _ _ _ p => TensorPower.pairingDual K V p

/-- Normalized alternation, expressed using the quotient and the signed tensor
lift. Its elementary formula below identifies it with the permutation average. -/
abbrev average_type := (K : Type u) → (V : Type v) →
  [Field K] → [AddCommGroup V] → [Module K V] → (p : ℕ) →
  TensorPower K p V →ₗ[K] TensorPower K p V

abbrev average_value : average_type := fun K V _ _ _ p =>
  (Nat.factorial p : K)⁻¹ •
    (exteriorPower.toTensorPower K V p).comp (Exterior.tensorProjection_value K V p)

def elementary : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (f : Fin p → Module.Dual K V) (x : Fin p → V),
    pairing_value K V p (exteriorPower.ιMulti K p f) (exteriorPower.ιMulti K p x) =
      Matrix.det (fun i j => f i (x j))

/-- Elementary values uniquely specify the bilinear pairing on both quotients. -/
def unique_pairing : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (B : (⋀[K]^p (Module.Dual K V)) →ₗ[K] Module.Dual K (⋀[K]^p V)),
    (∀ f x, B (exteriorPower.ιMulti K p f) (exteriorPower.ιMulti K p x) =
      Matrix.det (fun i j => f i (x j))) → B = pairing_value K V p

def dual_basis : Prop :=
  ∀ {K : Type u} {V : Type v} {I : Type w}
    [Field K] [AddCommGroup V] [Module K V] [LinearOrder I] [Finite I]
    (b : Module.Basis I K V) (p : ℕ) (s t : Set.powersetCard I p),
    pairing_value K V p (ExteriorBasis.increasingWedge b.dualBasis p s)
      (ExteriorBasis.increasingWedge b p t) = if s = t then 1 else 0

def perfect : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (p : ℕ),
    ∃ e : (⋀[K]^p (Module.Dual K V)) ≃ₗ[K] Module.Dual K (⋀[K]^p V),
      e.toLinearMap = pairing_value K V p

/-- Naturality holds even before imposing finite dimension. -/
def naturality : Prop :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p : ℕ) (T : V →ₗ[K] W) (a : ⋀[K]^p (Module.Dual K W)) (x : ⋀[K]^p V),
    pairing_value K V p (WedgeSign.powerMap_value p T.dualMap a) x =
      pairing_value K W p a (WedgeSign.powerMap_value p T x)

def degree_zero : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (a b : K),
    pairing_value K V 0 ((exteriorPower.zeroEquiv K (Module.Dual K V)).symm a)
      ((exteriorPower.zeroEquiv K V).symm b) = a * b

def tensor_elementary : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (f : Fin p → Module.Dual K V) (x : Fin p → V),
    tensorEvaluation_value K V p (PiTensorProduct.tprod K f) (PiTensorProduct.tprod K x) =
      ∏ i, f i (x i)

def average_elementary : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (x : Fin p → V),
    average_value K V p (PiTensorProduct.tprod K x) =
      (Nat.factorial p : K)⁻¹ • ∑ σ : Equiv.Perm (Fin p),
        Equiv.Perm.sign σ • PiTensorProduct.tprod K (x ∘ σ.symm)

/-- The double average has exactly one inverse factorial, rather than two. -/
def average_pairing : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ), (Nat.factorial p : K) ≠ 0 →
    ∀ (f : Fin p → Module.Dual K V) (x : Fin p → V),
    tensorEvaluation_value K V p
      (average_value K (Module.Dual K V) p (PiTensorProduct.tprod K f))
      (average_value K V p (PiTensorProduct.tprod K x)) =
      Matrix.det (fun i j => f i (x j)) / (Nat.factorial p : K)

/-- Comparison on arbitrary exterior elements, with the same normalization. -/
def normalized_tensor_comparison : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ), (Nat.factorial p : K) ≠ 0 →
    ∀ (a : ⋀[K]^p (Module.Dual K V)) (x : ⋀[K]^p V),
    pairing_value K V p a x = (Nat.factorial p : K) *
      tensorEvaluation_value K V p
        ((Nat.factorial p : K)⁻¹ • exteriorPower.toTensorPower K (Module.Dual K V) p a)
        ((Nat.factorial p : K)⁻¹ • exteriorPower.toTensorPower K V p x)

end Specs.D05.M15.ExteriorPairing
