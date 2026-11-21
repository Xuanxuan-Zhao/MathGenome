import MathGenome.Internal.Specs.D05.M11.Bilinear
import MathGenome.Internal.Specs.D05.M15.TensorUniversal
import MathGenome.Internal.Specs.D05.M15.TensorKernel
import MathGenome.Internal.Specs.D05.M15.TensorPairing
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! Independent statements for paper.tex:2861–2872, general bilinear tensor
pairings. Pairings need not be symmetric or positive. Construction and uniqueness
allow arbitrary dimension. The radical and perfection assertions below use finite
dimension, and converse separation assertions retain the nonzero-side guards.
Radicals are the kernels of the actual maps into algebraic duals. Tensor subspaces
are embedded by their natural maps, and their sum is the submodule supremum. -/
namespace Specs.D05.M15.InnerTensor.BilinearMetrics

open scoped TensorProduct
universe u v w v' w'

/-- The canonical pairing obtained by tensoring the maps into the two duals,
then evaluating dual tensors. This uses only tensor universal constructions. -/
def tensorPairing {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K) :
    (V ⊗[K] W) →ₗ[K] (V' ⊗[K] W') →ₗ[K] K :=
  (TensorProduct.dualDistrib K V' W').comp (TensorProduct.map b c)

def tensorPairing_type :=
  {K : Type u} → {V : Type v} → {W : Type w} → {V' : Type v'} → {W' : Type w'} →
  [Field K] → [AddCommGroup V] → [Module K V] → [AddCommGroup W] → [Module K W] →
  [AddCommGroup V'] → [Module K V'] → [AddCommGroup W'] → [Module K W'] →
  (V →ₗ[K] V' →ₗ[K] K) → (W →ₗ[K] W' →ₗ[K] K) →
  (V ⊗[K] W) →ₗ[K] (V' ⊗[K] W') →ₗ[K] K

def tensorPairing_value : tensorPairing_type.{u,v,w,v',w'} := @tensorPairing

def tensorPairing_apply : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K) v w v' w',
    tensorPairing b c (v ⊗ₜ[K] w) (v' ⊗ₜ[K] w') = b v v' * c w w'

def tensorPairing_unique : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K)
    (P : (V ⊗[K] W) →ₗ[K] (V' ⊗[K] W') →ₗ[K] K),
    (∀ v w v' w', P (v ⊗ₜ[K] w) (v' ⊗ₜ[K] w') = b v v' * c w w') →
    P = tensorPairing b c

def tensorPairing_exists_unique : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K),
    ∃! P : (V ⊗[K] W) →ₗ[K] (V' ⊗[K] W') →ₗ[K] K,
      ∀ v w v' w', P (v ⊗ₜ[K] w) (v' ⊗ₜ[K] w') = b v v' * c w w'

def tensorPairing_flip : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K),
    (tensorPairing b c).flip = tensorPairing b.flip c.flip

/-- These membership formulas identify the kernels with the source radicals. -/
def left_radical_membership : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K) z,
    z ∈ (tensorPairing b c).ker ↔ ∀ z', tensorPairing b c z z' = 0

def right_radical_membership : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K) z',
    z' ∈ (tensorPairing b c).flip.ker ↔ ∀ z, tensorPairing b c z z' = 0

def left_radical : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K),
    (tensorPairing b c).ker =
      (TensorProduct.map b.ker.subtype (LinearMap.id : W →ₗ[K] W)).range ⊔
      (TensorProduct.map (LinearMap.id : V →ₗ[K] V) c.ker.subtype).range

def right_radical : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K),
    (tensorPairing b c).flip.ker =
      (TensorProduct.map b.flip.ker.subtype (LinearMap.id : W' →ₗ[K] W')).range ⊔
      (TensorProduct.map (LinearMap.id : V' →ₗ[K] V') c.flip.ker.subtype).range

def perfect_tensorPairing : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K),
    b.IsPerfPair → c.IsPerfPair → (tensorPairing b c).IsPerfPair

def left_nondegenerate : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K),
    b.SeparatingLeft → c.SeparatingLeft → (tensorPairing b c).SeparatingLeft

def right_nondegenerate : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K),
    b.SeparatingRight → c.SeparatingRight → (tensorPairing b c).SeparatingRight

/-- The forward implication needs nonzero left spaces, not nonzero codomains. -/
def left_nondegenerate_iff : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W']
    [Nontrivial V] [Nontrivial W],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K),
    (tensorPairing b c).SeparatingLeft ↔ b.SeparatingLeft ∧ c.SeparatingLeft

/-- The analogous converse uses nonzero right spaces. -/
def right_nondegenerate_iff : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W']
    [Nontrivial V'] [Nontrivial W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K),
    (tensorPairing b c).SeparatingRight ↔ b.SeparatingRight ∧ c.SeparatingRight

def nondegenerate_tensorPairing : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W'],
  ∀ (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K),
    b.Nondegenerate → c.Nondegenerate → (tensorPairing b c).Nondegenerate

/-- Symmetry is an algebraic property, without a positivity assumption. -/
def symmetric_tensorPairing : Prop :=
  ∀ {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∀ (b : V →ₗ[K] V →ₗ[K] K) (c : W →ₗ[K] W →ₗ[K] K),
    (∀ x y, b x y = b y x) → (∀ x y, c x y = c y x) →
    ∀ z t, tensorPairing b c z t = tensorPairing b c t z

/-- A zero factor makes the tensor form nondegenerate regardless of the other
form, recording why the converse cannot omit its nonzero guard. -/
def zero_factor_nondegenerate : Prop :=
  ∀ {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Subsingleton V],
  ∀ (b : V →ₗ[K] V →ₗ[K] K) (c : W →ₗ[K] W →ₗ[K] K),
    (tensorPairing b c).Nondegenerate

end Specs.D05.M15.InnerTensor.BilinearMetrics
