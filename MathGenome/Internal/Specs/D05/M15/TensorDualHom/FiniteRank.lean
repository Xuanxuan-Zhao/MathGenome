import MathGenome.Internal.Specs.D05.M15.TensorDualHom.CompositionTrace
import MathGenome.Internal.Specs.D05.M02.BasisExtension.Choice

/-!
K05.15.tensor_dual_hom, paper.tex:2814–2816. All vector spaces are
algebraic and may be infinite dimensional. The canonical map is the upstream
`phi`. Finite rank means that its actual image is finite dimensional, with
no finiteness condition on either ambient space. Unrestricted basis choices
use the declared classical basis-extension principle.
-/

namespace Specs.D05.M15.TensorDualHom.FiniteRank

open scoped TensorProduct
open Specs.D05.M15.TensorDualHom (phi)

/-- The intrinsic subspace of finite-rank maps, independent of tensor notation. -/
def finiteRankMaps (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] : Submodule K (V →ₗ[K] W) where
  carrier := {T | FiniteDimensional K T.range}
  zero_mem' := by
    rw [Set.mem_ofPred_eq, LinearMap.range_zero]
    infer_instance
  add_mem' := by
    intro f g hf hg
    letI : FiniteDimensional K f.range := hf
    letI : FiniteDimensional K g.range := hg
    exact FiniteDimensional.of_injective
      (Submodule.inclusion (LinearMap.range_add_le f g))
      (Submodule.inclusion_injective _)
  smul_mem' := by
    intro c f hf
    letI : FiniteDimensional K f.range := hf
    exact FiniteDimensional.of_injective
      (Submodule.inclusion (LinearMap.range_smul_le_range f c))
      (Submodule.inclusion_injective _)

def finiteRankMaps_type :=
  (K V W : Type*) → [Field K] → [AddCommGroup V] → [Module K V] →
    [AddCommGroup W] → [Module K W] → Submodule K (V →ₗ[K] W)

def finiteRankMaps_value : finiteRankMaps_type := @finiteRankMaps

/-- Postcomposition on the vector factor defines the unrestricted bilinear
composition product. In finite dimension it must agree with the upstream one. -/
def compositionProduct (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    (Module.Dual K V ⊗[K] V) →ₗ[K]
      (Module.Dual K V ⊗[K] V) →ₗ[K] (Module.Dual K V ⊗[K] V) :=
  (LinearMap.lTensorHom (Module.Dual K V)).comp (phi K V V)

def compositionProduct_type :=
  (K V : Type*) → [Field K] → [AddCommGroup V] → [Module K V] →
    (Module.Dual K V ⊗[K] V) →ₗ[K]
      (Module.Dual K V ⊗[K] V) →ₗ[K] (Module.Dual K V ⊗[K] V)

def compositionProduct_value : compositionProduct_type := @compositionProduct

/-- No finite-dimensional assumption is needed for injectivity. -/
def phi_injective : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W], Function.Injective (phi K V W)

/-- This is both directions of the precise image assertion. -/
def mem_range_iff : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    T ∈ LinearMap.range (phi K V W) ↔ FiniteDimensional K T.range

/-- The identification is a linear equivalence with the intrinsic subspace;
its forward map is exactly the canonical map on every tensor. -/
def finite_rank_equivalence : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    ∃ E : (Module.Dual K V ⊗[K] W) ≃ₗ[K] finiteRankMaps K V W,
      ∀ t, (E t : V →ₗ[K] W) = phi K V W t

def product_tmul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : Module.Dual K V) (v w : V),
    compositionProduct K V (f ⊗ₜ[K] v) (g ⊗ₜ[K] w) = (f w • g) ⊗ₜ[K] v

def phi_product : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (s t : Module.Dual K V ⊗[K] V),
    phi K V V (compositionProduct K V s t) = (phi K V V s).comp (phi K V V t)

def product_assoc : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (r s t : Module.Dual K V ⊗[K] V),
    compositionProduct K V (compositionProduct K V r s) t =
      compositionProduct K V r (compositionProduct K V s t)

def product_agrees_finite : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    compositionProduct K V = CompositionTrace.compositionProduct K V

/-- A tensor is a two-sided identity exactly when Phi sends it to the identity
operator. This rules out even an identity internal to the finite-rank algebra. -/
def unit_iff_identity : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e : Module.Dual K V ⊗[K] V),
    (∀ t, compositionProduct K V e t = t ∧ compositionProduct K V t e = t) ↔
      phi K V V e = LinearMap.id

def identity_infinite_rank : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    ¬ FiniteDimensional K V →
      ¬ FiniteDimensional K (LinearMap.range (LinearMap.id : V →ₗ[K] V))

/-- Infinite dimension already excludes the zero space. -/
def no_unit : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    ¬ FiniteDimensional K V →
      ¬ ∃ e : Module.Dual K V ⊗[K] V,
        ∀ t, compositionProduct K V e t = t ∧ compositionProduct K V t e = t

end Specs.D05.M15.TensorDualHom.FiniteRank
