import MathGenome.Internal.Specs.D05.M15.PermutationActions
import MathGenome.Internal.Specs.D05.Foundations.PermutationSign

/-!
Independent specifications for K05.15.symmetrizers (paper.tex:2897–2907).
The tensor power and inverse-index permutation convention are the upstream ones.
No dimension restriction is imposed. The normalization is defined only with a
proof that the factorial is nonzero, equivalently invertible in the field.
Alternating bilinear maps mean repeated-input vanishing, in every characteristic.
-/

noncomputable section
namespace Specs.D05.M15.Symmetrizers

universe u v w
open D05.Foundations
open Specs.D05.M15.PermutationActions

abbrev TensorPower (K : Type u) (V : Type v) [Field K] [AddCommGroup V]
    [Module K V] (p : ℕ) := PiTensorProduct K (fun _ : Fin p => V)

variable {K : Type u} {V : Type v} {W : Type w}
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def IsInvariant (p : ℕ) (t : TensorPower K V p) : Prop :=
  ∀ σ : Equiv.Perm (Fin p), permutationOperator p σ t = t

def IsSignInvariant (p : ℕ) (t : TensorPower K V p) : Prop :=
  ∀ σ : Equiv.Perm (Fin p), permutationOperator p σ t = (permutationSign σ : K) • t

def symmetricProjector (p : ℕ) (_hp : (p.factorial : K) ≠ 0) :
    TensorPower K V p →ₗ[K] TensorPower K V p :=
  (p.factorial : K)⁻¹ • ∑ σ : Equiv.Perm (Fin p), permutationOperator p σ

def alternatingProjector (p : ℕ) (_hp : (p.factorial : K) ≠ 0) :
    TensorPower K V p →ₗ[K] TensorPower K V p :=
  (p.factorial : K)⁻¹ • ∑ σ : Equiv.Perm (Fin p),
    (permutationSign σ : K) • permutationOperator p σ

def IsSymmetric (b : V →ₗ[K] V →ₗ[K] W) : Prop := ∀ u v, b u v = b v u

def IsAlternating (b : V →ₗ[K] V →ₗ[K] W) : Prop := ∀ v, b v v = 0

def symmetricPart (_h2 : (2 : K) ≠ 0) (b : V →ₗ[K] V →ₗ[K] W) :=
  (2 : K)⁻¹ • (b + b.flip)

def alternatingPart (_h2 : (2 : K) ≠ 0) (b : V →ₗ[K] V →ₗ[K] W) :=
  (2 : K)⁻¹ • (b - b.flip)

def symmetricProjector_type :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ), (p.factorial : K) ≠ 0 →
      (TensorPower K V p →ₗ[K] TensorPower K V p)
def symmetricProjector_value : symmetricProjector_type.{u,v} := @symmetricProjector

def alternatingProjector_type := symmetricProjector_type.{u,v}
def alternatingProjector_value : alternatingProjector_type.{u,v} := @alternatingProjector

def symmetricPart_type :=
  ∀ {K : Type u} {V : Type v} {W : Type w} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    (2 : K) ≠ 0 → (V →ₗ[K] V →ₗ[K] W) → (V →ₗ[K] V →ₗ[K] W)
def symmetricPart_value : symmetricPart_type.{u,v,w} := @symmetricPart

def alternatingPart_type := symmetricPart_type.{u,v,w}
def alternatingPart_value : alternatingPart_type.{u,v,w} := @alternatingPart

def symmetrizer_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (hp : (p.factorial : K) ≠ 0) (τ : Equiv.Perm (Fin p)),
    (permutationOperator (K := K) (V := V) p τ).comp (symmetricProjector p hp) =
      symmetricProjector p hp

def antisymmetrizer_covariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (hp : (p.factorial : K) ≠ 0) (τ : Equiv.Perm (Fin p)),
    (permutationOperator (K := K) (V := V) p τ).comp (alternatingProjector p hp) =
      (permutationSign τ : K) • alternatingProjector p hp

def symmetrizer_fixed : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (hp : (p.factorial : K) ≠ 0) (t : TensorPower K V p),
    IsInvariant p t → symmetricProjector p hp t = t

def antisymmetrizer_fixed : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (hp : (p.factorial : K) ≠ 0) (t : TensorPower K V p),
    IsSignInvariant p t → alternatingProjector p hp t = t

def projectors_idempotent : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (hp : (p.factorial : K) ≠ 0),
    (symmetricProjector (V := V) p hp).comp (symmetricProjector p hp) =
      symmetricProjector p hp ∧
    (alternatingProjector (V := V) p hp).comp (alternatingProjector p hp) =
      alternatingProjector p hp

def projector_images : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (hp : (p.factorial : K) ≠ 0) (t : TensorPower K V p),
    (t ∈ LinearMap.range (symmetricProjector p hp) ↔ IsInvariant p t) ∧
    (t ∈ LinearMap.range (alternatingProjector p hp) ↔ IsSignInvariant p t)

def low_degrees : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ), p ≤ 1 → ∀ hp : (p.factorial : K) ≠ 0,
    symmetricProjector (V := V) p hp = LinearMap.id ∧
    alternatingProjector (V := V) p hp = LinearMap.id

/-- In particular, no inverse-factorial projector is provided in this case. -/
def vanishing_factorial : Prop :=
  ∀ {K : Type*} [Field K] (p : ℕ), (p.factorial : K) = 0 →
    ¬ IsUnit (p.factorial : K)

def bilinear_parts : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (h2 : (2 : K) ≠ 0)
    (b : V →ₗ[K] V →ₗ[K] W),
    IsSymmetric (symmetricPart h2 b) ∧ IsAlternating (alternatingPart h2 b) ∧
      symmetricPart h2 b + alternatingPart h2 b = b

def bilinear_intersection_zero : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W], (2 : K) ≠ 0 →
    ∀ b : V →ₗ[K] V →ₗ[K] W, IsSymmetric b → IsAlternating b → b = 0

def bilinear_decomposition_unique : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (h2 : (2 : K) ≠ 0)
    (b s a : V →ₗ[K] V →ₗ[K] W),
    IsSymmetric s → IsAlternating a → s + a = b →
      s = symmetricPart h2 b ∧ a = alternatingPart h2 b

def tensor_intersection_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ), 2 ≤ p → (2 : K) ≠ 0 → ∀ t : TensorPower K V p,
    IsInvariant p t → IsSignInvariant p t → t = 0

end Specs.D05.M15.Symmetrizers
