import MathGenome.Internal.Specs.D05.M03.LinearMap
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.Data.Matrix.Basic

/-!
Independent statements for K05.11.bilinear, paper.tex:1635–1639.

A pairing uses two possibly different vector spaces over the same field. A form
is the same object with its two domains equal. No symmetry, nondegeneracy,
positivity, or characteristic assumption is imposed. The elementary identities
are valid even without finite dimension. The coordinate statements use finite
bases, so in particular cover every finite-dimensional space, including zero.
All sums use indexed families and retain repeated occurrences.
-/

namespace Specs.D05.M11.Bilinear

open Module
open scoped BigOperators

universe u v w i j

/-- Type constructor for bilinear scalar pairings. -/
def bilinearPairing_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  (K : Type u) → (V : Type v) → (W : Type w) → [Field K] →
    [AddCommGroup V] → [Module K V] → [AddCommGroup W] → [Module K W] →
      Type (max u v w)

/-- Currying into the canonical space of linear maps. -/
def bilinearPairing_value : bilinearPairing_type.{u, v, w} :=
  fun K V W _ _ _ _ _ => V →ₗ[K] W →ₗ[K] K

/-- Type constructor for bilinear forms. -/
def bilinearForm_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] →
    [Module K V] → Type (max u v)

/-- A form is precisely a pairing whose domains coincide. -/
def bilinearForm_value : bilinearForm_type.{u, v} :=
  fun K V _ _ _ => LinearMap.BilinForm K V

/-- Exactly the paper's four slotwise linearity identities on the same function. -/
def pairing_iff_axioms : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (b : V → W → K),
    (∃ B : V →ₗ[K] W →ₗ[K] K, ∀ x y, B x y = b x y) ↔
      (∀ x x' y, b (x + x') y = b x y + b x' y) ∧
      (∀ (a : K) x y, b (a • x) y = a * b x y) ∧
      (∀ x y y', b x (y + y') = b x y + b x y') ∧
      (∀ (a : K) x y, b x (a • y) = a * b x y)

/-- Canonical pairing addition, scalar multiplication and zero are pointwise;
these operations already take values in the space of bilinear pairings. -/
def pointwise_operations : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (B C : V →ₗ[K] W →ₗ[K] K)
    (a : K) (x : V) (y : W),
    (B + C) x y = B x y + C x y ∧
    (a • B) x y = a * B x y ∧
    (0 : V →ₗ[K] W →ₗ[K] K) x y = 0

/-- Expansion in each argument for any two finite indexed combinations. -/
def finite_expansion : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (B : V →ₗ[K] W →ₗ[K] K)
    (s : Finset I) (t : Finset J) (x : I → K) (y : J → K)
    (e : I → V) (f : J → W),
    B (∑ a ∈ s, x a • e a) (∑ b ∈ t, y b • f b) =
      ∑ a ∈ s, ∑ b ∈ t, x a * y b * B (e a) (f b)

/-- The displayed formula in basis coordinates, for arbitrary input vectors. -/
def basis_expansion : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype I] [Fintype J]
    (e : Basis I K V) (f : Basis J K W) (B : V →ₗ[K] W →ₗ[K] K)
    (x : V) (y : W),
    B x y = ∑ a, ∑ b, e.repr x a * f.repr y b * B (e a) (f b)

/-- Values on the pairs of basis vectors determine the entire pairing. -/
def basis_ext : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype I] [Fintype J]
    (e : Basis I K V) (f : Basis J K W) (B C : V →ₗ[K] W →ₗ[K] K),
    (∀ a b, B (e a) (f b) = C (e a) (f b)) → B = C

/-- Type of the explicit construction from an arbitrary array of basis values.
No finite-index restriction is needed to construct it: coordinates have finite support. -/
def coordinatePairing_type : Type (max (u + 1) (v + 1) (w + 1) (i + 1) (j + 1)) :=
  {K : Type u} → {V : Type v} → {W : Type w} → {I : Type i} → {J : Type j} →
    [Field K] → [AddCommGroup V] → [Module K V] →
    [AddCommGroup W] → [Module K W] →
    Basis I K V → Basis J K W → Matrix I J K → (V →ₗ[K] W →ₗ[K] K)

/-- Extend in the second slot on each first basis vector, then in the first slot. -/
noncomputable def coordinatePairing_value {K V W I J : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : Basis I K V) (f : Basis J K W) (A : Matrix I J K) :
    V →ₗ[K] W →ₗ[K] K :=
  e.constr K (fun a => f.constr K (fun b => A a b))

/-- The construction really takes the prescribed values. -/
def coordinatePairing_basis : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype I] [Fintype J]
    (e : Basis I K V) (f : Basis J K W) (A : Matrix I J K) (a : I) (b : J),
    coordinatePairing_value e f A (e a) (f b) = A a b

/-- Every array constructs a pairing by the displayed double-sum formula. -/
def coordinatePairing_apply : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype I] [Fintype J]
    (e : Basis I K V) (f : Basis J K W) (A : Matrix I J K) (x : V) (y : W),
    coordinatePairing_value e f A x y =
      ∑ a, ∑ b, e.repr x a * f.repr y b * A a b

/-- Existence and uniqueness for every prescribed array, with no rank or
nondegeneracy condition. The construction is not inferred from dimension counts. -/
def exists_unique_pairing : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype I] [Fintype J]
    (e : Basis I K V) (f : Basis J K W) (A : Matrix I J K),
    ∃! B : V →ₗ[K] W →ₗ[K] K, ∀ a b, B (e a) (f b) = A a b

end Specs.D05.M11.Bilinear
