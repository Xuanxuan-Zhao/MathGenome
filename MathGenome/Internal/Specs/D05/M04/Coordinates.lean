import Mathlib.LinearAlgebra.Basis.Defs
import MathGenome.Internal.Specs.D05.M02.Basis
import MathGenome.Internal.Specs.D05.M03.Isomorphism

/-!
Independent specification for K05.04.coordinates (paper.tex:622–623).
An ordered basis has index type `Fin n`, and a column is the function `Fin n → K`.
The coordinate map is the canonical finite-basis linear equivalence, using the
same basis and field as the accepted foundation. Its inverse is specified by
an explicit finite sum. No positivity of `n` is assumed. Reindexing uses
`b.reindex σ`, whose vector at `j` is `b (σ.symm j)`.
-/

namespace Specs.D05.M04.Coordinates

universe u v

/-- Type of the coordinate isomorphism attached to a finite ordered basis. -/
def coordinates_type : Type (max (u + 1) (v + 1)) :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] → [Module K V] →
    {n : ℕ} → Module.Basis (Fin n) K V → (V ≃ₗ[K] (Fin n → K))

/-- The canonical representation: the finite basis's `repr`, viewed as a column. -/
noncomputable def coordinates_value : coordinates_type.{u, v} :=
  fun b => b.equivFun

/-- The coordinate at each position is the unique basis coefficient. -/
def coordinates_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x : V) (j : Fin n),
    coordinates_value b x j = b.repr x j

/-- Coordinates add componentwise. -/
def coordinates_add : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x y : V),
    coordinates_value b (x + y) = coordinates_value b x + coordinates_value b y

/-- Coordinates scale componentwise. -/
def coordinates_smul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (a : K) (x : V),
    coordinates_value b (a • x) = a • coordinates_value b x

/-- The coordinate column of the stated expansion is exactly its coefficient column. -/
def coordinates_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x : Fin n → K),
    coordinates_value b (∑ j, x j • b j) = x

/-- Reconstruct a vector from its column coordinates. -/
def reconstruction : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x : V),
    (∑ j, coordinates_value b x j • b j) = x

/-- The inverse is precisely the finite-sum map in the paper. -/
def inverse_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x : Fin n → K),
    (coordinates_value b).symm x = ∑ j, x j • b j

/-- The inverse adds and scales columns linearly. -/
def inverse_linear_combination : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (a c : K) (x y : Fin n → K),
    (coordinates_value b).symm (a • x + c • y) =
      a • (coordinates_value b).symm x + c • (coordinates_value b).symm y

/-- The coordinate and reconstruction linear maps are inverse in both directions. -/
def inverse_laws : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V),
    (coordinates_value b).symm.toLinearMap.comp (coordinates_value b).toLinearMap =
      LinearMap.id ∧
    (coordinates_value b).toLinearMap.comp (coordinates_value b).symm.toLinearMap =
      LinearMap.id

/-- The sum formula has exactly one column for every vector. -/
def unique_coordinates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (v : V),
    ∃! x : Fin n → K, (∑ j, x j • b j) = v

/-- Reordering basis positions permutes coordinates by the same inverse-index rule. -/
def reindex_coordinates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (σ : Equiv.Perm (Fin n)) (x : V) (j : Fin n),
    coordinates_value (b.reindex σ) x j = coordinates_value b x (σ.symm j)

/-- The empty ordered basis describes the zero space; its expansion is the empty sum. -/
def empty_basis_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis (Fin 0) K V) (x : V), x = 0

end Specs.D05.M04.Coordinates
