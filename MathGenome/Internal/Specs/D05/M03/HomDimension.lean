import MathGenome.Internal.Specs.D05.M02.Dimension
import MathGenome.Internal.Specs.D05.M03.BasisExtension

/-! Independent statements for K05.03.hom_dimension (paper.tex:608–614).
Rows index the target basis, columns index the source basis. The given finite
bases supply all finiteness hypotheses; neither length is required positive.
-/

namespace Specs.D05.M03.HomDimension

open scoped BigOperators

/-- The elementary map is the source coordinate functional times a target vector. -/
noncomputable def elementaryMap {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {n m : ℕ} (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (i : Fin m) (j : Fin n) : V →ₗ[K] W :=
  (b.coord j).smulRight (c i)

def elementary_map_apply : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (i : Fin m) (j k : Fin n),
    elementaryMap b c i j (b k) = if j = k then c i else 0

def elementary_map_exists_unique : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (i : Fin m) (j : Fin n),
    ∃! E : V →ₗ[K] W, ∀ k, E (b k) = if j = k then c i else 0

/-- An actual basis with exactly the prescribed elementary maps as its vectors. -/
def elementary_maps_basis : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W),
    ∃ B : Module.Basis (Fin m × Fin n) K (V →ₗ[K] W),
      ∀ p, B p = elementaryMap b c p.1 p.2

/-- The coefficient in row i, column j is the i-coordinate of T(b j). -/
def linear_map_expansion : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (T : V →ₗ[K] W),
    T = ∑ i : Fin m, ∑ j : Fin n,
      c.repr (T (b j)) i • elementaryMap b c i j

/-- The elementary maps are independent, stated in the source's coefficient form. -/
def zero_relation_iff : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (a : Fin m → Fin n → K),
    (∑ i : Fin m, ∑ j : Fin n, a i j • elementaryMap b c i j) = 0 ↔
      ∀ i j, a i j = 0

def hom_dimension : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W),
    Module.finrank K (V →ₗ[K] W) = m * n

/-- In either empty shape all maps vanish; the basis above has empty index type. -/
def empty_shape_zero : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W),
    n = 0 ∨ m = 0 → ∀ T : V →ₗ[K] W, T = 0

end Specs.D05.M03.HomDimension
