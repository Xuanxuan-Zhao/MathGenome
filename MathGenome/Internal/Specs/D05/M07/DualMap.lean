import MathGenome.Internal.Specs.D05.M07.Dual

/-!
Independent specifications for K05.07.dual_map (paper.tex:1037–1042).
The dual is the algebraic `Module.Dual`, with the same field on every space.
Precomposition is linear in the functional and in the original map. There are
no dimension, topology, inner-product, or characteristic assumptions.
-/

namespace Specs.D05.M07.DualMap

universe u v w

/-- A map to the linear maps between the algebraic duals, reversing their order. -/
def dualMap_type :=
  {K : Type u} → {V : Type v} → {W : Type w} → [Field K] →
    [AddCommGroup V] → [Module K V] → [AddCommGroup W] → [Module K W] →
    (V →ₗ[K] W) → (Module.Dual K W →ₗ[K] Module.Dual K V)

/-- The canonical algebraic transpose, defined by ordinary precomposition. -/
def dualMap_value : dualMap_type.{u, v, w} :=
  fun {_ _ _} _ _ _ _ _ T => T.dualMap

/-- Its output is exactly composition of bundled linear maps. -/
def dualMap_apply : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) (f : Module.Dual K W),
    T.dualMap f = f.comp T

/-- In particular its value on a vector is the paper's defining formula. -/
def dualMap_apply_apply : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) (f : Module.Dual K W) (v : V),
    T.dualMap f v = f (T v)

/-- Linearity in the functional: addition. -/
def map_add : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) (f g : Module.Dual K W),
    T.dualMap (f + g) = T.dualMap f + T.dualMap g

/-- Linearity in the functional: scalar multiplication over the same field. -/
def map_smul : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) (a : K) (f : Module.Dual K W),
    T.dualMap (a • f) = a • T.dualMap f

/-- Composition reverses, for arbitrary composable maps. -/
def dualMap_comp : Prop :=
  ∀ {K V W X : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
    (S : W →ₗ[K] X) (T : V →ₗ[K] W),
    (S.comp T).dualMap = T.dualMap.comp S.dualMap

def dualMap_id : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    (LinearMap.id : V →ₗ[K] V).dualMap =
      (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V)

/-- Additivity in the original map with fixed source and target. -/
def dualMap_add : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (S T : V →ₗ[K] W),
    (S + T).dualMap = S.dualMap + T.dualMap

/-- Scalar linearity in the original map; there is no scalar conjugation. -/
def dualMap_smul : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (a : K) (T : V →ₗ[K] W),
    (a • T).dualMap = a • T.dualMap

/-- The full two-scalar identity stated in the paper. -/
def dualMap_linear_combination : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (a b : K) (S T : V →ₗ[K] W),
    (a • S + b • T).dualMap = a • S.dualMap + b • T.dualMap

/-- Over ℂ the scalar is still the original scalar, not its conjugate. -/
def complex_no_conjugation : Prop :=
  ∀ {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (a : ℂ) (T : V →ₗ[ℂ] W)
    (f : Module.Dual ℂ W) (v : V),
    (a • T).dualMap f v = a * f (T v)

end Specs.D05.M07.DualMap
