import MathGenome.Internal.Specs.D05.M03.LinearMap
import Mathlib.Algebra.Algebra.Basic

/-!
Independent specifications for K05.03.map_algebra (paper.tex:536–537).
All spaces use the same field; no finite-dimensional or nonzero-space premise
is imposed. Hom operations and End multiplication are the canonical Mathlib
operations. The last statement retains all values in the paper's example on K²,
represented by the standard coordinate product K × K.
-/

namespace Specs.D05.M03.MapAlgebra

universe u v w

/-- The canonical vector-space structure on the existing type of linear maps. -/
def homModule_type :=
  (K : Type u) → (V : Type v) → (W : Type w) → [Field K] →
    [AddCommGroup V] → [Module K V] → [AddCommGroup W] → [Module K W] →
      Module K (V →ₗ[K] W)

def homModule_value : homModule_type.{u, v, w} :=
  fun K V W _ _ _ _ _ => (inferInstance : Module K (V →ₗ[K] W))

/-- The ring structure with the existing pointwise addition and composition. -/
def endomorphismRing_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Ring (Module.End K V)

def endomorphismRing_value : endomorphismRing_type.{u, v} :=
  fun K V _ _ _ => (inferInstance : Ring (Module.End K V))

/-- The canonical unital algebra, whose scalars act pointwise. -/
def endomorphismAlgebra_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Algebra K (Module.End K V)

def endomorphismAlgebra_value : endomorphismAlgebra_type.{u, v} :=
  fun K V _ _ _ => (inferInstance : Algebra K (Module.End K V))

def add_apply : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    ∀ (S T : V →ₗ[K] W) (v : V), (S + T) v = S v + T v

def smul_apply : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    ∀ (a : K) (T : V →ₗ[K] W) (v : V), (a • T) v = a • T v

def zero_apply : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    ∀ v : V, (0 : V →ₗ[K] W) v = 0

def neg_apply : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    ∀ (T : V →ₗ[K] W) (v : V), (-T) v = -(T v)

def comp_apply : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    ∀ (S : V →ₗ[K] W) (T : U →ₗ[K] V) (u : U), S.comp T u = S (T u)

def comp_assoc : Prop :=
  ∀ {K U V W X : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup X] [Module K X],
    ∀ (R : W →ₗ[K] X) (S : V →ₗ[K] W) (T : U →ₗ[K] V),
      (R.comp S).comp T = R.comp (S.comp T)

def comp_add : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    ∀ (R : V →ₗ[K] W) (S T : U →ₗ[K] V),
      R.comp (S + T) = R.comp S + R.comp T

def add_comp : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    ∀ (R S : V →ₗ[K] W) (T : U →ₗ[K] V),
      (R + S).comp T = R.comp T + S.comp T

def comp_smul : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    ∀ (R : V →ₗ[K] W) (a : K) (T : U →ₗ[K] V),
      R.comp (a • T) = a • R.comp T

def smul_comp : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
    ∀ (a : K) (R : V →ₗ[K] W) (T : U →ₗ[K] V),
      (a • R).comp T = a • R.comp T

def comp_id : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    ∀ T : V →ₗ[K] W, T.comp (LinearMap.id : V →ₗ[K] V) = T

def id_comp : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    ∀ T : V →ₗ[K] W, (LinearMap.id : W →ₗ[K] W).comp T = T

def end_mul_eq_comp : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    ∀ S T : Module.End K V, S * T = S.comp T

def end_one_eq_id : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    (1 : Module.End K V) = LinearMap.id

def end_algebraMap_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    ∀ (a : K) (v : V), algebraMap K (Module.End K V) a v = a • v

def noncommuting_example : Prop :=
  ∀ (K : Type*) [Field K],
    ∃ S T : Module.End K (K × K),
      S (1, 0) = (0, 1) ∧ S (0, 1) = 0 ∧
      T (1, 0) = (1, 0) ∧ T (0, 1) = 0 ∧
      (S * T) (1, 0) = (0, 1) ∧ (T * S) (1, 0) = 0 ∧ S * T ≠ T * S

end Specs.D05.M03.MapAlgebra
