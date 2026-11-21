import MathGenome.Internal.Specs.D05.M02.Dimension
import MathGenome.Internal.Specs.D05.M03.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Span.Basic

/-!
Independent statements for K05.03.image (paper.tex:550–551).

The image is the canonical submodule `LinearMap.range`, with carrier precisely
the set of values of the map. Spanning is stated for arbitrary indexed families;
no finiteness of the index type, domain, or codomain is required. Both the ambient
span equality and the span inside the image subtype are recorded.

The natural-number rank is defined only with a finite-dimensional image. Neither
the domain nor the whole codomain is required to be finite-dimensional, and the
dimension is that of the image subtype, not the codomain.
-/

namespace Specs.D05.M03.Image

universe u v w

def image_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  (K : Type u) → (V : Type v) → (W : Type w) → [Field K] →
    [AddCommGroup V] → [Module K V] → [AddCommGroup W] → [Module K W] →
      (V →ₗ[K] W) → Submodule K W

/-- The paper's image with its vector-subspace structure. -/
def image_value : image_type.{u, v, w} :=
  fun K V W _ _ _ _ _ T => LinearMap.range T

/-- Exact membership in the set of values, with no dimension hypotheses. -/
def mem_image : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) (y : W),
    y ∈ LinearMap.range T ↔ ∃ x : V, T x = y

def zero_mem_image : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    (0 : W) ∈ LinearMap.range T

/-- The identity used in the source to prove closure of the image. -/
def map_linear_combination : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) (a b : K) (x z : V),
    a • T x + b • T z = T (a • x + b • z)

def image_closed_combination : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) (a b : K) (y z : W),
    y ∈ LinearMap.range T → z ∈ LinearMap.range T →
      a • y + b • z ∈ LinearMap.range T

/-- The exact set in the source is the carrier of a subspace of the codomain. -/
def image_subspace : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    ∃ U : Submodule K W, (U : Set W) = {y | ∃ x : V, T x = y}

/-- Images of a spanning family span precisely the image in the ambient space. -/
def span_image_eq : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) (v : I → V),
    Submodule.span K (Set.range v) = ⊤ →
      Submodule.span K (Set.range (fun i => T (v i))) = LinearMap.range T

/-- The same spanning statement with vectors regarded as elements of the image. -/
def span_image_subtype_eq : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) (v : I → V),
    Submodule.span K (Set.range v) = ⊤ →
      Submodule.span K (Set.range (fun i =>
        (⟨T (v i), LinearMap.mem_range_self T (v i)⟩ : LinearMap.range T))) = ⊤

def rank_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  (K : Type u) → (V : Type v) → (W : Type w) → [Field K] →
    [AddCommGroup V] → [Module K V] → [AddCommGroup W] → [Module K W] →
      (T : V →ₗ[K] W) → [FiniteDimensional K (LinearMap.range T)] → ℕ

/-- Rank is the dimension of the finite-dimensional image, even in a larger codomain. -/
noncomputable def rank_value : rank_type.{u, v, w} :=
  fun K V W _ _ _ _ _ T _ => Module.finrank K (LinearMap.range T)

/-- The rank equals the length of any finite basis of the image, including an empty one. -/
def rank_eq_card_image_basis : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W)
    [FiniteDimensional K (LinearMap.range T)] [Fintype I]
    (b : Module.Basis I K (LinearMap.range T)),
    rank_value K V W T = Fintype.card I

end Specs.D05.M03.Image
