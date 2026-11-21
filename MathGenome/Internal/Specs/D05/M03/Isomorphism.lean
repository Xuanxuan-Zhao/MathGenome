import MathGenome.Internal.Specs.D05.M03.InjectiveSurjective
import MathGenome.Internal.Specs.D05.M02.Basis

/-!
Independent statements for K05.03.isomorphism (paper.tex:571–572).

Isomorphisms are the canonical `LinearEquiv`s over the common field. The
bridge below identifies these with precisely the bijective linear maps;
linearity of an inverse is a conclusion, not an additional hypothesis.
Composition `S.comp T` means first `T`, then `S`, as in the source's `ST`.
All spaces and basis index types are arbitrary, including zero spaces and
empty or infinite index types. No finite-dimensional hypothesis is used.
-/

namespace Specs.D05.M03.Isomorphism

universe u v w

/-- The type of the canonical linear-isomorphism constructor. -/
def isomorphism_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  (K : Type u) → (V : Type v) → (W : Type w) → [Field K] →
    [AddCommGroup V] → [Module K V] → [AddCommGroup W] → [Module K W] →
      Type (max v w)

/-- Reuse Mathlib's linear equivalences, with the same scalar field on both sides. -/
def isomorphism_value : isomorphism_type.{u, v, w} :=
  fun K V W _ _ _ _ _ => V ≃ₗ[K] W

/-- A linear map underlies an isomorphism exactly when it is bijective. -/
def isomorphism_iff_bijective : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    (∃ e : V ≃ₗ[K] W, e.toLinearMap = T) ↔ Function.Bijective T

/-- A bijective linear map has a unique two-sided inverse among linear maps. -/
def inverse_of_bijective : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    Function.Bijective T → ∃! S : W →ₗ[K] V,
      S.comp T = LinearMap.id ∧ T.comp S = LinearMap.id

/-- The source's explicit two-term linearity formula for the inverse. -/
def inverse_linear_combination : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V ≃ₗ[K] W)
    (a b : K) (y z : W),
    T.symm (a • y + b • z) = a • T.symm y + b • T.symm z

/-- The identity linear map is an isomorphism. -/
def identity_isomorphism : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    ∃ e : V ≃ₗ[K] V, e.toLinearMap = LinearMap.id

/-- Composites of bijective linear maps are isomorphisms. -/
def composition_isomorphism : Prop :=
  ∀ {K V W U : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    (T : V →ₗ[K] W) (S : W →ₗ[K] U),
    Function.Bijective T → Function.Bijective S →
      ∃ e : V ≃ₗ[K] U, e.toLinearMap = S.comp T

/-- The bundled inverse has the two required composition identities. -/
def inverse_laws : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V ≃ₗ[K] W),
    T.symm.toLinearMap.comp T.toLinearMap = LinearMap.id ∧
      T.toLinearMap.comp T.symm.toLinearMap = LinearMap.id

/-- The inverse of the identity is the identity. -/
def inverse_identity : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    (LinearEquiv.refl K V).symm = LinearEquiv.refl K V

/-- Inverses reverse composition: `(ST)⁻¹ = T⁻¹S⁻¹`. -/
def inverse_composition : Prop :=
  ∀ {K V W U : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    (T : V ≃ₗ[K] W) (S : W ≃ₗ[K] U),
    (T.trans S).symm = S.symm.trans T.symm

/-- The image basis retains exactly the original index set and image vectors. -/
def map_basis : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V ≃ₗ[K] W)
    (b : Module.Basis I K V),
    ∃ c : Module.Basis I K W, ∀ i, c i = T (b i)

/-- In particular, the indexed image family is independent and spans the codomain. -/
def map_basis_independent_span : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V ≃ₗ[K] W)
    (b : Module.Basis I K V),
    LinearIndependent K (fun i => T (b i)) ∧
      Submodule.span K (Set.range (fun i => T (b i))) = ⊤

end Specs.D05.M03.Isomorphism
