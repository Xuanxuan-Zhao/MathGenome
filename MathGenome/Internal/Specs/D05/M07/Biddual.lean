import MathGenome.Internal.Specs.D05.M07.DualBasis
import MathGenome.Internal.Specs.D05.M03.EqualDimension

/-!
Independent specifications for K05.07.biddual, paper.tex:1066–1075.
All duals are algebraic `Hom_K(-, K)`, with no topology or conjugation.
Evaluation and naturality require no finite dimension. Bijectivity and the
canonical isomorphism assume finite dimension only of V, including dimension
zero. The unrestricted injectivity statement is the separate choice-based
variant from the source, and asserts no surjectivity.
-/

namespace Specs.D05.M07.Biddual

universe u v

/-- Type of the canonical linear evaluation map for arbitrary vector spaces. -/
def evaluation_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    V →ₗ[K] Module.Dual K (Module.Dual K V)

/-- Evaluation uses the original vector as the argument of each functional. -/
def evaluation_value : evaluation_type.{u, v} :=
  fun K V _ _ _ => Module.Dual.eval K V

/-- The defining equation fixes the map without choosing a basis. -/
def evaluation_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (x : V) (f : Module.Dual K V), Module.Dual.eval K V x f = f x

/-- No other linear map can have the same evaluation formula. -/
def evaluation_unique : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (J : V →ₗ[K] Module.Dual K (Module.Dual K V)),
    (∀ x f, J x f = f x) → J = Module.Dual.eval K V

/-- Finite coordinates separate vectors. -/
def evaluation_injective_finite : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], Function.Injective (Module.Dual.eval K V)

/-- Apply finite duality twice; bidual finiteness is a conclusion. -/
def biddual_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    FiniteDimensional K (Module.Dual K (Module.Dual K V)) ∧
      Module.finrank K (Module.Dual K (Module.Dual K V)) = Module.finrank K V

/-- The paper's explicit preimage works for every finite basis, including empty ones. -/
def explicit_preimage : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (b : Module.Basis I K V) (F : Module.Dual K (Module.Dual K V)),
    Module.Dual.eval K V (∑ i, F (b.coord i) • b i) = F

/-- Finite dimension makes evaluation bijective. -/
def evaluation_bijective : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], Function.Bijective (Module.Dual.eval K V)

/-- The unique isomorphism whose map is evaluation: canonicity refers to this
formula, not just to equal dimensions or existence of an arbitrary isomorphism. -/
def canonical_isomorphism : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    ∃! e : V ≃ₗ[K] Module.Dual K (Module.Dual K V),
      ∀ x f, e x f = f x

/-- Inverse coordinates for any equivalence with the canonical forward formula. -/
def inverse_formula : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (b : Module.Basis I K V) (e : V ≃ₗ[K] Module.Dual K (Module.Dual K V)),
    (∀ x f, e x f = f x) →
      ∀ F, e.symm F = ∑ i, F (b.coord i) • b i

/-- Double dualization intertwines the evaluation maps in arbitrary dimension. -/
def naturality : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    T.dualMap.dualMap.comp (Module.Dual.eval K V) =
      (Module.Dual.eval K W).comp T

/-- The optional Zorn/basis-extension variant asserts only injectivity. -/
def evaluation_injective : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    Function.Injective (Module.Dual.eval K V)

end Specs.D05.M07.Biddual
