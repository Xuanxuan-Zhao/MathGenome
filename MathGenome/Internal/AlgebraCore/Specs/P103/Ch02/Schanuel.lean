import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Exact.Basic

/-! Schanuel's lemma, paper.tex 331–352. The two finite direct sums are
represented by products. No finiteness, freeness, commutativity, nontriviality,
or common universe for the modules is required. -/

universe u v₁ v₂ w₁ w₂ z

namespace P103.Specs.Ch02.Schanuel

/-- Two short exact projective presentations of the same left module have
isomorphic stabilized kernels. -/
def schanuelType : Prop :=
  ∀ (R : Type u) [Ring R]
    (K₁ : Type v₁) (K₂ : Type v₂) (P₁ : Type w₁) (P₂ : Type w₂) (M : Type z)
    [AddCommGroup K₁] [AddCommGroup K₂] [AddCommGroup P₁] [AddCommGroup P₂]
    [AddCommGroup M] [Module R K₁] [Module R K₂] [Module R P₁] [Module R P₂]
    [Module R M] [Module.Projective R P₁] [Module.Projective R P₂]
    (i₁ : K₁ →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] M)
    (i₂ : K₂ →ₗ[R] P₂) (p₂ : P₂ →ₗ[R] M),
    Function.Injective i₁ → Function.Exact i₁ p₁ → Function.Surjective p₁ →
    Function.Injective i₂ → Function.Exact i₂ p₂ → Function.Surjective p₂ →
    Nonempty ((K₁ × P₂) ≃ₗ[R] (K₂ × P₁))

/-- The same statement for right modules, using the source's opposite-ring
convention. -/
def right_schanuelType : Prop :=
  ∀ (R : Type u) [Ring R]
    (K₁ : Type v₁) (K₂ : Type v₂) (P₁ : Type w₁) (P₂ : Type w₂) (M : Type z)
    [AddCommGroup K₁] [AddCommGroup K₂] [AddCommGroup P₁] [AddCommGroup P₂]
    [AddCommGroup M] [Module Rᵐᵒᵖ K₁] [Module Rᵐᵒᵖ K₂]
    [Module Rᵐᵒᵖ P₁] [Module Rᵐᵒᵖ P₂] [Module Rᵐᵒᵖ M]
    [Module.Projective Rᵐᵒᵖ P₁] [Module.Projective Rᵐᵒᵖ P₂]
    (i₁ : K₁ →ₗ[Rᵐᵒᵖ] P₁) (p₁ : P₁ →ₗ[Rᵐᵒᵖ] M)
    (i₂ : K₂ →ₗ[Rᵐᵒᵖ] P₂) (p₂ : P₂ →ₗ[Rᵐᵒᵖ] M),
    Function.Injective i₁ → Function.Exact i₁ p₁ → Function.Surjective p₁ →
    Function.Injective i₂ → Function.Exact i₂ p₂ → Function.Surjective p₂ →
    Nonempty ((K₁ × P₂) ≃ₗ[Rᵐᵒᵖ] (K₂ × P₁))

end P103.Specs.Ch02.Schanuel
