import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
Independent specifications for paper.tex 113–138 (short five lemma) and
159–165, 183–195 (four and five lemmas). The five-term rows are
`M₁ → M₂ → M₃ → M₄ → M₅` and `N₁ → N₂ → N₃ → N₄ → N₅`.
The `hⱼ` are the vertical maps. Exactness is imposed at all three
interior positions of both rows, and each square commutes.

Rings are arbitrary unital rings, without commutativity or nontriviality.
Every statement applies to right S-modules by taking `R := Sᵐᵒᵖ`.
An isomorphism conclusion includes equality of its forward linear map
with the given middle map, rather than only an abstract isomorphism.
-/

namespace P103.Specs.Ch01.FourFiveLemmas

def four_injectiveType.{uR, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10} : Prop :=
  ∀ (R : Type uR) [Ring R]
    (M₁ : Type u1) (M₂ : Type u2) (M₃ : Type u3) (M₄ : Type u4) (M₅ : Type u5) (N₁ : Type u6) (N₂ : Type u7) (N₃ : Type u8) (N₄ : Type u9) (N₅ : Type u10)
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄] [AddCommGroup M₅]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄] [AddCommGroup N₅]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R M₅]
    [Module R N₁] [Module R N₂] [Module R N₃] [Module R N₄] [Module R N₅]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] M₄) (f₄ : M₄ →ₗ[R] M₅)
    (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (g₃ : N₃ →ₗ[R] N₄) (g₄ : N₄ →ₗ[R] N₅)
    (h₁ : M₁ →ₗ[R] N₁) (h₂ : M₂ →ₗ[R] N₂) (h₃ : M₃ →ₗ[R] N₃) (h₄ : M₄ →ₗ[R] N₄) (h₅ : M₅ →ₗ[R] N₅)
    (_hc₁ : g₁.comp h₁ = h₂.comp f₁)
    (_hc₂ : g₂.comp h₂ = h₃.comp f₂)
    (_hc₃ : g₃.comp h₃ = h₄.comp f₃)
    (_hc₄ : g₄.comp h₄ = h₅.comp f₄)
    (_hf₁ : Function.Exact f₁ f₂) (_hf₂ : Function.Exact f₂ f₃) (_hf₃ : Function.Exact f₃ f₄)
    (_hg₁ : Function.Exact g₁ g₂) (_hg₂ : Function.Exact g₂ g₃) (_hg₃ : Function.Exact g₃ g₄)
    (_hh₁ : Function.Surjective h₁) (_hh₂ : Function.Injective h₂)
    (_hh₄ : Function.Injective h₄), Function.Injective h₃

def four_surjectiveType.{uR, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10} : Prop :=
  ∀ (R : Type uR) [Ring R]
    (M₁ : Type u1) (M₂ : Type u2) (M₃ : Type u3) (M₄ : Type u4) (M₅ : Type u5) (N₁ : Type u6) (N₂ : Type u7) (N₃ : Type u8) (N₄ : Type u9) (N₅ : Type u10)
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄] [AddCommGroup M₅]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄] [AddCommGroup N₅]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R M₅]
    [Module R N₁] [Module R N₂] [Module R N₃] [Module R N₄] [Module R N₅]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] M₄) (f₄ : M₄ →ₗ[R] M₅)
    (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (g₃ : N₃ →ₗ[R] N₄) (g₄ : N₄ →ₗ[R] N₅)
    (h₁ : M₁ →ₗ[R] N₁) (h₂ : M₂ →ₗ[R] N₂) (h₃ : M₃ →ₗ[R] N₃) (h₄ : M₄ →ₗ[R] N₄) (h₅ : M₅ →ₗ[R] N₅)
    (_hc₁ : g₁.comp h₁ = h₂.comp f₁)
    (_hc₂ : g₂.comp h₂ = h₃.comp f₂)
    (_hc₃ : g₃.comp h₃ = h₄.comp f₃)
    (_hc₄ : g₄.comp h₄ = h₅.comp f₄)
    (_hf₁ : Function.Exact f₁ f₂) (_hf₂ : Function.Exact f₂ f₃) (_hf₃ : Function.Exact f₃ f₄)
    (_hg₁ : Function.Exact g₁ g₂) (_hg₂ : Function.Exact g₂ g₃) (_hg₃ : Function.Exact g₃ g₄)
    (_hh₂ : Function.Surjective h₂) (_hh₄ : Function.Surjective h₄)
    (_hh₅ : Function.Injective h₅), Function.Surjective h₃

def five_bijectiveType.{uR, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10} : Prop :=
  ∀ (R : Type uR) [Ring R]
    (M₁ : Type u1) (M₂ : Type u2) (M₃ : Type u3) (M₄ : Type u4) (M₅ : Type u5) (N₁ : Type u6) (N₂ : Type u7) (N₃ : Type u8) (N₄ : Type u9) (N₅ : Type u10)
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄] [AddCommGroup M₅]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄] [AddCommGroup N₅]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R M₅]
    [Module R N₁] [Module R N₂] [Module R N₃] [Module R N₄] [Module R N₅]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] M₄) (f₄ : M₄ →ₗ[R] M₅)
    (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (g₃ : N₃ →ₗ[R] N₄) (g₄ : N₄ →ₗ[R] N₅)
    (h₁ : M₁ →ₗ[R] N₁) (h₂ : M₂ →ₗ[R] N₂) (h₃ : M₃ →ₗ[R] N₃) (h₄ : M₄ →ₗ[R] N₄) (h₅ : M₅ →ₗ[R] N₅)
    (_hc₁ : g₁.comp h₁ = h₂.comp f₁)
    (_hc₂ : g₂.comp h₂ = h₃.comp f₂)
    (_hc₃ : g₃.comp h₃ = h₄.comp f₃)
    (_hc₄ : g₄.comp h₄ = h₅.comp f₄)
    (_hf₁ : Function.Exact f₁ f₂) (_hf₂ : Function.Exact f₂ f₃) (_hf₃ : Function.Exact f₃ f₄)
    (_hg₁ : Function.Exact g₁ g₂) (_hg₂ : Function.Exact g₂ g₃) (_hg₃ : Function.Exact g₃ g₄)
    (_hh₁ : Function.Bijective h₁) (_hh₂ : Function.Bijective h₂)
    (_hh₄ : Function.Bijective h₄) (_hh₅ : Function.Bijective h₅),
    Function.Bijective h₃

def five_isomorphismType.{uR, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10} : Prop :=
  ∀ (R : Type uR) [Ring R]
    (M₁ : Type u1) (M₂ : Type u2) (M₃ : Type u3) (M₄ : Type u4) (M₅ : Type u5) (N₁ : Type u6) (N₂ : Type u7) (N₃ : Type u8) (N₄ : Type u9) (N₅ : Type u10)
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄] [AddCommGroup M₅]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄] [AddCommGroup N₅]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R M₅]
    [Module R N₁] [Module R N₂] [Module R N₃] [Module R N₄] [Module R N₅]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] M₄) (f₄ : M₄ →ₗ[R] M₅)
    (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (g₃ : N₃ →ₗ[R] N₄) (g₄ : N₄ →ₗ[R] N₅)
    (h₁ : M₁ →ₗ[R] N₁) (h₂ : M₂ →ₗ[R] N₂) (h₃ : M₃ →ₗ[R] N₃) (h₄ : M₄ →ₗ[R] N₄) (h₅ : M₅ →ₗ[R] N₅)
    (_hc₁ : g₁.comp h₁ = h₂.comp f₁)
    (_hc₂ : g₂.comp h₂ = h₃.comp f₂)
    (_hc₃ : g₃.comp h₃ = h₄.comp f₃)
    (_hc₄ : g₄.comp h₄ = h₅.comp f₄)
    (_hf₁ : Function.Exact f₁ f₂) (_hf₂ : Function.Exact f₂ f₃) (_hf₃ : Function.Exact f₃ f₄)
    (_hg₁ : Function.Exact g₁ g₂) (_hg₂ : Function.Exact g₂ g₃) (_hg₃ : Function.Exact g₃ g₄)
    (_hh₁ : Function.Bijective h₁) (_hh₂ : Function.Bijective h₂)
    (_hh₄ : Function.Bijective h₄) (_hh₅ : Function.Bijective h₅),
    ∃ e : M₃ ≃ₗ[R] N₃, e.toLinearMap = h₃

def short_five_bijectiveType.{uR, u1, u2, u3, u4, u5, u6} : Prop :=
  ∀ (R : Type uR) [Ring R] (A : Type u1) (B : Type u2) (C : Type u3) (A' : Type u4) (B' : Type u5) (C' : Type u6)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [Module R A] [Module R B] [Module R C]
    [Module R A'] [Module R B'] [Module R C']
    (i : A →ₗ[R] B) (p : B →ₗ[R] C) (i' : A' →ₗ[R] B') (p' : B' →ₗ[R] C')
    (a : A →ₗ[R] A') (b : B →ₗ[R] B') (c : C →ₗ[R] C')
    (_hi : Function.Injective i) (_hp : Function.Surjective p)
    (_hi' : Function.Injective i') (_hp' : Function.Surjective p')
    (_hex : Function.Exact i p) (_hex' : Function.Exact i' p')
    (_hc₁ : i'.comp a = b.comp i) (_hc₂ : p'.comp b = c.comp p)
    (_ha : Function.Bijective a) (_hc : Function.Bijective c),
    Function.Bijective b

def short_five_isomorphismType.{uR, u1, u2, u3, u4, u5, u6} : Prop :=
  ∀ (R : Type uR) [Ring R] (A : Type u1) (B : Type u2) (C : Type u3) (A' : Type u4) (B' : Type u5) (C' : Type u6)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [Module R A] [Module R B] [Module R C]
    [Module R A'] [Module R B'] [Module R C']
    (i : A →ₗ[R] B) (p : B →ₗ[R] C) (i' : A' →ₗ[R] B') (p' : B' →ₗ[R] C')
    (a : A →ₗ[R] A') (b : B →ₗ[R] B') (c : C →ₗ[R] C')
    (_hi : Function.Injective i) (_hp : Function.Surjective p)
    (_hi' : Function.Injective i') (_hp' : Function.Surjective p')
    (_hex : Function.Exact i p) (_hex' : Function.Exact i' p')
    (_hc₁ : i'.comp a = b.comp i) (_hc₂ : p'.comp b = c.comp p)
    (_ha : Function.Bijective a) (_hc : Function.Bijective c),
    ∃ e : B ≃ₗ[R] B', e.toLinearMap = b

end P103.Specs.Ch01.FourFiveLemmas
