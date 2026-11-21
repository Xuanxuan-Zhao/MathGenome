import MathGenome.Internal.Specs.D05.M02.VectorSpace
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
Independent statements for K05.03.linear_map (paper.tex:533–534).

The canonical maps are Mathlib `LinearMap`s over the same named field on both
spaces. The equivalence below checks the underlying function against exactly
the two defining identities. No dimension hypothesis is imposed. The finite
sum statements use indexed families, so repeated vectors remain distinct, and
the finitely supported formulation also permits an infinite index type.

The scalar-field warning is witnessed by ordinary conjugation on ℂ: the same
function is real-linear but is not complex-linear. It is not a claim that every
formula mentioning conjugation fails to be complex-linear.
-/

namespace Specs.D05.M03.LinearMap

open scoped BigOperators ComplexConjugate

universe u v w

/-- The type of a canonical linear-map type constructor. -/
def linearMap_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  (K : Type u) → (V : Type v) → (W : Type w) → [Field K] →
    [AddCommGroup V] → [Module K V] → [AddCommGroup W] → [Module K W] →
      Type (max v w)

/-- Use the existing bundled linear map over the common scalar field. -/
def linearMap_value : linearMap_type.{u, v, w} :=
  fun K V W _ _ _ _ _ => V →ₗ[K] W

/-- The paper's two identities characterize precisely the same functions. -/
def linearMap_iff_axioms : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (t : V → W),
    (∃ T : V →ₗ[K] W, (T : V → W) = t) ↔
      (∀ u v : V, t (u + v) = t u + t v) ∧
      (∀ (a : K) (v : V), t (a • v) = a • t v)

/-- Every finite indexed linear combination is preserved, including the empty one. -/
def map_finite_combination : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W)
    (s : Finset I) (a : I → K) (v : I → V),
    T (∑ i ∈ s, a i • v i) = ∑ i ∈ s, a i • T (v i)

/-- An arbitrary indexed family may be combined with finitely supported coefficients. -/
def map_finsupp_combination : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W)
    (a : I →₀ K) (v : I → V),
    T (a.sum (fun i c => c • v i)) = a.sum (fun i c => c • T (v i))

/-- A linear map sends the zero vector to zero. -/
def map_zero : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W), T 0 = 0

/-- A linear map preserves additive inverses. -/
def map_neg : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) (v : V), T (-v) = -T v

/-- Conjugation is linear with the canonical restricted real scalar action. -/
def conjugation_real_linear : Prop :=
  ∃ T : ℂ →ₗ[ℝ] ℂ, ∀ z : ℂ, T z = conj z

/-- The same conjugation function is not complex-linear. -/
def conjugation_not_complex_linear : Prop :=
  ¬ ∃ T : ℂ →ₗ[ℂ] ℂ, ∀ z : ℂ, T z = conj z

end Specs.D05.M03.LinearMap
