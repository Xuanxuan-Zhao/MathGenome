import Mathlib.Algebra.Field.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
Independent statements for `foundation.free_vectors`, paper.tex:350.

The free vector space is the existing type `S →₀ K`, with its pointwise
operations. The generator at `s` is `Finsupp.single s 1`. All sums below are
finite sums over the support of a coefficient family. In particular `S` may
be infinite or empty, and the target vector space has no dimension restriction.
-/

namespace Specs.D05.Foundations.FreeVectors

open scoped BigOperators

universe u v w

/-- Type of the delta family in the canonical finitely supported space. -/
def delta_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (S : Type v) → [Field K] → S → (S →₀ K)

/-- A delta vector has coefficient one at its named index and zero elsewhere. -/
noncomputable def delta_value : delta_type.{u, v} :=
  fun K S _ s => Finsupp.single s (1 : K)

/-- The two operations on the free vector space are pointwise. -/
def pointwise_operations : Prop :=
  ∀ {K : Type u} {S : Type v} [Field K]
    (a b : S →₀ K) (r : K) (s : S),
    (a + b) s = a s + b s ∧ (r • a) s = r * a s

/-- The explicit values of a delta vector, without assuming decidable equality. -/
def delta_coordinates : Prop :=
  ∀ {K : Type u} {S : Type v} [Field K] (s : S),
    (Finsupp.single s (1 : K)) s = 1 ∧
      ∀ t : S, t ≠ s → (Finsupp.single s (1 : K)) t = 0

/-- Every free vector is its finite delta expansion. -/
def support_expansion : Prop :=
  ∀ {K : Type u} {S : Type v} [Field K] (a : S →₀ K),
    a = ∑ s ∈ a.support, a s • Finsupp.single s (1 : K)

/-- Evaluation recovers every coefficient, including indices outside the support. -/
def coefficient_recovery : Prop :=
  ∀ {K : Type u} {S : Type v} [Field K] (c : S →₀ K) (s : S),
    (∑ t ∈ c.support, c t • Finsupp.single t (1 : K)) s = c s

/-- Each vector has exactly one finitely supported family of delta coefficients. -/
def unique_coefficients : Prop :=
  ∀ {K : Type u} {S : Type v} [Field K] (a : S →₀ K),
    ∃! c : S →₀ K, a = ∑ s ∈ c.support, c s • Finsupp.single s (1 : K)

/-- Type of the explicit linear extension of an arbitrary function. -/
def linearExtension_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  (K : Type u) → (S : Type v) → (W : Type w) → [Field K] →
    [AddCommGroup W] → [Module K W] → (S → W) → ((S →₀ K) →ₗ[K] W)

/-- The canonical extension is the finite linear-combination map. -/
noncomputable def linearExtension_value : linearExtension_type.{u, v, w} :=
  fun K _ _ _ _ _ f => Finsupp.linearCombination K f

/-- The constructed linear map has exactly the formula in the manuscript. -/
def linearExtension_apply : Prop :=
  ∀ {K : Type u} {S : Type v} {W : Type w} [Field K]
    [AddCommGroup W] [Module K W] (f : S → W) (a : S →₀ K),
    Finsupp.linearCombination K f a = ∑ s ∈ a.support, a s • f s

/-- On delta generators the extension agrees with the original function. -/
def linearExtension_delta : Prop :=
  ∀ {K : Type u} {S : Type v} {W : Type w} [Field K]
    [AddCommGroup W] [Module K W] (f : S → W) (s : S),
    Finsupp.linearCombination K f (Finsupp.single s 1) = f s

/-- Any linear extension is forced to have the stated finite-sum formula. -/
def extension_formula : Prop :=
  ∀ {K : Type u} {S : Type v} {W : Type w} [Field K]
    [AddCommGroup W] [Module K W] (f : S → W) (T : (S →₀ K) →ₗ[K] W),
    (∀ s : S, T (Finsupp.single s 1) = f s) →
      ∀ a : S →₀ K, T a = ∑ s ∈ a.support, a s • f s

/-- The universal property includes both existence and uniqueness as linear maps. -/
def unique_linear_extension : Prop :=
  ∀ {K : Type u} {S : Type v} {W : Type w} [Field K]
    [AddCommGroup W] [Module K W] (f : S → W),
    ∃! T : (S →₀ K) →ₗ[K] W, ∀ s : S, T (Finsupp.single s 1) = f s

end Specs.D05.Foundations.FreeVectors
