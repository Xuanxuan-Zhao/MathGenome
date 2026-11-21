import Mathlib.LinearAlgebra.Basis.Defs
import MathGenome.Internal.Specs.D05.M02.Independence

/-!
Independent statements for K05.02.basis (paper.tex:483–489).

The basis object is Mathlib's `Module.Basis`. For a given indexed family,
being a basis is expressed by the existence of such an object with exactly
those vectors. All coordinate families are `Finsupp`s, and every expansion
is a sum over its finite support. Neither the index type nor the vector space
is assumed finite, and empty index types and zero spaces are allowed.
-/

namespace Specs.D05.M02.Basis

universe u v w

/-- Type of the canonical basis construction over a named field. -/
def basis_type : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  (K : Type u) → (V : Type v) → (I : Type w) →
    [Field K] → [AddCommGroup V] → [Module K V] → Type (max u v w)

/-- Reuse the canonical basis and its finitely supported coordinate map. -/
def basis_value : basis_type.{u, v, w} :=
  fun K V I _ _ _ => Module.Basis I K V

/-- A specified indexed family is a basis exactly when it is independent and spans. -/
def basis_iff_independent_span : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] (v : I → V),
    (∃ b : Module.Basis I K V, ∀ i, b i = v i) ↔
      LinearIndependent K v ∧ Submodule.span K (Set.range v) = ⊤

/-- The source's equivalence, with the finite-support expansion written explicitly. -/
def independent_span_iff_unique_expansion : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] (v : I → V),
    (LinearIndependent K v ∧ Submodule.span K (Set.range v) = ⊤) ↔
      ∀ x : V, ∃! a : I →₀ K, (∑ i ∈ a.support, a i • v i) = x

/-- The unique-expansion characterization for the canonical basis object. -/
def basis_iff_unique_expansion : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] (v : I → V),
    (∃ b : Module.Basis I K V, ∀ i, b i = v i) ↔
      ∀ x : V, ∃! a : I →₀ K, (∑ i ∈ a.support, a i • v i) = x

/-- `repr` supplies the unique coefficients, so the coordinate convention is fixed. -/
def repr_unique_expansion : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis I K V) (x : V),
    (∑ i ∈ (b.repr x).support, b.repr x i • b i) = x ∧
      ∀ a : I →₀ K, (∑ i ∈ a.support, a i • b i) = x → a = b.repr x

end Specs.D05.M02.Basis
