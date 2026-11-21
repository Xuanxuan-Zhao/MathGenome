import Mathlib.LinearAlgebra.LinearIndependent.Defs
import MathGenome.Internal.Specs.D05.M02.Span

/-!
Independent statements for K05.02.independence (paper.tex:472–473).

Families are functions on an index type, so equal vectors at different indices
remain different occurrences. Relations use `Finsupp`, even when the index type
is infinite. No finite-dimensional hypothesis is imposed on the ambient space,
and there is no restriction on the characteristic of the field.
-/

namespace Specs.D05.M02.Independence

universe u v w

/-- The type of the canonical independence predicate for indexed families. -/
def independent_type : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  (K : Type u) → (V : Type v) → (I : Type w) →
    [Field K] → [AddCommGroup V] → [Module K V] → (I → V) → Prop

/-- Use Mathlib's independence of indexed families. -/
def independent_value : independent_type.{u, v, w} :=
  fun K _ _ _ _ _ v => LinearIndependent K v

/-- The source's defining condition: every finite-support zero relation has
zero coefficient at every index. The displayed sum is over the support. -/
def independent_iff_finsupp_relation : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] (v : I → V),
    LinearIndependent K v ↔
      ∀ a : I →₀ K, (∑ i ∈ a.support, a i • v i) = 0 → ∀ i, a i = 0

/-- An equivalent formulation using an arbitrary finite set of indices. -/
def independent_iff_finset_relation : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] (v : I → V),
    LinearIndependent K v ↔
      ∀ (F : Finset I) (a : I → K), (∑ i ∈ F, a i • v i) = 0 →
        ∀ i ∈ F, a i = 0

/-- Any family indexed by an empty type is independent. -/
def empty_family : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [IsEmpty I]
    (v : I → V), LinearIndependent K v

/-- The coefficient one at a zero entry gives a nontrivial relation. -/
def zero_entry_relation : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : I → V) (j : I), v j = 0 →
      ∃ a : I →₀ K, a j = 1 ∧ (∀ i, i ≠ j → a i = 0) ∧
        (∑ i ∈ a.support, a i • v i) = 0 ∧ a ≠ 0

/-- A zero entry prevents independence. -/
def not_independent_of_zero_entry : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : I → V) (j : I), v j = 0 → ¬ LinearIndependent K v

/-- At two distinct equal entries, coefficients one and negative one give a
nontrivial zero relation, also in characteristic two. -/
def repeated_entry_relation : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : I → V) (i j : I), i ≠ j → v i = v j →
      ∃ a : I →₀ K, a i = 1 ∧ a j = -1 ∧
        (∀ k, k ≠ i → k ≠ j → a k = 0) ∧
        (∑ k ∈ a.support, a k • v k) = 0 ∧ a ≠ 0

/-- Repeated entries at different indices prevent independence. -/
def not_independent_of_repeated_entry : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : I → V) (i j : I), i ≠ j → v i = v j → ¬ LinearIndependent K v

/-- Injective reindexing picks a subfamily, preserving independence. -/
def subfamily : Prop :=
  ∀ {K V I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : I → V) (f : J → I), Function.Injective f →
      LinearIndependent K v → LinearIndependent K (v ∘ f)

/-- In particular, restriction to any subset of the indices is independent. -/
def restriction : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : I → V) (S : Set I), LinearIndependent K v →
      LinearIndependent K (fun i : S => v i)

/-- Dependence means some occurrence is in the span of the other occurrences.
The image is taken after deleting an index, rather than deleting a vector value.
The statement even holds for infinite families because span uses finite sums. -/
def dependent_iff_mem_span_others : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] (v : I → V),
    ¬ LinearIndependent K v ↔
      ∃ j, v j ∈ Submodule.span K (v '' (Set.univ \ {j}))

/-- The finite-list criterion with the combination written out. `Fin n` keeps
repeated entries distinct; `n = 0` is allowed. -/
def finite_list_dependent_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) (v : Fin n → V),
    ¬ LinearIndependent K v ↔
      ∃ (j : Fin n) (a : Fin n → K),
        v j = ∑ i ∈ Finset.univ.erase j, a i • v i

end Specs.D05.M02.Independence
