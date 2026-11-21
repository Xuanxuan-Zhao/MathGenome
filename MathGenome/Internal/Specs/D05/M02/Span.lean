import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.BigOperators.Module
import MathGenome.Internal.Specs.D05.M02.Subspace

/-!
Independent statements for K05.02.span (paper.tex:457–462).

The canonical span is `Submodule.span`. The set `finiteCombinations` records
the paper's formula separately, so its identification with that submodule is
a proof obligation. Only the finite set `F` is summed over: the generating set
`S` and the ambient vector space need not be finite. Coefficients outside `F`
are irrelevant and impose no restriction on the finite sum.
-/

namespace Specs.D05.M02.Span

universe u v

/-- The type of a span operation on subsets of a vector space. -/
def span_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] →
    [Module K V] → Set V → Submodule K V

/-- Use the canonical algebraic span, with its subspace structure. -/
def span_value : span_type.{u, v} :=
  fun K V _ _ _ S => Submodule.span K S

/-- The paper's set of finite linear combinations, including the empty sum. -/
def finiteCombinations (K : Type u) {V : Type v} [Field K]
    [AddCommGroup V] [Module K V] (S : Set V) : Set V :=
  {x | ∃ (F : Finset V) (a : V → K),
    (↑F : Set V) ⊆ S ∧ (∑ s ∈ F, a s • s) = x}

/-- Membership in the canonical span is exactly the displayed finite-sum formula. -/
def mem_span_iff_finite_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S : Set V) (x : V),
    x ∈ Submodule.span K S ↔
      ∃ (F : Finset V) (a : V → K),
        (↑F : Set V) ⊆ S ∧ (∑ s ∈ F, a s • s) = x

/-- The finite sum over the empty set is the zero vector. -/
def empty_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (a : V → K),
    (∑ s ∈ (∅ : Finset V), a s • s) = (0 : V)

/-- The empty combination supplies zero even if the generating set is empty. -/
def zero_mem_span : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (S : Set V),
    (0 : V) ∈ Submodule.span K S

/-- The sum of two finite combinations is again in the span. -/
def add_mem_span : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S : Set V) (x y : V),
    x ∈ Submodule.span K S → y ∈ Submodule.span K S →
      x + y ∈ Submodule.span K S

/-- Multiplying by a scalar preserves span membership. -/
def smul_mem_span : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S : Set V) (a : K) (x : V),
    x ∈ Submodule.span K S → a • x ∈ Submodule.span K S

/-- Scalar multiplication multiplies the coefficients of the same finite sum. -/
def smul_finite_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F : Finset V) (a : K) (b : V → K),
    a • (∑ s ∈ F, b s • s) = ∑ s ∈ F, (a * b s) • s

/-- The finite-combination set itself is the carrier of a vector subspace. -/
def finite_combinations_subspace : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (S : Set V),
    ∃ U : Submodule K V, (U : Set V) = finiteCombinations K S

end Specs.D05.M02.Span
