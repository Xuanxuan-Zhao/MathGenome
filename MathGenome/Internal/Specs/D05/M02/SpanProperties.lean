import MathGenome.Internal.Specs.D05.M02.Span

/-!
Independent statements for K05.02.span_properties (paper.tex:464–470).

The span is the canonical `Submodule.span`, identified with the paper's finite
linear combinations by the upstream span goal. Sets of generators and ambient
vector spaces are arbitrary; no finite-dimensional hypothesis is imposed.
-/

namespace Specs.D05.M02.SpanProperties

/-- Every generator belongs to its span. -/
def subset_span : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (S : Set V),
    S ⊆ (Submodule.span K S : Set V)

/-- A subspace contains the span exactly when it contains all generators. -/
def span_le_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S : Set V) (U : Submodule K V),
    (Submodule.span K S : Set V) ⊆ (U : Set V) ↔ S ⊆ (U : Set V)

/-- Enlarging the generating set enlarges its span. -/
def span_mono : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S T : Set V), S ⊆ T → Submodule.span K S ≤ Submodule.span K T

/-- Taking the span of the underlying set of a span changes nothing. -/
def span_idempotent : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (S : Set V),
    Submodule.span K (Submodule.span K S : Set V) = Submodule.span K S

/-- With no generators, the span consists exactly of the zero vector. -/
def span_empty : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    (Submodule.span K (∅ : Set V) : Set V) = {0}

end Specs.D05.M02.SpanProperties
