import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.TotalComplexConstruction

/-!
The complete assembly implications of paper.tex 2377–2414, using the shared
canonical direct-sum total, signed interchange, and anticommuting twist.
The expected propositions are independent of all assembly implementations.
R is any associative unital ring, including the zero ring; right modules use
an opposite coefficient ring. The quadrant bounds are arbitrary integers.
-/
namespace P103.Specs.Ch10.TotalComplexAssembly
universe u v

/-- Either original acyclic direction suffices for the signed chain total. -/
def chain_acyclic_of_columns_or_rowsType : Prop :=
  ∀ {R : Type u} [Ring R] (K : ChainBicomplex.{u,v} R) (a b : ℤ),
    SupportedQuadrant K a b →
    (ColumnsAcyclic K ∨ RowsAcyclic K) → Complexes.Acyclic (total K)

/-- Either original acyclic direction suffices for the signed cochain total. -/
def cochain_acyclic_of_columns_or_rowsType : Prop :=
  ∀ {R : Type u} [Ring R] (K : CochainBicomplex.{u,v} R) (a b : ℤ),
    SupportedQuadrant K a b →
    (ColumnsAcyclic K ∨ RowsAcyclic K) → Complexes.Acyclic (total K)

/-- The ordinary-sum chain total, with the original untwisted hypotheses. -/
def anticommuting_chain_acyclic_of_columns_or_rowsType : Prop :=
  ∀ {R : Type u} [Ring R]
    (A : AnticommutingBicomplex.{u,v} R (ComplexShape.down ℤ)) (a b : ℤ),
    (∀ p q, p < a ∨ q < b → Subsingleton ((A.column p).X q)) →
    ((∀ p, Complexes.Acyclic (A.column p)) ∨
      (∀ q, Complexes.Acyclic (A.row q))) → Complexes.Acyclic A.total

/-- The ordinary-sum cochain total, with the original untwisted hypotheses. -/
def anticommuting_cochain_acyclic_of_columns_or_rowsType : Prop :=
  ∀ {R : Type u} [Ring R]
    (A : AnticommutingBicomplex.{u,v} R (ComplexShape.up ℤ)) (a b : ℤ),
    (∀ p q, p < a ∨ q < b → Subsingleton ((A.column p).X q)) →
    ((∀ p, Complexes.Acyclic (A.column p)) ∨
      (∀ q, Complexes.Acyclic (A.row q))) → Complexes.Acyclic A.total

end P103.Specs.Ch10.TotalComplexAssembly
