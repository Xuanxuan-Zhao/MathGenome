import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.TotalComplexConstruction

/-! Chain assembly for translated first quadrants, paper.tex 2377–2414.
The acyclicity predicate is the shared quotient-of-cycles definition.
Right modules are represented by taking the opposite coefficient ring. -/
namespace P103.Specs.Ch10.TotalComplexAssembly
universe u v

/-- Acyclic original vertical columns imply acyclicity of the signed direct-sum total. -/
def chain_columns_acyclicType : Prop :=
  ∀ {R : Type u} [Ring R] (K : ChainBicomplex.{u,v} R) (a b : ℤ),
    SupportedQuadrant K a b → ColumnsAcyclic K → Complexes.Acyclic (total K)

/-- Acyclic original horizontal rows imply acyclicity of the same total. -/
def chain_rows_acyclicType : Prop :=
  ∀ {R : Type u} [Ring R] (K : ChainBicomplex.{u,v} R) (a b : ℤ),
    SupportedQuadrant K a b → RowsAcyclic K → Complexes.Acyclic (total K)

/-- The ordinary-sum total of anticommuting chain differentials, column version. -/
def anticommuting_chain_columns_acyclicType : Prop :=
  ∀ {R : Type u} [Ring R] (A : AnticommutingBicomplex.{u,v} R (ComplexShape.down ℤ))
    (a b : ℤ),
    (∀ p q, p < a ∨ q < b → Subsingleton ((A.column p).X q)) →
    (∀ p, Complexes.Acyclic (A.column p)) → Complexes.Acyclic (anticommutingTotal A)

/-- The ordinary-sum total of anticommuting chain differentials, row version. -/
def anticommuting_chain_rows_acyclicType : Prop :=
  ∀ {R : Type u} [Ring R] (A : AnticommutingBicomplex.{u,v} R (ComplexShape.down ℤ))
    (a b : ℤ),
    (∀ p q, p < a ∨ q < b → Subsingleton ((A.column p).X q)) →
    (∀ q, Complexes.Acyclic (A.row q)) → Complexes.Acyclic (anticommutingTotal A)

end P103.Specs.Ch10.TotalComplexAssembly
