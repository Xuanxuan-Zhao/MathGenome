import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.TotalComplexConstruction

/-!
Full cochain assembly propositions for paper.tex 2377–2414. These use the
shared explicit quotient cohomology and algebraic direct-sum total. The bounds
a,b are arbitrary integers; no finiteness or nontriviality hypothesis is added.
-/
namespace P103.Specs.Ch10.CochainAssembly
open P103.Specs.Ch10.TotalComplexAssembly
noncomputable section
universe u v

def cochain_columns_acyclicType : Prop :=
  ∀ {R : Type u} [Ring R] (K : CochainBicomplex.{u,v} R) (a b : ℤ),
    SupportedQuadrant K a b → ColumnsAcyclic K → Complexes.Acyclic (total K)

def cochain_rows_acyclicType : Prop :=
  ∀ {R : Type u} [Ring R] (K : CochainBicomplex.{u,v} R) (a b : ℤ),
    SupportedQuadrant K a b → RowsAcyclic K → Complexes.Acyclic (total K)

def anticommuting_cochain_columns_acyclicType : Prop :=
  ∀ {R : Type u} [Ring R] (A : AnticommutingBicomplex.{u,v} R (ComplexShape.up ℤ))
    (a b : ℤ),
    (∀ p q, p < a ∨ q < b → Subsingleton ((A.column p).X q)) →
    (∀ p, Complexes.Acyclic (A.column p)) → Complexes.Acyclic A.total

def anticommuting_cochain_rows_acyclicType : Prop :=
  ∀ {R : Type u} [Ring R] (A : AnticommutingBicomplex.{u,v} R (ComplexShape.up ℤ))
    (a b : ℤ), SupportedQuadrant A.toCommuting a b →
    (∀ q, Complexes.Acyclic (A.row q)) → Complexes.Acyclic A.total

end
end P103.Specs.Ch10.CochainAssembly
