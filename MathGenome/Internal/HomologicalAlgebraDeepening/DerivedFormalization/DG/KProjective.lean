import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomComplex

universe u v w

namespace DerivedFormalization.RightDGModule

/-- A right dg module is K-projective if its Hom complex into each acyclic
right dg module is acyclic. -/
def IsKProjective {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
    (P : RightDGModule A) : Prop :=
  ∀ N : RightDGModule A, N.Acyclic → (homComplex P N).Acyclic

end DerivedFormalization.RightDGModule
