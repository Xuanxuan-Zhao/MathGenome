import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.EmbeddingProblem
import Mathlib.Algebra.Group.DivInvMonoid

/-! Proposition IG08 for the Krull group of a chosen separable closure. -/

namespace Specs.GaloisFormalization.IG.FiniteFieldEmbeddingProblems

open GH.KrullLayers

universe u v w z

/-- Every finite embedding problem over a finite field admits a weak solution. -/
def weakSolutionExistsType : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {B : Type w} {Q : Type z}
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    [Finite k] (P : FiniteEmbeddingProblem (AbsoluteGaloisGroup k S) B Q),
    Nonempty P.WeakSolution

/-- A proper solution exists precisely when the middle group is cyclic. -/
def properSolutionExistsIffType : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {B : Type w} {Q : Type z}
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    [Finite k] (P : FiniteEmbeddingProblem (AbsoluteGaloisGroup k S) B Q),
    (∃ s : P.WeakSolution, Function.Surjective s.lift) ↔ IsCyclic B

end Specs.GaloisFormalization.IG.FiniteFieldEmbeddingProblems
