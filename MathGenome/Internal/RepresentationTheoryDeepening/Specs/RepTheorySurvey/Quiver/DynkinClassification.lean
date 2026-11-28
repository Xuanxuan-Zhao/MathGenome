import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.GraphShapes

namespace RepTheorySurvey.Quiver.DynkinClassificationSpec

universe u v

open SimpleGraph

/-- A graph presented by three nonempty paths from one center, with no additional
vertices or edges. -/
structure ThreeArms {V : Type u} (G : SimpleGraph V) where
  center : V
  tip : Fin 3 → V
  arm : ∀ a, G.Walk center (tip a)
  isPath : ∀ a, (arm a).IsPath
  length_pos : ∀ a, 0 < (arm a).length
  disjoint : ∀ a b, a ≠ b → ∀ x, x ∈ (arm a).support → x ∈ (arm b).support → x = center
  cover : ∀ x, x = center ∨ ∃ a, x ∈ (arm a).support
  adj_iff : ∀ x y, G.Adj x y ↔ ∃ a, (arm a).toSubgraph.Adj x y

abbrev IsDynkinDiagramType := ∀ {V : Type u}, SimpleGraph V → Prop

/-- The simply laced Dynkin diagrams, described on their own vertex types.
A spanning path is type A (including A₁). The permitted arm lengths are
`(1, 1, n - 3)` for Dₙ and `(1, 2, 2/3/4)` for E₆/E₇/E₈. -/
def isDynkinDiagram : IsDynkinDiagramType.{u} := fun G =>
  GraphShapesSpec.IsPathGraph G ∨
    ∃ T : ThreeArms G, ∃ σ : Equiv.Perm (Fin 3),
      (T.arm (σ 0)).length = 1 ∧
        ((T.arm (σ 1)).length = 1 ∨
          (T.arm (σ 1)).length = 2 ∧
            ((T.arm (σ 2)).length = 2 ∨ (T.arm (σ 2)).length = 3 ∨
              (T.arm (σ 2)).length = 4))

abbrev HasDynkinComponentsType := ∀ (Q : Type u) [Quiver.{v} Q], Prop

/-- Each edge has multiplicity one, and every connected component is a
simply laced Dynkin diagram. The empty graph satisfies this condition. -/
def hasDynkinComponents : HasDynkinComponentsType.{u, v} := fun Q _ =>
  (∀ i j : Q, FormsSpec.edgeMultiplicity i j ≤ 1) ∧
    ∀ C : (GraphShapesSpec.underlyingGraph (Q := Q)).ConnectedComponent,
      isDynkinDiagram C.toSimpleGraph

abbrev PositiveDefiniteIffDynkin : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)],
    ¬ RM03.HasOrientedCycle Q → (FormsSpec.PositiveDefinite Q ↔ hasDynkinComponents Q)

end RepTheorySurvey.Quiver.DynkinClassificationSpec
