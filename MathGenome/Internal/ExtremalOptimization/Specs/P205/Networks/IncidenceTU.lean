import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.TotalUnimodularity
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.Models

/-! Independent statements for the incidence assertions of paper.tex W35.
Arc labels are an arbitrary type E; their endpoints need not be injective or
unequal. Thus parallel arcs, opposite arcs, loops, and isolated vertices are
all retained. The statements hold for arbitrary types, in particular finite
networks and finite bipartite graphs. -/

universe u v
noncomputable section
namespace Specs.P205.Networks

/-- Net-outflow convention: a loop contributes 1 - 1 = 0. -/
def directedIncidence {V : Type u} {E : Type v} (tail head : E → V) : Matrix V E ℤ := by
  classical
  exact fun i e => (if i = tail e then 1 else 0) - (if i = head e then 1 else 0)

def directedIncidenceType :=
  ∀ {V : Type u} {E : Type v}, (E → V) → (E → V) → Matrix V E ℤ

/-- No injectivity, looplessness, capacity, or flow hypotheses. -/
def directed_incidence_tu : Prop :=
  ∀ {V : Type u} {E : Type v} (tail head : E → V),
    (directedIncidence tail head).IsTotallyUnimodular

/-- The canonical allowed-edge coordinates from the shared matching interface. -/
def bipartite_incidence_tu : Prop :=
  ∀ {L : Type u} {R : Type v} (G : Specs.P205.Matching.BipartiteGraph L R),
    (Specs.P205.Matching.incidence G).IsTotallyUnimodular

/-- Orient from L to R and negate exactly the R rows of the unsigned matrix. -/
def bipartite_orientation : Prop :=
  ∀ {L : Type u} {R : Type v} (G : Specs.P205.Matching.BipartiteGraph L R),
    directedIncidence (fun e : Specs.P205.Matching.Edge G => Sum.inl e.val.1)
      (fun e => Sum.inr e.val.2) =
    Matrix.of (fun i e =>
      (Sum.elim (fun _ : L => (1 : ℤ)) (fun _ : R => -1)) i *
        Specs.P205.Matching.incidence G i e)

end Specs.P205.Networks
