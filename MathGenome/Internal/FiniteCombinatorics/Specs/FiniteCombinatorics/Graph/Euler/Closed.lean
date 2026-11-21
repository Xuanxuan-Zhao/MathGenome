import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Euler.Foundations

/-! W39, closed Euler trails. Edge support removes exactly the isolated vertices;
no connectivity of the entire vertex set is assumed. -/
universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Euler.Closed
open Specs.FiniteCombinatorics.Graph.Euler.Foundations
open Specs.FiniteCombinatorics.Graph.Foundations

def closed_eulerTrail_even_degreeType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a : V) (p : G.Walk a a),
    IsEulerTrailValue G p → ∀ v, Even (degreeValue G v)

def eulerTrail_edgeSupport_connectedType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), G.edgeSet.Nonempty →
    ∀ {a b : V} (p : G.Walk a b), IsEulerTrailValue G p →
      (edgeSupportValue G).Connected

def closed_eulerTrail_iff_even_degreeType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), G.edgeSet.Nonempty →
    (edgeSupportValue G).Connected →
      ((∃ (a : V) (p : G.Walk a a), IsEulerTrailValue G p ∧ IsClosedValue G p) ↔
        ∀ v, Even (degreeValue G v))

end Specs.FiniteCombinatorics.Graph.Euler.Closed
