import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Euler.Foundations
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Connected.PathConnected

/-! Independent interface for the geometric argument in W63,
paper.tex 2468–2488. `walkTrace` is the actual union of the drawn edges,
including the vertex for a length-zero walk. Cyclic order is defined geometrically
using initial rays of the actual edge sets and angular order after a rotation.
No separation or coloring certificate is a field of the drawing or cyclic order.
The main-result types state the full circle, separation and coloring obligations. -/

universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation
open Specs.FiniteCombinatorics.Graph.Plane.Foundations

/-- Image of a graph walk in the actual drawing. -/
def walkTrace {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G) :
    {a b : V} → G.Walk a b → Set Point
  | a, _, .nil => {D.point a}
  | a, _, @SimpleGraph.Walk.cons _ _ _ b _ h p => D.edge ⟨s(a,b), h⟩ ∪ walkTrace D p

def walkTraceType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (_D : Drawing G),
  {a b : V} → G.Walk a b → Set Point

def walkTraceValue : walkTraceType := @walkTrace

def walk_trace_vertexType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) {a b : V} (p : G.Walk a b) (v : V),
  D.point v ∈ walkTrace D p ↔ v ∈ p.support

def walk_trace_compactType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) {a b : V} (p : G.Walk a b), IsCompact (walkTrace D p)

def walk_trace_polygonalType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) {a b : V} (p : G.Walk a b), IsPolygonal (walkTrace D p)

/-- The combinatorial closing operation really is a simple graph cycle. -/
def closed_walk_cycleType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
    (x : V) {a c : V} (ha : G.Adj x a) (hc : G.Adj x c) (p : G.Walk a c),
    a ≠ c → p.IsPath → x ∉ p.support →
      (SimpleGraph.Walk.cons ha (p.concat hc.symm)).IsCycle

def walk_trace_joinedType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) {a b : V} (p : G.Walk a b),
  JoinedIn (walkTrace D p) (D.point a) (D.point b)

def disjoint_walk_tracesType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) {a b c d : V} (p : G.Walk a b) (q : G.Walk c d),
  List.Disjoint p.support q.support → Disjoint (walkTrace D p) (walkTrace D q)

def walk_avoiding_setType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) {a b : V} (p : G.Walk a b) (K : Set Point),
  Disjoint (walkTrace D p) K →
    connectedComponentIn Kᶜ (D.point a) = connectedComponentIn Kᶜ (D.point b)

/-- The local-to-global argument needs no extra regularity beyond two connected
local sectors and the common-boundary assertion of Jordan separation. -/
def local_sectors_distinctType : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (S U A B : Set X) (x a b p q : X),
  IsOpen U → x ∈ U → U ∩ S ⊆ A ∪ B → A ⊆ S → B ⊆ S →
  IsPreconnected A → IsPreconnected B → a ∈ A → b ∈ B →
  x ∈ closure (connectedComponentIn S p) →
  x ∈ closure (connectedComponentIn S q) →
  connectedComponentIn S p ≠ connectedComponentIn S q →
  connectedComponentIn S a ≠ connectedComponentIn S b

/-- A spoke which avoids a closed curve after its initial endpoint stays in
one complementary component, all the way to its other endpoint. -/
def punctured_path_componentType : Prop :=
  ∀ {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y) (K : Set X),
  (∀ t : unitInterval, t ≠ 0 → p t ∉ K) →
  ∀ t : unitInterval, t ≠ 0 →
    connectedComponentIn Kᶜ (p t) = connectedComponentIn Kᶜ y

/-- A geometric ray, with its initial point included. -/
def rayFrom (c u : Point) : Set Point := {z | ∃ t : ℝ, 0 ≤ t ∧ z = c + t • u}

/-- A nonzero direction giving the actual edge germ at its initial endpoint.
This describes a local subset equality, not a topological separation witness. -/
def IsInitialDirection {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (x y : V) (h : G.Adj x y) (v : Point) : Prop :=
  v ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
    D.edge ⟨s(x,y), h⟩ ∩ Metric.ball (D.point x) ε =
      rayFrom (D.point x) v ∩ Metric.ball (D.point x) ε

/-- Angular order with an arbitrary cut; rotating allows a cut in any gap. -/
def CyclicDirections (a b c d : Point) : Prop :=
  let z : Point → ℂ := fun p => ⟨p.1, p.2⟩
  ∃ r : ℂ, r ≠ 0 ∧
    (r * z a).arg < (r * z b).arg ∧
    (r * z b).arg < (r * z c).arg ∧
    (r * z c).arg < (r * z d).arg

/-- Four incident edges alternate about x, allowing either orientation of the
plane. No assertion about components of a curve complement is assumed. -/
def CyclicSpokes {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (x a b c d : V) (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (hd : G.Adj x d) : Prop :=
  ∃ va vb vc vd : Point,
    IsInitialDirection D x a ha va ∧ IsInitialDirection D x b hb vb ∧
    IsInitialDirection D x c hc vc ∧ IsInitialDirection D x d hd vd ∧
    (CyclicDirections va vb vc vd ∨ CyclicDirections va vd vc vb)

/-- The closed curve formed by the simple a-to-c path and its two closing spokes. -/
def closedTrace {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (x : V) {a c : V} (ha : G.Adj x a) (hc : G.Adj x c) (p : G.Walk a c) : Set Point :=
  D.edge ⟨s(x,a), ha⟩ ∪ walkTrace D p ∪ D.edge ⟨s(x,c), hc⟩

def sphereClosedTrace {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (x : V) {a c : V} (ha : G.Adj x a) (hc : G.Adj x c) (p : G.Walk a c) : Set Sphere :=
  OnePoint.some '' closedTrace D x ha hc p

def closed_trace_vertexType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (x : V) {a c : V} (ha : G.Adj x a) (hc : G.Adj x c) (p : G.Walk a c) (v : V),
    D.point v ∈ closedTrace D x ha hc p ↔ v = x ∨ v ∈ p.support

def closed_trace_polygonalType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (x : V) {a c : V} (ha : G.Adj x a) (hc : G.Adj x c) (p : G.Walk a c),
    IsPolygonal (closedTrace D x ha hc p)

/-- Required regularity bridge: every allowed polygonal edge has an initial ray. -/
def initial_direction_existsType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (x y : V) (h : G.Adj x y), ∃ v, IsInitialDirection D x y h v

/-- The first part of the assigned result: construct a genuine embedded circle
from a simple graph path avoiding x. -/
def closed_trace_circleType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (x : V) {a c : V} (ha : G.Adj x a) (hc : G.Adj x c) (p : G.Walk a c),
    a ≠ c → p.IsPath → x ∉ p.support →
    ∃ e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → Sphere,
      Topology.IsEmbedding e ∧ Set.range e = sphereClosedTrace D x ha hc p

/-- The global separation assertion for alternating neighbors. The drawing
axioms themselves imply the required spoke disjointness once b,d avoid p. -/
def kempe_separationType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (x a b c d : V) (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (hd : G.Adj x d) (p : G.Walk a c),
    [a,b,c,d].Nodup → CyclicSpokes D x a b c d ha hb hc hd →
    p.IsPath → x ∉ p.support → b ∉ p.support → d ∉ p.support →
    connectedComponentIn (sphereClosedTrace D x ha hc p)ᶜ (OnePoint.some (D.point b)) ≠
      connectedComponentIn (sphereClosedTrace D x ha hc p)ᶜ (OnePoint.some (D.point d))

/-- No continuous complementary path joins the alternating neighbors. -/
def kempe_no_complementary_pathType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (x a b c d : V) (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (hd : G.Adj x d) (p : G.Walk a c),
    [a,b,c,d].Nodup → CyclicSpokes D x a b c d ha hb hc hd →
    p.IsPath → x ∉ p.support → b ∉ p.support → d ∉ p.support →
    ¬JoinedIn (sphereClosedTrace D x ha hc p)ᶜ
      (OnePoint.some (D.point b)) (OnePoint.some (D.point d))

/-- The coloring specialization, for arbitrary two walks in G−x. Properness of
the coloring is not needed for this stronger obstruction to two disjoint palettes. -/
def alternating_color_pathsType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (x a b c d : V) (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (hd : G.Adj x d) (color : V → Fin 4),
    [a,b,c,d].Nodup → CyclicSpokes D x a b c d ha hb hc hd →
    color a = 0 → color b = 1 → color c = 2 → color d = 3 →
    ¬((∃ p : G.Walk a c, x ∉ p.support ∧
          ∀ v ∈ p.support, color v = 0 ∨ color v = 2) ∧
       ∃ q : G.Walk b d, x ∉ q.support ∧
          ∀ v ∈ q.support, color v = 1 ∨ color v = 3)

/-- Disjoint palettes imply geometric disjointness, without a planarity certificate. -/
def disjoint_palette_tracesType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    {C : Type} (color : V → C) (A B : Set C), Disjoint A B →
    (∀ v ∈ p.support, color v ∈ A) → (∀ v ∈ q.support, color v ∈ B) →
    Disjoint (walkTrace D p) (walkTrace D q)

end Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation
