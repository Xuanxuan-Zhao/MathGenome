import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.FundamentalGroupoid
import Mathlib.Topology.Homotopy.Lifting

/-! Source objects for paper.tex, Definition 1.3 and Theorem 1.4.
All topologies are the given topologies. A sheet is an open partial
homeomorphism whose forward map is the projection and whose target is U.
Thus its source is an open subset of E homeomorphic over B to U.
The homotopy statements below use the paper's order Z × I. -/
namespace P202Specs.Topology

open scoped unitInterval
universe u v w

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

structure CoveringSheet (p : E → B) (U : Set B) where
  chart : OpenPartialHomeomorph E B
  projection : (chart : E → B) = p
  target_eq : chart.target = U

/-- A disjoint union of open sheets, each mapping homeomorphically onto U. -/
def EvenlyCovered (p : E → B) (U : Set B) : Prop :=
  IsOpen U ∧ ∃ S : Set (CoveringSheet p U),
    S.Pairwise (fun s t => Disjoint s.chart.source t.chart.source) ∧
    (⋃ s ∈ S, s.chart.source) = p ⁻¹' U

/-- Coverings are surjective, including over disconnected bases. -/
def Covering (p : E → B) : Prop :=
  Function.Surjective p ∧ ∀ b, ∃ U, b ∈ U ∧ EvenlyCovered p U

namespace CoveringExpected

def coveringBridge : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B] (p : E → B),
    Covering p ↔ IsCoveringMap p ∧ Function.Surjective p

def coveringContinuous : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B] (p : E → B),
    Covering p → Continuous p

/-- Continuous paths with prescribed initial value; the terminal point is free. -/
def pathLifting : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), Covering p → ∀ (a : C(unitInterval, B)) (e : E), p e = a 0 →
      ∃! L : C(unitInterval, E), (∀ t, p (L t) = a t) ∧ L 0 = e

def homotopyLifting : Prop :=
  ∀ (E : Type u) (B : Type v) (Z : Type w)
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Z]
    (p : E → B), Covering p → ∀ (F : C(Z × unitInterval, B)) (h : C(Z, E)),
    (∀ z, p (h z) = F (z, 0)) →
      ∃! L : C(Z × unitInterval, E),
        (∀ q, p (L q) = F q) ∧ ∀ z, L (z, 0) = h z

/-- Every continuous lift of a constant path is itself constant. -/
def constantLift : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), Covering p → ∀ (b : B) (L : C(unitInterval, E)),
      (∀ t, p (L t) = b) → ∀ t, L t = L 0

/-- A continuous lifted endpoint-fixed square, written (homotopy time, path time),
has both endpoint sides fixed when its initial side is fixed. -/
def homotopyEndpoints : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), Covering p → ∀ (x y : B) (a b : SourcePath x y)
    (H : PathHomotopy a b) (L : C(unitInterval × unitInterval, E)) (e : E),
    (∀ q, p (L q) = H q) → (∀ s, L (s, 0) = e) →
      (∀ s, L (s, 0) = e) ∧ ∀ s, L (s, 1) = L (0, 1)

/-- Pointwise continuous lifts of the paths of a homotopy also have fixed
terminal points; joint continuity of the chosen lifts is not assumed. -/
def pathHomotopyLifts : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), Covering p → ∀ (x y : B) (a b : SourcePath x y)
    (H : PathHomotopy a b) (L : unitInterval → C(unitInterval, E)) (e : E),
    (∀ s t, p (L s t) = H (s, t)) → (∀ s, L s 0 = e) →
      ∀ s, L s 1 = L 0 1

/-- In particular any two lifts of homotopic paths with the same initial value
have the same terminal value. -/
def homotopicLiftEndpoints : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), Covering p → ∀ (x y : B) (a b : SourcePath x y),
    Nonempty (PathHomotopy a b) → ∀ (L M : C(unitInterval, E)),
      (∀ t, p (L t) = a t) → (∀ t, p (M t) = b t) → L 0 = M 0 → L 1 = M 1

end CoveringExpected
end P202Specs.Topology
