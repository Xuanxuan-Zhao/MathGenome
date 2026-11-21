import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.FaceSides
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Plane.RealizationGeometry
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Coloring.Bipartite
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Convex.Between

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.Bipartite

universe u v
noncomputable section
/-! Auxiliary definitions for the directed-side construction. They impose no
additional premise on the drawing; every construction and compatibility
property used by the public numerical theorem is proved below. -/
namespace FiniteCombinatorics.Graph.Plane.FaceSideAux

structure RotationSystem {V : Type u} (G : SimpleGraph V) where
  turn : ∀ v, Equiv.Perm (G.neighborSet v)
  cyclic : ∀ v, (turn v).IsCycleOn Set.univ

variable {V : Type u} {G : SimpleGraph V}

/-- Reverse the incoming dart, then take the next outgoing neighbor. -/
def successor (R : RotationSystem G) : Equiv.Perm G.Dart where
  toFun d := ⟨(d.snd, (R.turn d.snd ⟨d.fst, d.adj.symm⟩).val),
    (R.turn d.snd ⟨d.fst, d.adj.symm⟩).property⟩
  invFun d := ⟨((R.turn d.fst).symm ⟨d.snd, d.adj⟩, d.fst),
    ((R.turn d.fst).symm ⟨d.snd, d.adj⟩).property.symm⟩
  left_inv d := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · change ((R.turn d.snd).symm (R.turn d.snd ⟨d.fst, d.adj.symm⟩)).val = d.fst
      simp
    · rfl
  right_inv d := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · rfl
    · change (R.turn d.fst ((R.turn d.fst).symm ⟨d.snd, d.adj⟩)).val = d.snd
      simp

/-- The least positive return time; finiteness makes it positive. -/
def boundaryLength (R : RotationSystem G) (d : G.Dart) : ℕ :=
  Function.minimalPeriod (successor R) d

/-- Orbits include every dart, even if a bridge has both sides in one orbit. -/
def BoundaryOrbit (R : RotationSystem G) :=
  Quotient (Equiv.Perm.SameCycle.setoid (successor R))

def orbitMk (R : RotationSystem G) (d : G.Dart) : BoundaryOrbit R :=
  Quotient.mk _ d

def RotationSystemType := ∀ {V : Type u}, SimpleGraph V → Type u

def successorType := ∀ {V : Type u} {G : SimpleGraph V},
  RotationSystem G → Equiv.Perm G.Dart

def boundaryLengthType := ∀ {V : Type u} {G : SimpleGraph V},
  RotationSystem G → G.Dart → ℕ

def BoundaryOrbitType := ∀ {V : Type u} {G : SimpleGraph V}, RotationSystem G → Type u

def successor_continuesType : Prop := ∀ {V : Type u} {G : SimpleGraph V}
  (R : RotationSystem G) (d : G.Dart), (successor R d).fst = d.snd

def boundary_length_ge_threeType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V}, G.Connected → 3 ≤ Nat.card V →
  ∀ (R : RotationSystem G) (d : G.Dart), 3 ≤ boundaryLength R d

def boundary_closed_walkType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (R : RotationSystem G) (d : G.Dart),
  ∃ p : G.Walk d.fst d.fst, p.length = boundaryLength R d ∧
    ∀ i : Fin p.length,
      p.darts[i.val] = (successor R : G.Dart → G.Dart)^[i.val] d

def dart_countType : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Nat.card G.Dart = 2 * Nat.card G.edgeSet

def RotationSystemValue : RotationSystemType := @RotationSystem

def orbitMkType := ∀ {V : Type u} {G : SimpleGraph V} (R : RotationSystem G),
  G.Dart → BoundaryOrbit R

def boundaryLength_evenType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V}, G.IsBipartite → ∀ (R : RotationSystem G) (d : G.Dart),
    Even (boundaryLength R d)

def boundary_length_ge_fourType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V}, G.Connected → 3 ≤ Nat.card V → G.IsBipartite →
  ∀ (R : RotationSystem G) (d : G.Dart), 4 ≤ boundaryLength R d

/-- Exact orbit coverage and multiplicity one for directed sides. -/
def boundary_walk_orbitType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (R : RotationSystem G) (d : G.Dart),
  ∃ p : G.Walk d.fst d.fst, p.length = boundaryLength R d ∧ p.darts.Nodup ∧
    ∀ e : G.Dart, e ∈ p.darts ↔ orbitMk R d = orbitMk R e

def side_label_three_boundType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V}, G.Connected → 3 ≤ Nat.card V →
  ∀ {F : Type v} (R : RotationSystem G) (label : G.Dart → F),
    Function.Surjective label → (∀ d, label (successor R d) = label d) →
    3 * Nat.card F ≤ 2 * Nat.card G.edgeSet

def side_label_four_boundType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V}, G.Connected → 3 ≤ Nat.card V → G.IsBipartite →
  ∀ {F : Type v} (R : RotationSystem G) (label : G.Dart → F),
    Function.Surjective label → (∀ d, label (successor R d) = label d) →
    4 * Nat.card F ≤ 2 * Nat.card G.edgeSet

open Specs.FiniteCombinatorics.Graph.Plane.Foundations

def face_frontier_subsetType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G) (F : Face D),
    frontier (faceRegion D F) ⊆ sphereImage D

def face_frontier_nonemptyType : Prop := ∀ {V : Type u} [Finite V] [Nonempty V]
  {G : SimpleGraph V} (D : Drawing G) (F : Face D),
    (frontier (faceRegion D F)).Nonempty

/-- Finiteness concerns the actual complement components, for arbitrary finite
polygonal drawings, including disconnected drawings and isolated vertices. -/
def finite_facesType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G), Finite (Face D)

/-- Oriented area relative to an oriented straight line. -/
def planeDet (a b x : Point) : ℝ :=
  (b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1)

/-- The two open local sides of a straight piece. Their actual faces may coincide. -/
def lineHalfBall (a b x : Point) (r : ℝ) (positive : Bool) : Set Point :=
  Metric.ball x r ∩ {y | if positive then 0 < planeDet a b y else planeDet a b y < 0}

def polygonal_arc_endpoint_locally_segmentType : Prop :=
  ∀ {a b : Point} {s : Set Point}, IsSimplePolygonalArc a b s →
    ∃ (q : Point) (δ : ℝ), q ≠ a ∧ 0 < δ ∧ segment ℝ a q ⊆ s ∧
      s ∩ Metric.ball a δ = segment ℝ a q ∩ Metric.ball a δ

/-- This is an ambient straight-ray model, proved from the drawing, rather
than an intrinsic star homeomorphism or an assumed rotation certificate. -/
def vertex_straight_raysType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G) (v : V),
  ∃ (q : G.neighborSet v → Point) (r : ℝ), 0 < r ∧
    (∀ w, q w ≠ D.point v ∧
      segment ℝ (D.point v) (q w) ⊆ D.edge ⟨s(v, w.val), w.property⟩) ∧
    (∀ w, D.edge ⟨s(v, w.val), w.property⟩ ∩ Metric.ball (D.point v) r =
      segment ℝ (D.point v) (q w) ∩ Metric.ball (D.point v) r) ∧
    planeImage D ∩ Metric.ball (D.point v) r =
      ({D.point v} ∪ ⋃ w, segment ℝ (D.point v) (q w)) ∩ Metric.ball (D.point v) r ∧
    (∀ w z, w ≠ z → ¬ SameRay ℝ (q w - D.point v) (q z - D.point v))

def every_face_has_local_sideType : Prop := ∀ {V : Type u} {G : SimpleGraph V}
  [Finite V] (D : Drawing G), G.edgeSet.Nonempty → ∀ F : Face D,
    ∃ (x a b : Point) (r : ℝ) (p : Bool),
      a ≠ b ∧ 0 < r ∧ planeDet a b x = 0 ∧ x ∉ Set.range D.point ∧
      (∀ y ∈ Metric.ball x r, y ∈ planeImage D ↔ planeDet a b y = 0) ∧
      OnePoint.some '' lineHalfBall a b x r p ⊆ faceRegion D F ∧
      OnePoint.some x ∈ frontier (faceRegion D F)

/-- Angular coordinates in the fixed orientation of the drawing plane. -/
def directionAngle (d : Point) : ℝ := (Complex.equivRealProdCLM.symm d).arg

/-- Increasing angles, followed by wraparound, determine the local turn. -/
def IsAngularTurn {α : Type*} (c : Point) (q : α → Point) (turn : Equiv.Perm α) : Prop := by
  classical
  exact ∃ L : List α, L.Nodup ∧ (∀ a, a ∈ L) ∧
    L.Pairwise (fun a b => directionAngle (q a - c) < directionAngle (q b - c)) ∧
    turn = L.formPerm

/-- A rotation constructed from actual outgoing edge directions. The global
face assignment is a separate conclusion, not a field of these data. -/
def drawing_rotation_geometryType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G), ∃ R : RotationSystem G,
    ∀ v : V, ∃ (q : G.neighborSet v → Point) (r : ℝ), 0 < r ∧
      (∀ w, q w ≠ D.point v ∧
        segment ℝ (D.point v) (q w) ⊆ D.edge ⟨s(v, w.val), w.property⟩) ∧
      (∀ w, D.edge ⟨s(v, w.val), w.property⟩ ∩ Metric.ball (D.point v) r =
        segment ℝ (D.point v) (q w) ∩ Metric.ball (D.point v) r) ∧
      planeImage D ∩ Metric.ball (D.point v) r =
        ({D.point v} ∪ ⋃ w, segment ℝ (D.point v) (q w)) ∩ Metric.ball (D.point v) r ∧
      IsAngularTurn (D.point v) q (R.turn v)

/-- A connected open-angle patch, expressed by its polar parametrization. -/
def angularSector (c : Point) (R α β : ℝ) : Set Point :=
  (fun z : ℝ × ℝ => c + z.1 • (Real.cos z.2, Real.sin z.2)) ''
    (Set.Ioo 0 R ×ˢ Set.Ioo α β)

/-- Lift the next angular coordinate past the first, including a full turn
at a leaf, where the two bounding edge directions coincide. -/
def sectorEndAngle (α β : ℝ) : ℝ := if α < β then β else β + 2 * Real.pi

/-- Actual sector labels exist before proving their compatibility along edges.
This partial construction asserts neither surjectivity nor successor invariance. -/
def drawing_sector_label_existsType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G),
  ∃ (R : RotationSystem G) (label : G.Dart → Face D)
    (q : ∀ v, G.neighborSet v → Point),
    (∀ v, ∃ r : ℝ, 0 < r ∧
      (∀ w, q v w ≠ D.point v ∧
        segment ℝ (D.point v) (q v w) ⊆ D.edge ⟨s(v, w.val), w.property⟩) ∧
      planeImage D ∩ Metric.ball (D.point v) r =
        ({D.point v} ∪ ⋃ w, segment ℝ (D.point v) (q v w)) ∩ Metric.ball (D.point v) r ∧
      IsAngularTurn (D.point v) (q v) (R.turn v)) ∧
    (∀ d : G.Dart,
      let w : G.neighborSet d.snd := ⟨d.fst, d.adj.symm⟩
      let α := directionAngle (q d.snd w - D.point d.snd)
      let β := directionAngle (q d.snd (R.turn d.snd w) - D.point d.snd)
      ∃ r : ℝ, 0 < r ∧
        OnePoint.some '' angularSector (D.point d.snd) r α (sectorEndAngle α β) ⊆
          faceRegion D (label d) ∧
        OnePoint.some (D.point d.snd) ∈ frontier (faceRegion D (label d)))

/-- The complete directed-side construction in W62. Its local
labels are constrained by genuine angular sectors of the actual drawing;
surjectivity and successor invariance are conclusions, not hypotheses. -/
def face_sidesType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G), G.Connected → 3 ≤ Nat.card V →
  ∃ (R : RotationSystem G) (label : G.Dart → Face D)
    (q : ∀ v, G.neighborSet v → Point) (r : V → ℝ),
    (∀ v, 0 < r v ∧
      (∀ w, q v w ≠ D.point v ∧
        segment ℝ (D.point v) (q v w) ⊆ D.edge ⟨s(v, w.val), w.property⟩) ∧
      planeImage D ∩ Metric.ball (D.point v) (r v) =
        ({D.point v} ∪ ⋃ w, segment ℝ (D.point v) (q v w)) ∩
          Metric.ball (D.point v) (r v) ∧
      IsAngularTurn (D.point v) (q v) (R.turn v)) ∧
    (∀ d : G.Dart,
      let w : G.neighborSet d.snd := ⟨d.fst, d.adj.symm⟩
      let α := directionAngle (q d.snd w - D.point d.snd)
      let β := directionAngle (q d.snd (R.turn d.snd w) - D.point d.snd)
      OnePoint.some '' angularSector (D.point d.snd) (r d.snd) α (sectorEndAngle α β) ⊆
        faceRegion D (label d)) ∧
    Function.Surjective label ∧ (∀ d, label (successor R d) = label d) ∧
    (∀ d, 3 ≤ boundaryLength R d ∧
      (G.IsBipartite → Even (boundaryLength R d) ∧ 4 ≤ boundaryLength R d) ∧
      ∃ p : G.Walk d.fst d.fst, p.length = boundaryLength R d ∧ p.darts.Nodup ∧
        ∀ e : G.Dart, e ∈ p.darts ↔ orbitMk R d = orbitMk R e) ∧
    Finite (Face D) ∧ 3 * Nat.card (Face D) ≤ 2 * Nat.card G.edgeSet ∧
      (G.IsBipartite → 4 * Nat.card (Face D) ≤ 2 * Nat.card G.edgeSet)

end FiniteCombinatorics.Graph.Plane.FaceSideAux

namespace FiniteCombinatorics.Graph.Plane

abbrev RotationSystem := @FiniteCombinatorics.Graph.Plane.FaceSideAux.RotationSystem
abbrev sideSuccessor := @FiniteCombinatorics.Graph.Plane.FaceSideAux.successor
abbrev boundaryLength := @FiniteCombinatorics.Graph.Plane.FaceSideAux.boundaryLength
abbrev BoundaryOrbit := @FiniteCombinatorics.Graph.Plane.FaceSideAux.BoundaryOrbit
abbrev boundaryOrbitMk := @FiniteCombinatorics.Graph.Plane.FaceSideAux.orbitMk

variable {V : Type u} {G : SimpleGraph V}

@[simp] theorem sideSuccessor_fst (R : RotationSystem G) (d : G.Dart) :
    (sideSuccessor R d).fst = d.snd := rfl

instance finite_darts [Finite V] : Finite G.Dart :=
  Finite.of_injective SimpleGraph.Dart.toProd SimpleGraph.Dart.toProd_injective

theorem boundaryLength_pos [Finite V] (R : RotationSystem G) (d : G.Dart) :
    0 < boundaryLength R d :=
  Function.minimalPeriod_pos_of_mem_periodicPts ((sideSuccessor R).injective.mem_periodicPts d)

theorem sideSuccessor_ne (R : RotationSystem G) (d : G.Dart) : sideSuccessor R d ≠ d := by
  intro h
  have he := congrArg (fun e : G.Dart => e.fst) h
  exact d.snd_ne_fst he

/-- A fixed neighbor in a cyclic order is its only element. -/
theorem rotation_fixed_neighbor (R : RotationSystem G) (v : V)
    (w : G.neighborSet v) (hw : R.turn v w = w) (z : G.neighborSet v) : z = w := by
  exact ((R.cyclic v).2 (Set.mem_univ w) (Set.mem_univ z)).eq_of_left hw |>.symm

/-- Two adjacent leaves are an entire connected component. -/
theorem reachable_two_leaves {a b : V}
    (ha : ∀ z, G.Adj a z → z = b) (hb : ∀ z, G.Adj b z → z = a)
    {z : V} (hz : G.Reachable a z) : z = a ∨ z = b := by
  obtain ⟨p⟩ := hz
  suffices h : ∀ {x y : V} (p : G.Walk x y), x = a ∨ x = b → y = a ∨ y = b by
    exact h p (Or.inl rfl)
  intro x y p
  induction p with
  | nil => exact id
  | @cons x t y hxt q ih =>
    rintro (rfl | rfl)
    · exact ih (Or.inr (ha t hxt))
    · exact ih (Or.inl (hb t hxt))

/-- A period-two face tracing would force both endpoints to be leaves. -/
theorem sideSuccessor_two_leaves (R : RotationSystem G) (d : G.Dart)
    (h : sideSuccessor R (sideSuccessor R d) = d) :
    (∀ z, G.Adj d.fst z → z = d.snd) ∧
      (∀ z, G.Adj d.snd z → z = d.fst) := by
  have he : sideSuccessor R d = d.symm := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · rfl
    · exact congrArg (fun e : G.Dart => e.fst) h
  have he' : sideSuccessor R d.symm = d := by simpa [he] using h
  have fixed_b : R.turn d.snd ⟨d.fst, d.adj.symm⟩ = ⟨d.fst, d.adj.symm⟩ := by
    apply Subtype.ext
    exact congrArg (fun e : G.Dart => e.snd) he
  have fixed_a : R.turn d.fst ⟨d.snd, d.adj⟩ = ⟨d.snd, d.adj⟩ := by
    apply Subtype.ext
    exact congrArg (fun e : G.Dart => e.snd) he'
  constructor
  · intro z hz
    exact congrArg Subtype.val (rotation_fixed_neighbor R d.fst _ fixed_a ⟨z, hz⟩)
  · intro z hz
    exact congrArg Subtype.val (rotation_fixed_neighbor R d.snd _ fixed_b ⟨z, hz⟩)

theorem boundary_length_ge_three :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.boundary_length_ge_threeType := by
  intro V _ G hc hv R d
  change 3 ≤ boundaryLength R d
  have hp := boundaryLength_pos R d
  have hret := Function.iterate_minimalPeriod (f := (sideSuccessor R : G.Dart → G.Dart)) (x := d)
  change (sideSuccessor R : G.Dart → G.Dart)^[boundaryLength R d] d = d at hret
  by_contra h
  have hl : boundaryLength R d = 1 ∨ boundaryLength R d = 2 := by omega
  rcases hl with hl | hl
  · rw [hl] at hret
    exact sideSuccessor_ne R d hret
  · rw [hl] at hret
    obtain ⟨ha, hb⟩ := sideSuccessor_two_leaves R d hret
    have hall : ∀ z : V, z = d.fst ∨ z = d.snd := fun z =>
      reachable_two_leaves ha hb (hc.preconnected d.fst z)
    classical
    let := Fintype.ofFinite V
    have hcard : Fintype.card V ≤ 2 := by
      have hsub : (Finset.univ : Finset V) ⊆ {d.fst, d.snd} := by
        intro z _
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hall z
      simpa [Finset.card_pair d.fst_ne_snd] using Finset.card_le_card hsub
    rw [Nat.card_eq_fintype_card] at hv
    omega

/-- The first n sides in the successor trajectory, as an actual graph walk. -/
def successorWalk (R : RotationSystem G) (d : G.Dart) :
    (n : ℕ) → G.Walk d.fst (((sideSuccessor R : G.Dart → G.Dart)^[n] d).fst)
  | 0 => .nil
  | n + 1 => ((successorWalk R d n).concat
      (((sideSuccessor R : G.Dart → G.Dart)^[n] d).adj)).copy rfl (by
        rw [Function.iterate_succ_apply']
        rfl)

@[simp] theorem successorWalk_length (R : RotationSystem G) (d : G.Dart) (n : ℕ) :
    (successorWalk R d n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [successorWalk, SimpleGraph.Walk.length_copy,
      SimpleGraph.Walk.length_concat, ih]

theorem successorWalk_darts (R : RotationSystem G) (d : G.Dart) (n : ℕ) :
    (successorWalk R d n).darts =
      (List.range n).map (fun i => (sideSuccessor R : G.Dart → G.Dart)^[i] d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [successorWalk, SimpleGraph.Walk.darts_copy,
      SimpleGraph.Walk.darts_concat, ih, List.range_succ, List.map_append, List.map_singleton, List.concat_eq_append]

def boundaryWalk [Finite V] (R : RotationSystem G) (d : G.Dart) : G.Walk d.fst d.fst :=
  (successorWalk R d (boundaryLength R d)).copy rfl
    (congrArg (fun e : G.Dart => e.fst) Function.iterate_minimalPeriod)

@[simp] theorem boundaryWalk_length [Finite V] (R : RotationSystem G) (d : G.Dart) :
    (boundaryWalk R d).length = boundaryLength R d := by
  simp [boundaryWalk]

theorem boundary_closed_walk :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.boundary_closed_walkType := by
  intro V _ G R d
  refine ⟨boundaryWalk R d, boundaryWalk_length R d, ?_⟩
  intro i
  simp [boundaryWalk, successorWalk_darts]

/-- Two-coloring forces even length for these walks, including repeated edges. -/
theorem boundaryLength_even :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.boundaryLength_evenType := by
  intro V _ G hb R d
  change Even (boundaryLength R d)
  obtain ⟨c⟩ := hb
  have he := Coloring.two_coloring_walk_parity c (boundaryWalk R d)
  have hv := (c d.fst).isLt
  rw [boundaryWalk_length] at he
  rw [even_iff_two_dvd]
  omega

theorem boundary_length_ge_four :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.boundary_length_ge_fourType := by
  intro V _ G hc hv hb R d
  change 4 ≤ boundaryLength R d
  have h3 : 3 ≤ boundaryLength R d := boundary_length_ge_three hc hv R d
  have he : Even (boundaryLength R d) := boundaryLength_even hb R d
  rw [even_iff_two_dvd] at he
  omega

theorem dart_count : FiniteCombinatorics.Graph.Plane.FaceSideAux.dart_countType := by
  intro V _ G
  classical
  let := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    G.card_edgeSet, G.dart_card_eq_twice_card_edges]

/-- No directed side is repeated before the least return time. Undirected edges
may be repeated, as is necessary at bridges. -/
theorem boundaryWalk_darts_nodup [Finite V] (R : RotationSystem G) (d : G.Dart) :
    (boundaryWalk R d).darts.Nodup := by
  rw [boundaryWalk, SimpleGraph.Walk.darts_copy, successorWalk_darts]
  apply List.nodup_range.map_on
  intro i hi j hj he
  exact Function.iterate_injOn_Iio_minimalPeriod
    (List.mem_range.mp hi) (List.mem_range.mp hj) he

/-- An invariant labeling is constant along every finite trajectory. -/
theorem side_label_iterate {F : Type*} (R : RotationSystem G) (label : G.Dart → F)
    (hinv : ∀ d, label (sideSuccessor R d) = label d) (d : G.Dart) (n : ℕ) :
    label ((sideSuccessor R : G.Dart → G.Dart)^[n] d) = label d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hinv, ih]

/-- An orbit of length m supplies m distinct sides of its assigned face. -/
theorem boundaryLength_le_fiber_card [Finite V] {F : Type*}
    (R : RotationSystem G) (label : G.Dart → F)
    (hinv : ∀ d, label (sideSuccessor R d) = label d) (d : G.Dart) :
    boundaryLength R d ≤ Nat.card {e : G.Dart // label e = label d} := by
  let f : Fin (boundaryLength R d) → {e : G.Dart // label e = label d} :=
    fun i => ⟨(sideSuccessor R : G.Dart → G.Dart)^[i.val] d,
      side_label_iterate R label hinv d i.val⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt
      (congrArg Subtype.val he)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- Pure counting, conditional on an actual surjective side assignment. -/
theorem side_label_count [Finite V] {F : Type*} (R : RotationSystem G)
    (label : G.Dart → F) (hsurj : Function.Surjective label)
    (hinv : ∀ d, label (sideSuccessor R d) = label d)
    (k : ℕ) (hk : ∀ d, k ≤ boundaryLength R d) :
    k * Nat.card F ≤ 2 * Nat.card G.edgeSet := by
  classical
  let : Finite F := Finite.of_surjective label hsurj
  let := Fintype.ofFinite F
  have hf (a : F) : k ≤ Nat.card {e : G.Dart // label e = a} := by
    obtain ⟨d, rfl⟩ := hsurj a
    exact (hk d).trans (boundaryLength_le_fiber_card R label hinv d)
  calc
    k * Nat.card F = ∑ _a : F, k := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]
    _ ≤ ∑ a : F, Nat.card {e : G.Dart // label e = a} :=
      Finset.sum_le_sum (fun a _ => hf a)
    _ = Nat.card (Σ a : F, {e : G.Dart // label e = a}) := Nat.card_sigma.symm
    _ = Nat.card G.Dart := Nat.card_congr (Equiv.sigmaFiberEquiv label)
    _ = 2 * Nat.card G.edgeSet := dart_count G

theorem side_label_three_bound :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.side_label_three_boundType := by
  intro V _ G hc hv F R label hsurj hinv
  exact side_label_count R label hsurj hinv 3 (boundary_length_ge_three hc hv R)

theorem side_label_four_bound :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.side_label_four_boundType := by
  intro V _ G hc hv hb F R label hsurj hinv
  exact side_label_count R label hsurj hinv 4 (boundary_length_ge_four hc hv hb R)

instance finite_boundary_orbits [Finite V] (R : RotationSystem G) : Finite (BoundaryOrbit R) :=
  Quotient.finite _

theorem boundaryOrbitMk_eq_iff (R : RotationSystem G) (d e : G.Dart) :
    boundaryOrbitMk R d = boundaryOrbitMk R e ↔ (sideSuccessor R).SameCycle d e :=
  Quotient.eq

theorem boundaryOrbitMk_surjective (R : RotationSystem G) :
    Function.Surjective (boundaryOrbitMk R) := Quotient.mk_surjective

/-- The exact list of sides traversed by the orbit through d. -/
theorem mem_boundaryWalk_darts_iff [Finite V] (R : RotationSystem G) (d e : G.Dart) :
    e ∈ (boundaryWalk R d).darts ↔ (sideSuccessor R).SameCycle d e := by
  rw [boundaryWalk, SimpleGraph.Walk.darts_copy, successorWalk_darts]
  constructor
  · rintro he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    have h : (sideSuccessor R).SameCycle d ((sideSuccessor R ^ i) d) :=
      Equiv.Perm.SameCycle.rfl.pow_right
    simpa only [Equiv.Perm.coe_pow] using h
  · intro he
    obtain ⟨i, hi⟩ := he.exists_nat_pow_eq
    have hpos := boundaryLength_pos R d
    have hmod : (sideSuccessor R : G.Dart → G.Dart)^[i % boundaryLength R d] d = e := by
      change (sideSuccessor R : G.Dart → G.Dart)^[i %
        Function.minimalPeriod (sideSuccessor R) d] d = e
      rw [Function.iterate_mod_minimalPeriod_eq]
      simpa only [Equiv.Perm.coe_pow] using hi
    exact List.mem_map.mpr ⟨i % boundaryLength R d,
      List.mem_range.mpr (Nat.mod_lt _ hpos), hmod⟩

theorem boundary_walk_orbit :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.boundary_walk_orbitType := by
  intro V _ G R d
  refine ⟨boundaryWalk R d, boundaryWalk_length R d, boundaryWalk_darts_nodup R d, ?_⟩
  intro e
  exact (mem_boundaryWalk_darts_iff R d e).trans (boundaryOrbitMk_eq_iff R d e).symm

/-- Invariant side labels descend to boundary-walk orbits. -/
def orbitLabel [Finite V] {F : Type*} (R : RotationSystem G) (label : G.Dart → F)
    (hinv : ∀ d, label (sideSuccessor R d) = label d) : BoundaryOrbit R → F :=
  Quotient.lift label (by
    intro d e he
    obtain ⟨i, hi⟩ := he.exists_nat_pow_eq
    have hi' : (sideSuccessor R : G.Dart → G.Dart)^[i] d = e := by
      simpa only [Equiv.Perm.coe_pow] using hi
    rw [← hi']
    exact (side_label_iterate R label hinv d i).symm)

@[simp] theorem orbitLabel_mk [Finite V] {F : Type*} (R : RotationSystem G)
    (label : G.Dart → F) (hinv : ∀ d, label (sideSuccessor R d) = label d) (d : G.Dart) :
    orbitLabel R label hinv (boundaryOrbitMk R d) = label d := rfl

theorem orbitLabel_surjective [Finite V] {F : Type*} (R : RotationSystem G)
    (label : G.Dart → F) (hinv : ∀ d, label (sideSuccessor R d) = label d)
    (hsurj : Function.Surjective label) : Function.Surjective (orbitLabel R label hinv) := by
  intro f
  obtain ⟨d, rfl⟩ := hsurj f
  exact ⟨boundaryOrbitMk R d, rfl⟩

section ActualFaces
variable [Finite V] (D : PlaneEmbedding G)

lemma faceRegion_mem_iff (F : Face D) (x : SphereComplement D) :
    x.val ∈ faceRegion D F ↔ ConnectedComponents.mk x = F := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Subtype.ext he : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma faceRegion_preimage (F : Face D) :
    (Subtype.val : SphereComplement D → Sphere) ⁻¹' faceRegion D F =
      ConnectedComponents.mk ⁻¹' {F} := by
  ext x
  exact faceRegion_mem_iff D F x

lemma face_region_open (F : Face D) : _root_.IsOpen (faceRegion D F) := by
  have := sphere_complement_locally_path_connected D
  exact (sphere_complement_open D).isOpenMap_subtype_val _
    (ConnectedComponents.continuous_coe.isOpen_preimage {F} (isOpen_discrete _))

/-- A connected complementary patch that meets a face belongs entirely to it.
This applies to ambient sectors and edge-side neighborhoods, regardless of the
topology of the whole face. -/
theorem preconnected_subset_faceRegion {C : Set Sphere} (hC : IsPreconnected C)
    (hsub : C ⊆ (sphereImage D)ᶜ) (F : Face D)
    (hmeet : (C ∩ faceRegion D F).Nonempty) : C ⊆ faceRegion D F := by
  obtain ⟨x, hxC, hxF⟩ := hmeet
  let y : SphereComplement D := ⟨x, hsub hxC⟩
  have hy : ConnectedComponents.mk y = F := (faceRegion_mem_iff D F y).mp hxF
  have heq : faceRegion D F = connectedComponentIn (sphereImage D)ᶜ y.val :=
    (congrArg (faceRegion D) hy).symm.trans (face_region_component D y)
  exact heq.symm ▸ hC.subset_connectedComponentIn hxC hsub

/-- Every nonempty connected complementary patch selects exactly one actual
face; no cell structure is imposed on that face. -/
theorem existsUnique_face_of_preconnected {C : Set Sphere} (hC : IsConnected C)
    (hsub : C ⊆ (sphereImage D)ᶜ) : ∃! F : Face D, C ⊆ faceRegion D F := by
  obtain ⟨x, hxC⟩ := hC.nonempty
  let y : SphereComplement D := ⟨x, hsub hxC⟩
  refine ⟨ConnectedComponents.mk y, ?_, ?_⟩
  · change C ⊆ faceRegion D (ConnectedComponents.mk y)
    have heq : faceRegion D (ConnectedComponents.mk y) =
        connectedComponentIn (sphereImage D)ᶜ y.val := face_region_component D y
    exact heq.symm ▸
      hC.isPreconnected.subset_connectedComponentIn hxC hsub
  · intro F hF
    exact ((faceRegion_mem_iff D F y).mp (hF hxC)).symm

/-- A face approaching a point meets a whole complementary patch from any
preconnected local cover. This is the topological step in passing from local
edge sides or vertex sectors to actual faces. -/
theorem face_contains_local_patch {ι : Type*} (F : Face D) {p : Sphere}
    (hp : p ∈ closure (faceRegion D F)) {U : Set Sphere} (hU : U ∈ nhds p)
    (C : ι → Set Sphere) (hC : ∀ i, IsPreconnected (C i))
    (hsub : ∀ i, C i ⊆ (sphereImage D)ᶜ)
    (hcover : U ∩ (sphereImage D)ᶜ ⊆ ⋃ i, C i) :
    ∃ i, (C i).Nonempty ∧ C i ⊆ faceRegion D F := by
  obtain ⟨x, hxU, hxF⟩ := mem_closure_iff_nhds.mp hp U hU
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover ⟨hxU, face_region_subset D F hxF⟩)
  exact ⟨i, ⟨x, hxi⟩, preconnected_subset_faceRegion D (hC i) (hsub i) F ⟨x, hxi, hxF⟩⟩

/-- The planar version lets straight halfplanes and sectors be used directly. -/
theorem preconnected_plane_patch_subset_faceRegion {C : Set Point}
    (hC : IsPreconnected C) (hsub : C ⊆ (planeImage D)ᶜ) (F : Face D)
    (hmeet : (C ∩ OnePoint.some ⁻¹' faceRegion D F).Nonempty) :
    OnePoint.some '' C ⊆ faceRegion D F := by
  apply preconnected_subset_faceRegion D (hC.image _ OnePoint.continuous_coe.continuousOn)
  · rintro _ ⟨x, hx, rfl⟩ hximage
    exact hsub hx ((sphere_image_membership D x).mp hximage)
  · obtain ⟨x, hxC, hxF⟩ := hmeet
    exact ⟨OnePoint.some x, ⟨x, hxC, rfl⟩, hxF⟩

/-- A face has no frontier inside the open complement: its frontier lies on
actual drawn vertices and edges. -/
theorem face_frontier_subset_image (F : Face D) :
    frontier (faceRegion D F) ⊆ sphereImage D := by
  have := sphere_complement_locally_path_connected D
  intro x hx
  by_contra hn
  let y : SphereComplement D := ⟨x, hn⟩
  have hpre : _root_.IsClosed ((Subtype.val : SphereComplement D → Sphere) ⁻¹' faceRegion D F) := by
    rw [faceRegion_preimage]
    exact isClosed_singleton.preimage ConnectedComponents.continuous_coe
  have hcl : IsClopen ((Subtype.val : SphereComplement D → Sphere) ⁻¹' faceRegion D F) :=
    ⟨hpre, (face_region_open D F).preimage continuous_subtype_val⟩
  have hmem := (sphere_complement_open D).isOpenMap_subtype_val.preimage_frontier_subset_frontier_preimage (show y ∈
      (Subtype.val : SphereComplement D → Sphere) ⁻¹' frontier (faceRegion D F) from hx)
  rw [hcl.frontier_eq] at hmem
  exact hmem

/-- Every face of a nonempty drawing has nonempty boundary. This uses ambient
connectedness, without assuming the face is a disk. -/
theorem face_frontier_nonempty_of_nonempty [Nonempty V] (F : Face D) :
    (frontier (faceRegion D F)).Nonempty := by
  apply nonempty_frontier_iff.mpr
  refine ⟨(face_region_connected D F).nonempty, ?_⟩
  intro he
  let v : V := Classical.choice inferInstance
  have hm : OnePoint.some (D.point v) ∈ sphereImage D :=
    ⟨D.point v, Or.inl (Set.mem_range_self v), rfl⟩
  have hf : OnePoint.some (D.point v) ∈ faceRegion D F := he.symm ▸ Set.mem_univ _
  exact face_region_subset D F hf hm

/-- Once the geometric side assignment is established, the actual face bounds
follow from the general counting lemmas. The premises are not supplied here. -/
theorem face_bounds_of_assignment (hc : G.Connected) (hv : 3 ≤ Nat.card V)
    (R : RotationSystem G) (label : G.Dart → Face D)
    (hsurj : Function.Surjective label)
    (hinv : ∀ d, label (sideSuccessor R d) = label d) :
    Finite (Face D) ∧ 3 * Nat.card (Face D) ≤ 2 * Nat.card G.edgeSet ∧
      (G.IsBipartite → 4 * Nat.card (Face D) ≤ 2 * Nat.card G.edgeSet) := by
  exact ⟨Finite.of_surjective label hsurj,
    side_label_three_bound hc hv R label hsurj hinv,
    fun hb => side_label_four_bound hc hv hb R label hsurj hinv⟩
end ActualFaces

theorem face_frontier_subset :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.face_frontier_subsetType := by
  intro V _ G D F
  exact face_frontier_subset_image D F

theorem face_frontier_nonempty :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.face_frontier_nonemptyType := by
  intro V _ _ G D F
  exact face_frontier_nonempty_of_nonempty D F

/-- A finite preconnected cover suffices for finiteness of actual components;
the pieces need not be disjoint, closed, or cells. -/
theorem finite_components_of_finite_preconnected_cover
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Finite ι]
    (C : ι → Set X) (hC : ∀ i, IsPreconnected (C i))
    (hcover : ∀ x, ∃ i, x ∈ C i) : Finite (ConnectedComponents X) := by
  classical
  let I := {i : ι // (C i).Nonempty}
  let x (i : I) : X := i.property.choose
  have hx (i : I) : x i ∈ C i.val := i.property.choose_spec
  let f (i : I) : ConnectedComponents X := ConnectedComponents.mk (x i)
  apply Finite.of_surjective f
  intro F
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe F
  obtain ⟨i, hi⟩ := hcover y
  let j : I := ⟨i, y, hi⟩
  refine ⟨j, ConnectedComponents.coe_eq_coe'.mpr ?_⟩
  exact (hC i).subset_connectedComponent hi (hx j)

/-- Collinearity and coordinate bounds characterize a planar closed segment,
including vertical and degenerate segments. -/
theorem mem_plane_segment_iff (a b x : Point) : x ∈ segment ℝ a b ↔
    min a.1 b.1 ≤ x.1 ∧ x.1 ≤ max a.1 b.1 ∧
    min a.2 b.2 ≤ x.2 ∧ x.2 ≤ max a.2 b.2 ∧
    (b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1) = 0 := by
  constructor
  · rw [segment_eq_image]
    rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have hmin1 := min_le_left a.1 b.1
    have hmin2 := min_le_right a.1 b.1
    have hmax1 := le_max_left a.1 b.1
    have hmax2 := le_max_right a.1 b.1
    have hmin3 := min_le_left a.2 b.2
    have hmin4 := min_le_right a.2 b.2
    have hmax3 := le_max_left a.2 b.2
    have hmax4 := le_max_right a.2 b.2
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by ring⟩
  · rintro ⟨hx0, hx1, hy0, hy1, he⟩
    have along_first (a b x : Point) (hab : a.1 < b.1)
        (hx0 : a.1 ≤ x.1) (hx1 : x.1 ≤ b.1)
        (he : (b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1) = 0) :
        x ∈ segment ℝ a b := by
      have hd : 0 < b.1 - a.1 := sub_pos.mpr hab
      rw [segment_eq_image]
      refine ⟨(x.1 - a.1) / (b.1 - a.1),
        ⟨div_nonneg (sub_nonneg.mpr hx0) hd.le,
          (div_le_one hd).mpr (by linarith)⟩, ?_⟩
      apply Prod.ext <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      · field_simp
        nlinarith
      · field_simp
        nlinarith
    rcases lt_trichotomy a.1 b.1 with hab | hab | hab
    · exact along_first a b x hab (by simpa [min_eq_left hab.le] using hx0)
        (by simpa [max_eq_right hab.le] using hx1) he
    · have hxx : x.1 = a.1 := by
        simp only [hab, min_self, max_self] at hx0 hx1
        exact (le_antisymm hx1 hx0).trans hab.symm
      rcases lt_trichotomy a.2 b.2 with haby | haby | haby
      · have hd : 0 < b.2 - a.2 := sub_pos.mpr haby
        have hy0' : a.2 ≤ x.2 := by simpa [min_eq_left haby.le] using hy0
        have hy1' : x.2 ≤ b.2 := by simpa [max_eq_right haby.le] using hy1
        rw [segment_eq_image]
        refine ⟨(x.2 - a.2) / (b.2 - a.2),
          ⟨div_nonneg (sub_nonneg.mpr hy0') hd.le,
            (div_le_one hd).mpr (by linarith)⟩, ?_⟩
        apply Prod.ext <;>
          simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        · rw [← hab, hxx]; ring
        · field_simp
          nlinarith
      · have hyy : x.2 = a.2 := by
          simp only [haby, min_self, max_self] at hy0 hy1
          exact (le_antisymm hy1 hy0).trans haby.symm
        have hxa : x = a := Prod.ext hxx hyy
        exact hxa ▸ left_mem_segment ℝ a b
      · have hd : 0 < a.2 - b.2 := sub_pos.mpr haby
        have hy0' : b.2 ≤ x.2 := by simpa [min_eq_right haby.le] using hy0
        have hy1' : x.2 ≤ a.2 := by simpa [max_eq_left haby.le] using hy1
        rw [segment_symm, segment_eq_image]
        refine ⟨(x.2 - b.2) / (a.2 - b.2),
          ⟨div_nonneg (sub_nonneg.mpr hy0') hd.le,
            (div_le_one hd).mpr (by linarith)⟩, ?_⟩
        apply Prod.ext <;>
          simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        · rw [← hab, hxx]; ring
        · field_simp
          nlinarith
    · rw [segment_symm]
      apply along_first b a x hab
      · simpa [min_eq_right hab.le] using hx0
      · simpa [max_eq_left hab.le] using hx1
      · nlinarith [he]

/-- The complement of a planar segment is the union of six convex open
halfplanes. The coordinate bounds also cover the degenerate-segment case. -/
theorem plane_segment_compl_convex_cover (a b : Point) :
    ∃ C : Fin 6 → Set Point, (∀ i, Convex ℝ (C i)) ∧
      (segment ℝ a b)ᶜ = ⋃ i, C i := by
  let det : Point → ℝ := fun x =>
    (b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1)
  let C : Fin 6 → Set Point := ![
    {x | x.1 < min a.1 b.1}, {x | max a.1 b.1 < x.1},
    {x | x.2 < min a.2 b.2}, {x | max a.2 b.2 < x.2},
    {x | det x < 0}, {x | 0 < det x}]
  refine ⟨C, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact convex_halfSpace_lt (LinearMap.fst ℝ ℝ ℝ).isLinear _
    · exact convex_halfSpace_gt (LinearMap.fst ℝ ℝ ℝ).isLinear _
    · exact convex_halfSpace_lt (LinearMap.snd ℝ ℝ ℝ).isLinear _
    · exact convex_halfSpace_gt (LinearMap.snd ℝ ℝ ℝ).isLinear _
    · intro x hx y hy r t hr ht hrt
      change det x < 0 at hx
      change det y < 0 at hy
      change det (r • x + t • y) < 0
      have hd : det (r • x + t • y) = r * det x + t * det y := by
        have ht' : t = 1 - r := by linarith
        rw [ht']
        dsimp [det]
        ring
      rw [hd]
      by_cases hr0 : r = 0
      · have ht1 : t = 1 := by linarith
        simpa [hr0, ht1] using hy
      · exact add_neg_of_neg_of_nonpos
          (mul_neg_of_pos_of_neg (lt_of_le_of_ne hr (Ne.symm hr0)) hx)
          (mul_nonpos_of_nonneg_of_nonpos ht hy.le)
    · intro x hx y hy r t hr ht hrt
      change 0 < det x at hx
      change 0 < det y at hy
      change 0 < det (r • x + t • y)
      have hd : det (r • x + t • y) = r * det x + t * det y := by
        have ht' : t = 1 - r := by linarith
        rw [ht']
        dsimp [det]
        ring
      rw [hd]
      have hh : 0 < r * det x + t * det y := by
        by_cases hr0 : r = 0
        · have ht1 : t = 1 := by linarith
          simpa [hr0, ht1] using hy
        · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hr (Ne.symm hr0)) hx)
            (mul_nonneg ht hy.le)
      exact hh
  · ext x
    simp only [Set.mem_compl_iff, mem_plane_segment_iff, Set.mem_iUnion]
    constructor
    · intro hx
      by_cases h0 : x.1 < min a.1 b.1
      · exact ⟨0, h0⟩
      by_cases h1 : max a.1 b.1 < x.1
      · exact ⟨1, h1⟩
      by_cases h2 : x.2 < min a.2 b.2
      · exact ⟨2, h2⟩
      by_cases h3 : max a.2 b.2 < x.2
      · exact ⟨3, h3⟩
      have hne : det x ≠ 0 := by
        intro he
        exact hx ⟨le_of_not_gt h0, le_of_not_gt h1, le_of_not_gt h2,
          le_of_not_gt h3, he⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨4, h⟩
      · exact ⟨5, h⟩
    · rintro ⟨i, hi⟩ ⟨h0, h1, h2, h3, he⟩
      fin_cases i
      · exact (not_lt_of_ge h0) hi
      · exact (not_lt_of_ge h1) hi
      · exact (not_lt_of_ge h2) hi
      · exact (not_lt_of_ge h3) hi
      · change det x < 0 at hi
        exact (ne_of_lt hi) he
      · change 0 < det x at hi
        exact (ne_of_gt hi) he

/-- No general-position assumption is needed for a finite segment arrangement. -/
theorem finite_components_compl_segments {ι : Type*} [Finite ι]
    (a b : ι → Point) :
    Finite (ConnectedComponents ↥(⋃ i, segment ℝ (a i) (b i))ᶜ) := by
  classical
  choose C hC hcover using fun i => plane_segment_compl_convex_cover (a i) (b i)
  let S : Set Point := (⋃ i, segment ℝ (a i) (b i))ᶜ
  let T (f : ι → Fin 6) : Set Point := ⋂ i, C i (f i)
  have hT (f : ι → Fin 6) : Convex ℝ (T f) := convex_iInter (fun i => hC i (f i))
  have hTS (f : ι → Fin 6) : T f ⊆ S := by
    intro x hx hxs
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxs
    have hc : x ∈ (segment ℝ (a i) (b i))ᶜ := by
      rw [hcover i]
      exact Set.mem_iUnion.mpr ⟨f i, Set.mem_iInter.mp hx i⟩
    exact hc hi
  let U (f : ι → Fin 6) : Set S := Subtype.val ⁻¹' T f
  apply finite_components_of_finite_preconnected_cover U
  · intro f
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.mpr (hTS f)]
    exact (hT f).isPreconnected
  · intro x
    have hx (i : ι) : x.val ∈ (segment ℝ (a i) (b i))ᶜ := by
      intro hi
      exact x.property (Set.mem_iUnion.mpr ⟨i, hi⟩)
    have hchoice (i : ι) : ∃ j : Fin 6, x.val ∈ C i j := by
      simpa only [hcover i, Set.mem_iUnion] using hx i
    choose f hf using hchoice
    exact ⟨f, Set.mem_iInter.mpr hf⟩

/-- Polygonality, including isolated vertices, gives finitely many plane faces. -/
theorem finite_plane_faces [Finite V] (D : PlaneEmbedding G) : Finite (PlaneFace D) := by
  classical
  choose n a b hseg using edge_polygonal D
  let I := V ⊕ (Σ e : G.edgeSet, Fin (n e))
  let A : I → Point := Sum.elim D.point (fun i => a i.1 i.2)
  let B : I → Point := Sum.elim D.point (fun i => b i.1 i.2)
  have heq : planeImage D = ⋃ i, segment ℝ (A i) (B i) := by
    ext x
    change x ∈ Set.range D.point ∪ (⋃ e, D.edge e) ↔ _
    simp only [Set.mem_union, Set.mem_range, Set.mem_iUnion]
    constructor
    · rintro (⟨v, rfl⟩ | ⟨e, hx⟩)
      · exact ⟨Sum.inl v, left_mem_segment ℝ _ _⟩
      · rw [hseg e] at hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨e, i⟩, hi⟩
    · rintro ⟨v | ⟨e, i⟩, hx⟩
      · have : x = D.point v := by simpa [A, B] using hx
        exact Or.inl ⟨v, this.symm⟩
      · exact Or.inr ⟨e, (hseg e) ▸ Set.mem_iUnion.mpr ⟨i, hx⟩⟩
  change Finite (ConnectedComponents ↥(planeImage D)ᶜ)
  rw [heq]
  exact finite_components_compl_segments A B

/-- Actual sphere-complement faces are finite, without connectivity or a disk
condition on any face. -/
theorem finite_faces :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.finite_facesType := by
  intro V _ G D
  have := finite_plane_faces D
  obtain ⟨E, _⟩ := plane_sphere_faces D
  exact Finite.of_equiv (PlaneFace D) E

/-- A nonempty planar open set with infinite complement has infinite boundary:
a finite boundary could not separate the plane. -/
theorem infinite_frontier_of_open_of_infinite_compl {U : Set Point}
    (hopen : _root_.IsOpen U) (hne : U.Nonempty) (hinf : Uᶜ.Infinite) :
    (frontier U).Infinite := by
  intro hf
  have hc : IsConnected (frontier U)ᶜ :=
    hf.countable.isConnected_compl_of_one_lt_rank (by norm_num [Point])
  have : PreconnectedSpace ↥(frontier U)ᶜ := Subtype.preconnectedSpace hc.isPreconnected
  have hcl : IsClopen ((Subtype.val : ↥(frontier U)ᶜ → Point) ⁻¹' U) :=
    isClopen_preimage_val hopen disjoint_compl_right
  obtain ⟨x, hx⟩ := hne
  have hxf : x ∉ frontier U :=
    (mem_interior_iff_notMem_frontier hx).mp (hopen.interior_eq.symm ▸ hx)
  have hall := hcl.eq_univ ⟨⟨x, hxf⟩, hx⟩
  apply hinf
  apply hf.subset
  intro y hy
  by_contra hyf
  have hm : (⟨y, hyf⟩ : ↥(frontier U)ᶜ) ∈
      (Subtype.val : ↥(frontier U)ᶜ → Point) ⁻¹' U := hall.symm ▸ Set.mem_univ _
  exact hy hm

/-- Each genuine geometric edge is infinite; parametrization speed is irrelevant. -/
theorem edge_infinite [Finite V] (D : PlaneEmbedding G) (e : G.edgeSet) :
    (D.edge e).Infinite := by
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.val
  have h : G.Adj a b := by simpa [← hab] using e.property
  have he : e = ⟨s(a, b), h⟩ := Subtype.ext hab.symm
  rw [he]
  obtain ⟨_, p, hp, hps⟩ := D.edge_arc a b h
  have : Infinite unitInterval := Set.Icc.infinite (by norm_num : (0 : ℝ) < 1)
  rw [← hps]
  exact Set.infinite_range_of_injective hp

/-- Every actual face of a drawing with an edge has infinite frontier. This
allows all vertices and all finitely many polygonal corners to be avoided. -/
theorem face_frontier_infinite [Finite V] (D : PlaneEmbedding G)
    (he : G.edgeSet.Nonempty) (F : Face D) : (frontier (faceRegion D F)).Infinite := by
  let U : Set Point := OnePoint.some ⁻¹' faceRegion D F
  have hopen : _root_.IsOpen U := (face_region_open D F).preimage OnePoint.continuous_coe
  have hne : U.Nonempty := by
    exact OnePoint.denseRange_coe.exists_mem_open
      (face_region_open D F) (face_region_connected D F).nonempty
  have hdisj : planeImage D ⊆ Uᶜ := by
    intro x hx hF
    exact face_region_subset D F hF ⟨x, hx, rfl⟩
  have hinf : Uᶜ.Infinite := by
    obtain ⟨e, he⟩ := he
    exact (edge_infinite D ⟨e, he⟩).mono (fun x hx =>
      hdisj (Or.inr (Set.mem_iUnion.mpr ⟨⟨e, he⟩, hx⟩)))
  have hfront : OnePoint.some ⁻¹' frontier (faceRegion D F) = frontier U :=
    OnePoint.isOpenEmbedding_coe.isOpenMap.preimage_frontier_eq_frontier_preimage
      OnePoint.continuous_coe _
  intro hf
  apply infinite_frontier_of_open_of_infinite_compl hopen hne hinf
  rw [← hfront]
  exact hf.preimage OnePoint.coe_injective.injOn

/-- An actual face reaches an edge away from every vertex. -/
theorem face_frontier_edge_point [Finite V] (D : PlaneEmbedding G)
    (he : G.edgeSet.Nonempty) (F : Face D) :
    ∃ (e : G.edgeSet) (x : Point), OnePoint.some x ∈ frontier (faceRegion D F) ∧
      x ∈ D.edge e ∧ x ∉ Set.range D.point := by
  have hi := face_frontier_infinite D he F
  have hv : (OnePoint.some '' Set.range D.point : Set Sphere).Finite :=
    (Set.finite_range D.point).image _
  obtain ⟨z, hz, hzn⟩ := (hi.sdiff hv).nonempty
  obtain ⟨x, hx, rfl⟩ := face_frontier_subset_image D F hz
  have hxv : x ∉ Set.range D.point := fun hxv => hzn ⟨x, hxv, rfl⟩
  rcases hx with hx | hx
  · exact (hxv hx).elim
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    exact ⟨e, x, hz, he, hxv⟩


namespace PolygonalGeometry
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite closed convex union is star convex in a sufficiently small ball about each of its points. -/
theorem finite_closed_convex_union_locally_starConvex
    {ι : Type*} [Finite ι] (K : ι → Set E)
    (hclosed : ∀ i, IsClosed (K i)) (hconvex : ∀ i, Convex ℝ (K i))
    (x : E) (_hx : x ∈ ⋃ i, K i) :
    ∃ r : ℝ, 0 < r ∧ StarConvex ℝ x ((⋃ i, K i) ∩ Metric.ball x r) := by
  classical
  let B : Set E := ⋃ i : {i // x ∉ K i}, K i.val
  have hB : IsClosed B := isClosed_iUnion_of_finite fun i => hclosed i.val
  have hxB : x ∉ B := by
    intro h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact i.property hi
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hB.isOpen_compl x hxB
  refine ⟨r, hr, ?_⟩
  have hT : (⋃ i, K i) ∩ Metric.ball x r =
      (⋃ i : {i // x ∈ K i}, K i.val) ∩ Metric.ball x r := by
    ext y
    constructor
    · rintro ⟨hy, hyr⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      have hxi : x ∈ K i := by
        by_contra hn
        exact hball hyr (Set.mem_iUnion.mpr ⟨⟨i, hn⟩, hi⟩)
      exact ⟨Set.mem_iUnion.mpr ⟨⟨i, hxi⟩, hi⟩, hyr⟩
    · rintro ⟨hy, hyr⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact ⟨Set.mem_iUnion.mpr ⟨i.val, hi⟩, hyr⟩
  rw [hT]
  exact (starConvex_iUnion fun i : {i // x ∈ K i} =>
    (hconvex i.val).starConvex i.property).inter
      ((convex_ball x r).starConvex (Metric.mem_ball_self hr))

/-- An initial portion of an injective arc belongs to any straight segment in its image
joining its first point to a later point. -/
theorem initial_arc_subset_segment
    (p : unitInterval → E) (hp : Continuous p) (hpi : Function.Injective p)
    (t : unitInterval)
    (hseg : segment ℝ (p 0) (p t) ⊆ Set.range p) :
    ∀ s : unitInterval, s ≤ t → p s ∈ segment ℝ (p 0) (p t) := by
  have hind := hp.isClosedEmbedding hpi |>.isEmbedding.isInducing
  have heq : p '' (p ⁻¹' segment ℝ (p 0) (p t)) = segment ℝ (p 0) (p t) :=
    Set.image_preimage_eq_of_subset hseg
  have hc : IsPreconnected (p ⁻¹' segment ℝ (p 0) (p t)) := by
    apply hind.isPreconnected_image.mp
    rw [heq]
    exact (convex_segment _ _).isPreconnected
  intro s hs
  exact hc.Icc_subset (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    ⟨s.property.1, hs⟩

/-- An injective arc that is locally star convex at its first point is locally a single
straight segment there. This conclusion concerns equality in an ambient ball. -/
theorem arc_endpoint_locally_segment
    (p : unitInterval → E) (hp : Continuous p) (hpi : Function.Injective p)
    (hstar : ∃ r : ℝ, 0 < r ∧
      StarConvex ℝ (p 0) (Set.range p ∩ Metric.ball (p 0) r)) :
    ∃ (q : E) (δ : ℝ), q ≠ p 0 ∧ 0 < δ ∧ segment ℝ (p 0) q ⊆ Set.range p ∧
      Set.range p ∩ Metric.ball (p 0) δ =
        segment ℝ (p 0) q ∩ Metric.ball (p 0) δ := by
  obtain ⟨r, hr, hstar⟩ := hstar
  have hneigh : p ⁻¹' Metric.ball (p 0) r ∈ nhds (0 : unitInterval) :=
    hp.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hr)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hneigh
  let t : unitInterval := ⟨min (ρ / 2) (1 / 2), le_of_lt (lt_min (by positivity) (by norm_num)),
    (min_le_right _ _).trans (by norm_num)⟩
  have htpos : (0 : unitInterval) < t := by
    change (0 : ℝ) < min (ρ / 2) (1 / 2)
    positivity
  have htdist : dist t (0 : unitInterval) < ρ := by
    change dist (t : ℝ) 0 < ρ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hptr : p t ∈ Metric.ball (p 0) r := hρsub htdist
  have hseg' : segment ℝ (p 0) (p t) ⊆ Set.range p ∩ Metric.ball (p 0) r :=
    hstar.segment_subset ⟨Set.mem_range_self _, hptr⟩
  have hseg : segment ℝ (p 0) (p t) ⊆ Set.range p :=
    fun _ hy => (hseg' hy).1
  let K : Set E := p '' Set.Icc t 1
  have hK : IsClosed K := (isCompact_Icc.image hp).isClosed
  have hzeroK : p 0 ∉ K := by
    rintro ⟨s, hs, hps⟩
    have hs0 : s = 0 := hpi hps
    exact (not_le_of_gt htpos) (hs0 ▸ hs.1)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hK.isOpen_compl (p 0) hzeroK
  refine ⟨p t, δ, fun h => htpos.ne' (hpi h), hδ, hseg, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨s, rfl⟩, hys⟩
    refine ⟨initial_arc_subset_segment p hp hpi t hseg s ?_, hys⟩
    by_contra hs
    exact hδsub hys ⟨s, ⟨le_of_not_ge hs, s.property.2⟩, rfl⟩
  · rintro ⟨hy, hyr⟩
    exact ⟨hseg hy, hyr⟩


end PolygonalGeometry

open PolygonalGeometry in
/-- Every simple polygonal arc is locally a single straight segment at each endpoint.
The equality is taken in an ambient metric ball, so it controls the complement as well. -/
theorem polygonal_arc_endpoint_locally_segment :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.polygonal_arc_endpoint_locally_segmentType := by
  intro a b s hs
  obtain ⟨⟨n, A, B, hpoly⟩, p, hp, hps⟩ := hs
  have hclosed : ∀ i, IsClosed (segment ℝ (A i) (B i)) := by
    intro i
    rw [segment_eq_image]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hlocal : ∃ r : ℝ, 0 < r ∧ StarConvex ℝ (p 0)
      (Set.range p ∩ Metric.ball (p 0) r) := by
    rw [hps, hpoly]
    exact finite_closed_convex_union_locally_starConvex
      (fun i => segment ℝ (A i) (B i)) hclosed
      (fun i => convex_segment _ _) (p 0) (by rw [← hpoly, ← hps]; exact Set.mem_range_self _)
  obtain ⟨q, δ, hq, hδ, hseg, heq⟩ :=
    arc_endpoint_locally_segment p p.continuous hp hlocal
  refine ⟨q, δ, ?_, hδ, ?_, ?_⟩
  · simpa only [p.source] using hq
  · simpa only [p.source, hps] using hseg
  · simpa only [p.source, hps] using heq



open Set

abbrev planeDet := @FiniteCombinatorics.Graph.Plane.FaceSideAux.planeDet

abbrev lineHalfBall := @FiniteCombinatorics.Graph.Plane.FaceSideAux.lineHalfBall

lemma continuous_planeDet (a b : Point) : Continuous (planeDet a b) := by
  unfold planeDet FiniteCombinatorics.Graph.Plane.FaceSideAux.planeDet
  fun_prop

lemma planeDet_mix (a b x y : Point) (s t : ℝ) (hst : s+t=1) :
    planeDet a b (s • x + t • y) = s * planeDet a b x + t * planeDet a b y := by
  have ht : t = 1-s := by linarith
  rw [ht]
  dsimp [planeDet, FiniteCombinatorics.Graph.Plane.FaceSideAux.planeDet]
  ring

lemma convex_planeDet_pos (a b : Point) : Convex ℝ {y | 0 < planeDet a b y} := by
  intro x hx y hy s t hs ht hst
  change 0 < planeDet a b (s • x+t • y)
  rw [planeDet_mix a b x y s t hst]
  change 0 < planeDet a b x at hx
  change 0 < planeDet a b y at hy
  by_cases hs0 : s=0
  · have ht1 : t=1 := by linarith
    simpa [hs0,ht1] using hy
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hs (Ne.symm hs0)) hx)
      (mul_nonneg ht hy.le)

lemma convex_planeDet_neg (a b : Point) : Convex ℝ {y | planeDet a b y < 0} := by
  intro x hx y hy s t hs ht hst
  change planeDet a b (s • x+t • y) < 0
  rw [planeDet_mix a b x y s t hst]
  change planeDet a b x < 0 at hx
  change planeDet a b y < 0 at hy
  by_cases hs0 : s=0
  · have ht1 : t=1 := by linarith
    simpa [hs0,ht1] using hy
  · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (lt_of_le_of_ne hs (Ne.symm hs0)) hx)
      (mul_nonpos_of_nonneg_of_nonpos ht hy.le)

lemma lineHalfBall_convex (a b x : Point) (r : ℝ) (p : Bool) :
    Convex ℝ (lineHalfBall a b x r p) := by
  cases p
  · exact (convex_ball x r).inter (convex_planeDet_neg a b)
  · exact (convex_ball x r).inter (convex_planeDet_pos a b)

lemma lineHalfBall_open (a b x : Point) (r : ℝ) (p : Bool) :
    IsOpen (lineHalfBall a b x r p) := by
  cases p
  · exact Metric.isOpen_ball.inter (isOpen_lt (continuous_planeDet a b) continuous_const)
  · exact Metric.isOpen_ball.inter (isOpen_lt continuous_const (continuous_planeDet a b))

lemma lineHalfBall_union (a b x : Point) (r : ℝ) :
    lineHalfBall a b x r false ∪ lineHalfBall a b x r true =
      Metric.ball x r \ {y | planeDet a b y=0} := by
  ext y
  simp only [lineHalfBall, FiniteCombinatorics.Graph.Plane.FaceSideAux.lineHalfBall, Bool.false_eq_true, ite_false, ite_true, mem_union, mem_inter_iff,
    mem_ofPred_eq, mem_sdiff]
  constructor
  · rintro (⟨hy,hd⟩|⟨hy,hd⟩)
    · exact ⟨hy,ne_of_lt hd⟩
    · exact ⟨hy,ne_of_gt hd⟩
  · rintro ⟨hy,hd⟩
    exact (lt_or_gt_of_ne hd).imp (fun h => ⟨hy,h⟩) (fun h => ⟨hy,h⟩)

lemma lineHalfBall_disjoint (a b x : Point) (r : ℝ) :
    Disjoint (lineHalfBall a b x r false) (lineHalfBall a b x r true) := by
  apply Set.disjoint_left.mpr
  intro y hy hy'
  have hneg : planeDet a b y < 0 := hy.2
  have hpos : 0 < planeDet a b y := hy'.2
  exact (not_lt_of_ge hpos.le) hneg

lemma planeDet_normal (a b x : Point) (t : ℝ) :
    planeDet a b (x + t • (-(b.2-a.2),b.1-a.1)) =
      planeDet a b x + t * ((b.1-a.1)^2+(b.2-a.2)^2) := by
  dsimp [planeDet, FiniteCombinatorics.Graph.Plane.FaceSideAux.planeDet]
  ring

lemma plane_normal_sq_pos {a b : Point} (hab : a ≠ b) :
    0 < (b.1-a.1)^2+(b.2-a.2)^2 := by
  by_cases h1 : b.1=a.1
  · have h2 : b.2-a.2 ≠ 0 := by
      intro h
      apply hab
      exact Prod.ext h1.symm (sub_eq_zero.mp h).symm
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr h1)) (sq_nonneg _)

lemma planeDet_halfSpace_closure {a b x : Point} (hab : a ≠ b)
    (hx : planeDet a b x=0) (p : Bool) :
    x ∈ closure {y | if p then 0 < planeDet a b y else planeDet a b y < 0} := by
  have hpos := plane_normal_sq_pos hab
  have h0 : (0:ℝ) ∈ closure (Set.Ioi (0:ℝ)) := by simp
  cases p
  · let f : ℝ → Point := fun t => x + (-t) • (-(b.2-a.2),b.1-a.1)
    have hf : Continuous f := by fun_prop
    have hfc : f 0 ∈ closure (f '' Set.Ioi (0:ℝ)) := mem_closure_image hf.continuousAt h0
    have hmaps : f '' Set.Ioi (0:ℝ) ⊆ {y | planeDet a b y < 0} := by
      rintro y ⟨t,ht,rfl⟩
      change planeDet a b (x + (-t) • (-(b.2-a.2),b.1-a.1)) < 0
      rw [planeDet_normal,hx,zero_add]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos ht) hpos
    have hc := closure_mono hmaps hfc
    have hf0 : f 0 = x := by simp only [f,neg_zero,zero_smul,add_zero]
    rw [hf0] at hc
    simpa using hc
  · let f : ℝ → Point := fun t => x + t • (-(b.2-a.2),b.1-a.1)
    have hf : Continuous f := by fun_prop
    have hfc : f 0 ∈ closure (f '' Set.Ioi (0:ℝ)) := mem_closure_image hf.continuousAt h0
    have hmaps : f '' Set.Ioi (0:ℝ) ⊆ {y | 0 < planeDet a b y} := by
      rintro y ⟨t,ht,rfl⟩
      change 0 < planeDet a b (x + t • (-(b.2-a.2),b.1-a.1))
      rw [planeDet_normal,hx,zero_add]
      exact mul_pos ht hpos
    have hc := closure_mono hmaps hfc
    have hf0 : f 0 = x := by simp only [f,zero_smul,add_zero]
    rw [hf0] at hc
    simpa using hc

lemma lineHalfBall_center_mem_closure {a b x : Point} (hab : a ≠ b)
    (hx : planeDet a b x=0) {r : ℝ} (hr : 0 < r) (p : Bool) :
    x ∈ closure (lineHalfBall a b x r p) := by
  apply Metric.isOpen_ball.inter_closure
  exact ⟨Metric.mem_ball_self hr,planeDet_halfSpace_closure hab hx p⟩

lemma lineHalfBall_nonempty {a b x : Point} (hab : a ≠ b)
    (hx : planeDet a b x=0) {r : ℝ} (hr : 0 < r) (p : Bool) :
    (lineHalfBall a b x r p).Nonempty := by
  exact closure_nonempty_iff.mp ⟨x,lineHalfBall_center_mem_closure hab hx hr p⟩

lemma mem_plane_line_iff {a b : Point} (hab : a ≠ b) (x : Point) :
    x ∈ affineSpan ℝ {a,b} ↔ planeDet a b x=0 := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨t,rfl⟩
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    dsimp [planeDet, FiniteCombinatorics.Graph.Plane.FaceSideAux.planeDet]
    ring
  · intro hx
    by_cases h1 : b.1-a.1 = 0
    · have h2 : b.2-a.2 ≠ 0 := by
        intro h2
        apply hab
        exact Prod.ext (sub_eq_zero.mp h1).symm (sub_eq_zero.mp h2).symm
      refine ⟨(x.2-a.2)/(b.2-a.2), ?_⟩
      apply Prod.ext
      · simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          Prod.fst_add, Prod.smul_fst, Prod.fst_sub,smul_eq_mul,h1,mul_zero,zero_add]
        dsimp [planeDet, FiniteCombinatorics.Graph.Plane.FaceSideAux.planeDet] at hx
        rw [h1] at hx
        have : x.1-a.1=0 := by
          apply (mul_eq_zero.mp (by linarith : (b.2-a.2)*(x.1-a.1)=0)).resolve_left h2
        linarith
      · simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          Prod.snd_add,Prod.smul_snd,Prod.snd_sub,smul_eq_mul]
        field_simp
        ring
    · refine ⟨(x.1-a.1)/(b.1-a.1), ?_⟩
      apply Prod.ext
      · simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          Prod.fst_add,Prod.smul_fst,Prod.fst_sub,smul_eq_mul]
        field_simp
        ring
      · simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          Prod.snd_add,Prod.smul_snd,Prod.snd_sub,smul_eq_mul]
        dsimp [planeDet, FiniteCombinatorics.Graph.Plane.FaceSideAux.planeDet] at hx
        field_simp
        nlinarith




namespace PolygonalGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two nontrivial segments with only their first point in common have distinct rays. -/
theorem not_sameRay_of_segment_inter_subset {a x y : E}
    (hx : x ≠ a) (hy : y ≠ a)
    (hsep : segment ℝ a x ∩ segment ℝ a y ⊆ {a}) :
    ¬ SameRay ℝ (x - a) (y - a) := by
  intro hray
  obtain ⟨u, v, hu, hv, huv⟩ := hray.exists_pos (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy)
  let d : ℝ := 1 + u + v
  have hd : 0 < d := by dsimp [d]; linarith
  have hud : u / d ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hu.le hd.le, (div_le_one hd).mpr (by dsimp [d]; linarith)⟩
  have hvd : v / d ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hv.le hd.le, (div_le_one hd).mpr (by dsimp [d]; linarith)⟩
  have heq : (u / d) • (x - a) = (v / d) • (y - a) := by
    simpa only [smul_smul, div_eq_mul_inv, mul_comm] using
      congrArg (fun z : E => d⁻¹ • z) huv
  have hz : a + (u / d) • (x - a) ∈ segment ℝ a x ∩ segment ℝ a y := by
    constructor
    · rw [segment_eq_image']
      exact ⟨u / d, hud, rfl⟩
    · rw [segment_eq_image']
      exact ⟨v / d, hvd, by rw [heq]⟩
  have hza : a + (u / d) • (x - a) = a := hsep hz
  have hsmul : (u / d) • (x - a) = 0 := (add_left_cancel (hza.trans (add_zero a).symm))
  exact (smul_ne_zero (ne_of_gt (div_pos hu hd)) (sub_ne_zero.mpr hx)) hsmul


end PolygonalGeometry

/-- In one ambient ball, every edge at a graph vertex is a straight initial segment,
and the entire drawing consists precisely of these incident segments. -/
theorem plane_vertex_locally_segments
    {V : Type u} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G) (v : V) :
    ∃ (q : G.neighborSet v → Point) (r : ℝ), 0 < r ∧
      (∀ w, q w ≠ D.point v ∧
        segment ℝ (D.point v) (q w) ⊆ D.edge (incidentEdge v w)) ∧
      (∀ w, D.edge (incidentEdge v w) ∩ Metric.ball (D.point v) r =
        segment ℝ (D.point v) (q w) ∩ Metric.ball (D.point v) r) ∧
      planeImage D ∩ Metric.ball (D.point v) r =
        ({D.point v} ∪ ⋃ w, segment ℝ (D.point v) (q w)) ∩
          Metric.ball (D.point v) r := by
  classical
  have hw (w : G.neighborSet v) :=
    polygonal_arc_endpoint_locally_segment (D.edge_arc v w.val w.property)
  choose q δ hq hδ hseg heq using hw
  let W : Set Point := (Set.range D.point \ {D.point v}) ∪
    ⋃ e : {e : G.edgeSet // v ∉ e.val}, D.edge e.val
  have hW : IsClosed W := by
    apply ((Set.finite_range D.point).sdiff).isClosed.union
    exact isClosed_iUnion_of_finite fun e => (edge_compact D e.val).isClosed
  have hvW : D.point v ∉ W := by
    rintro (h | h)
    · exact h.2 rfl
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp h
      exact e.property ((D.vertex_edge e.val v).mp he)
  have hU : ((⋂ w, Metric.ball (D.point v) (δ w)) ∩ Wᶜ) ∈ nhds (D.point v) :=
    Filter.inter_mem (Filter.iInter_mem.mpr fun w => Metric.ball_mem_nhds _ (hδ w))
      (hW.isOpen_compl.mem_nhds hvW)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
  have hball (w : G.neighborSet v) :
      Metric.ball (D.point v) r ⊆ Metric.ball (D.point v) (δ w) :=
    fun _ hy => Set.mem_iInter.mp (hsub hy).1 w
  have hedge (w : G.neighborSet v) :
      D.edge (incidentEdge v w) ∩ Metric.ball (D.point v) r =
        segment ℝ (D.point v) (q w) ∩ Metric.ball (D.point v) r := by
    ext y
    constructor
    · rintro ⟨hy, hyr⟩
      exact ⟨((heq w).symm ▸ (show y ∈ D.edge (incidentEdge v w) ∩
        Metric.ball (D.point v) (δ w) from ⟨hy, hball w hyr⟩)).1, hyr⟩
    · rintro ⟨hy, hyr⟩
      exact ⟨hseg w hy, hyr⟩
  refine ⟨q, r, hr, fun w => ⟨hq w, hseg w⟩, hedge, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyr⟩
    refine ⟨?_, hyr⟩
    rcases hy with hy | hy
    · have hyc : y = D.point v := by
        by_contra hyn
        exact (hsub hyr).2 (Or.inl ⟨hy, hyn⟩)
      exact Or.inl hyc
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hy
      have hv : v ∈ e.val := by
        by_contra hv
        exact (hsub hyr).2 (Or.inr (Set.mem_iUnion.mpr ⟨⟨e, hv⟩, he⟩))
      obtain ⟨w, rfl⟩ := edge_eq_incidentEdge v e hv
      exact Or.inr (Set.mem_iUnion.mpr ⟨w, ((hedge w) ▸
        (show y ∈ D.edge (incidentEdge v w) ∩ Metric.ball (D.point v) r from ⟨he, hyr⟩)).1⟩)
  · rintro ⟨hy, hyr⟩
    refine ⟨?_, hyr⟩
    rcases hy with hy | hy
    · exact Or.inl (hy ▸ Set.mem_range_self v)
    · obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hy
      exact Or.inr (Set.mem_iUnion.mpr ⟨incidentEdge v w, hseg w hw⟩)


/-- Straight initial segments of distinct incident graph edges have only the vertex in common. -/
theorem incident_segments_inter_subset
    {V : Type u} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G) (v : V)
    (q : G.neighborSet v → Point)
    (hseg : ∀ w, segment ℝ (D.point v) (q w) ⊆ D.edge (incidentEdge v w))
    (w z : G.neighborSet v) (hwz : w ≠ z) :
    segment ℝ (D.point v) (q w) ∩ segment ℝ (D.point v) (q z) ⊆ {D.point v} := by
  intro x hx
  have hef : incidentEdge v w ≠ incidentEdge v z :=
    fun h => hwz (incidentEdge_injective v h)
  have hx' : x ∈ D.edge (incidentEdge v w) ∩ D.edge (incidentEdge v z) :=
    ⟨hseg w hx.1, hseg z hx.2⟩
  rw [D.edge_intersection _ _ hef] at hx'
  obtain ⟨a, ha, rfl⟩ := hx'
  have hav : a = v := by
    rcases Sym2.mem_iff.mp ha.1 with h | h
    · exact h
    · rcases Sym2.mem_iff.mp ha.2 with h' | h'
      · exact h'
      · exact False.elim (hwz (Subtype.ext (h.symm.trans h')))
  exact congrArg D.point hav

/-- The straight initial directions at a graph vertex are pairwise different rays. -/
theorem incident_segments_not_sameRay
    {V : Type u} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G) (v : V)
    (q : G.neighborSet v → Point)
    (hq : ∀ w, q w ≠ D.point v)
    (hseg : ∀ w, segment ℝ (D.point v) (q w) ⊆ D.edge (incidentEdge v w))
    (w z : G.neighborSet v) (hwz : w ≠ z) :
    ¬ SameRay ℝ (q w - D.point v) (q z - D.point v) :=
  PolygonalGeometry.not_sameRay_of_segment_inter_subset (hq w) (hq z)
    (incident_segments_inter_subset D v q hseg w z hwz)



namespace SegmentRegularity
open Set AffineSubspace

theorem segment_subset_line (a b : Point) : segment ℝ a b ⊆ (line[ℝ,a,b] : Set Point) := by
  rw [segment_eq_image_lineMap]
  rintro x ⟨t, ht, rfl⟩
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

theorem line_inter_subsingleton (a b c d : Point)
    (hne : line[ℝ,a,b] ≠ line[ℝ,c,d]) :
    ((line[ℝ,a,b] : Set Point) ∩ (line[ℝ,c,d] : Set Point)).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact hne ((affineSpan_pair_eq_of_mem_of_mem_of_ne hx.1 hy.1 hxy).symm.trans
    (affineSpan_pair_eq_of_mem_of_mem_of_ne hx.2 hy.2 hxy))

def parameter (a b y : Point) : ℝ :=
  if b.1-a.1 = 0 then (y.2-a.2)/(b.2-a.2) else (y.1-a.1)/(b.1-a.1)

theorem continuous_parameter (a b : Point) : Continuous (parameter a b) := by
  unfold parameter
  split_ifs
  · fun_prop
  · fun_prop

theorem parameter_lineMap (a b : Point) (hab : a ≠ b) (t : ℝ) :
    parameter a b (AffineMap.lineMap a b t) = t := by
  unfold parameter
  split_ifs with h
  · have h2 : b.2-a.2 ≠ 0 := by
      intro h2
      apply hab
      apply Prod.ext <;> linarith
    simp only [AffineMap.lineMap_apply_module, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  · simp only [AffineMap.lineMap_apply_module, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    field_simp
    ring

theorem segment_has_line_neighborhood (a b x : Point) (hx : x ∈ segment ℝ a b)
    (hxa : x ≠ a) (hxb : x ≠ b) :
    ∃ U : Set Point, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ line[ℝ,a,b] → y ∈ segment ℝ a b := by
  have hab : a ≠ b := by
    rintro rfl
    exact hxa (by simpa using hx)
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, htx⟩ := hx
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
    intro h
    apply hxa
    rw [← htx, ← h]
    simp)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by
    intro h
    apply hxb
    rw [← htx, h]
    simp)
  refine ⟨parameter a b ⁻¹' Ioo 0 1,
    isOpen_Ioo.preimage (continuous_parameter a b), ?_, ?_⟩
  · change parameter a b x ∈ Ioo 0 1
    rw [← htx, parameter_lineMap a b hab]
    exact ⟨ht0,ht1⟩
  · intro y hy hyl
    obtain ⟨s,hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hyl
    have hys : s ∈ Ioo (0:ℝ) 1 := by
      change parameter a b y ∈ Ioo 0 1 at hy
      rwa [← hs, parameter_lineMap a b hab] at hy
    rw [segment_eq_image_lineMap]
    exact ⟨s, ⟨hys.1.le,hys.2.le⟩,hs⟩

def segmentExceptions {ι : Type*} (a b : ι → Point) : Set Point := by
  classical
  exact range a ∪ range b ∪ ⋃ i, ⋃ j,
    if line[ℝ,a i,b i] = line[ℝ,a j,b j] then ∅
    else (line[ℝ,a i,b i] : Set Point) ∩ (line[ℝ,a j,b j] : Set Point)

theorem segmentExceptions_finite {ι : Type*} [Finite ι] (a b : ι → Point) :
    (segmentExceptions a b).Finite := by
  classical
  unfold segmentExceptions
  refine ((finite_range a).union (finite_range b)).union ?_
  apply finite_iUnion
  intro i
  apply finite_iUnion
  intro j
  split_ifs with h
  · exact finite_empty
  · exact (line_inter_subsingleton (a i) (b i) (a j) (b j) h).finite

theorem segmentUnion_regular {ι : Type*} [Finite ι] (a b : ι → Point) (x : Point)
    (hx : x ∈ ⋃ i, segment ℝ (a i) (b i)) (hbad : x ∉ segmentExceptions a b) :
    ∃ i : ι, a i ≠ b i ∧
      ∃ U : Set Point, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, (y ∈ ⋃ j, segment ℝ (a j) (b j)) ↔ y ∈ line[ℝ,a i,b i] := by
  classical
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  have hxa : x ≠ a i := by
    intro h
    apply hbad
    exact Or.inl (Or.inl ⟨i,h.symm⟩)
  have hxb : x ≠ b i := by
    intro h
    apply hbad
    exact Or.inl (Or.inr ⟨i,h.symm⟩)
  have hab : a i ≠ b i := by
    intro h
    rw [h,segment_same,mem_singleton_iff] at hxi
    exact hxb hxi
  have hactive (j : ι) (hxj : x ∈ segment ℝ (a j) (b j)) :
      line[ℝ,a j,b j] = line[ℝ,a i,b i] := by
    by_contra h
    apply hbad
    right
    apply mem_iUnion.mpr
    refine ⟨j,mem_iUnion.mpr ⟨i,?_⟩⟩
    simp only [ite_eq_right h, mem_inter_iff]
    exact ⟨segment_subset_line _ _ hxj, segment_subset_line _ _ hxi⟩
  obtain ⟨W,hWo,hxW,hW⟩ := segment_has_line_neighborhood (a i) (b i) x hxi hxa hxb
  let A : ι → Set Point := fun j => if x ∈ segment ℝ (a j) (b j) then univ
    else (segment ℝ (a j) (b j))ᶜ
  have hAo : ∀ j, IsOpen (A j) := by
    intro j
    dsimp [A]
    split_ifs
    · exact isOpen_univ
    · have hclosed : IsClosed (segment ℝ (a j) (b j)) := by
        rw [segment_eq_image_lineMap]
        exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
      exact hclosed.isOpen_compl
  refine ⟨i,hab,W ∩ ⋂ j, A j,hWo.inter (isOpen_iInter_of_finite hAo),?_,?_⟩
  · refine ⟨hxW,mem_iInter.mpr ?_⟩
    intro j
    dsimp [A]
    split_ifs with h
    · trivial
    · exact h
  · intro y hy
    constructor
    · intro hyS
      obtain ⟨j,hyj⟩ := mem_iUnion.mp hyS
      have hxj : x ∈ segment ℝ (a j) (b j) := by
        by_contra hxj
        have hyA := mem_iInter.mp hy.2 j
        have : y ∉ segment ℝ (a j) (b j) := by simpa [A,hxj] using hyA
        exact this hyj
      rw [← hactive j hxj]
      exact segment_subset_line _ _ hyj
    · intro hyl
      exact mem_iUnion.mpr ⟨i,hW y hy.1 hyl⟩



theorem plane_image_polygonal {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) : IsPolygonal (planeImage D) := by
  classical
  choose n a b hseg using edge_polygonal D
  let I := V ⊕ (Σ e : G.edgeSet, Fin (n e))
  let A : I → Point := Sum.elim D.point (fun i => a i.1 i.2)
  let B : I → Point := Sum.elim D.point (fun i => b i.1 i.2)
  have heq : planeImage D = ⋃ i, segment ℝ (A i) (B i) := by
    ext x
    change x ∈ Set.range D.point ∪ (⋃ e, D.edge e) ↔ _
    simp only [Set.mem_union, Set.mem_range, Set.mem_iUnion]
    constructor
    · rintro (⟨v, rfl⟩ | ⟨e, hx⟩)
      · exact ⟨Sum.inl v, left_mem_segment ℝ _ _⟩
      · rw [hseg e] at hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨e, i⟩, hi⟩
    · rintro ⟨v | ⟨e, i⟩, hx⟩
      · have hv : x = D.point v := by simpa [A, B, segment_same] using hx
        exact Or.inl ⟨v, hv.symm⟩
      · right
        refine ⟨e, ?_⟩
        rw [hseg e]
        exact Set.mem_iUnion.mpr ⟨i, hx⟩
  let e := Finite.equivFin I
  refine ⟨Nat.card I, A ∘ e.symm, B ∘ e.symm, heq.trans ?_⟩
  exact Set.iUnion_congr_of_surjective e e.surjective (by intro i; simp)

theorem face_frontier_regular_line {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (he : G.edgeSet.Nonempty) (F : Face D) :
    ∃ (x a b : Point), OnePoint.some x ∈ frontier (faceRegion D F) ∧ x ∉ range D.point ∧ a ≠ b ∧
      ∃ U : Set Point, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, y ∈ planeImage D ↔ y ∈ line[ℝ,a,b] := by
  obtain ⟨n,a,b,hab⟩ := plane_image_polygonal D
  have hi := face_frontier_infinite D he F
  have hb : (OnePoint.some '' (segmentExceptions a b ∪ range D.point) : Set Sphere).Finite :=
    ((segmentExceptions_finite a b).union (finite_range D.point)).image _
  obtain ⟨z,hz,hzn⟩ := (hi.sdiff hb).nonempty
  obtain ⟨x,hx,rfl⟩ := face_frontier_subset_image D F hz
  have hxS : x ∈ ⋃ i, segment ℝ (a i) (b i) := hab ▸ hx
  have hxB : x ∉ segmentExceptions a b := fun hxB => hzn ⟨x,Or.inl hxB,rfl⟩
  have hxV : x ∉ range D.point := fun hxV => hzn ⟨x,Or.inr hxV,rfl⟩
  obtain ⟨i,hi,U,hU,hxU,hlocal⟩ := segmentUnion_regular a b x hxS hxB
  exact ⟨x,a i,b i,hz,hxV,hi,U,hU,hxU,fun y hy => by rw [hab]; exact hlocal y hy⟩


end SegmentRegularity

/-- A regular straight piece has two genuine local sides, possibly belonging to
one and the same actual face. Every face approaching its center is one of them. -/
theorem local_line_faces [Finite V] (D : PlaneEmbedding G) {a b x : Point} (hab : a ≠ b)
    (hx : planeDet a b x=0) {r : ℝ} (hr : 0 < r)
    (hmodel : ∀ y ∈ Metric.ball x r, y ∈ planeImage D ↔ planeDet a b y=0) :
    ∃ face : Bool → Face D,
      (∀ p, OnePoint.some '' lineHalfBall a b x r p ⊆ faceRegion D (face p) ∧
        OnePoint.some x ∈ frontier (faceRegion D (face p))) ∧
      (∀ F : Face D, OnePoint.some x ∈ frontier (faceRegion D F) →
        F=face false ∨ F=face true) := by
  let C : Bool → Set Sphere := fun p => OnePoint.some '' lineHalfBall a b x r p
  have hCconn (p : Bool) : IsConnected (C p) :=
    ⟨(lineHalfBall_nonempty hab hx hr p).image _ ,
      (lineHalfBall_convex a b x r p).isPreconnected.image _
        OnePoint.continuous_coe.continuousOn⟩
  have hCsub (p : Bool) : C p ⊆ (sphereImage D)ᶜ := by
    rintro _ ⟨y,hy,rfl⟩ hym
    have hy0 := (hmodel y hy.1).mp ((sphere_image_membership D y).mp hym)
    cases p
    · have hyneg : planeDet a b y < 0 := hy.2
      exact (ne_of_lt hyneg) hy0
    · have hypos : 0 < planeDet a b y := hy.2
      exact (ne_of_gt hypos) hy0
  have hfaces (p : Bool) : ∃! F : Face D, C p ⊆ faceRegion D F :=
    existsUnique_face_of_preconnected D (hCconn p) (hCsub p)
  let face : Bool → Face D := fun p => (hfaces p).choose
  have hface (p : Bool) : C p ⊆ faceRegion D (face p) := (hfaces p).choose_spec.1
  have hxm : OnePoint.some x ∈ sphereImage D :=
    (sphere_image_membership D x).mpr ((hmodel x (Metric.mem_ball_self hr)).mpr hx)
  have hxcl (p : Bool) : OnePoint.some x ∈ closure (C p) :=
    mem_closure_image OnePoint.continuous_coe.continuousAt
      (lineHalfBall_center_mem_closure hab hx hr p)
  refine ⟨face, ?_, ?_⟩
  · intro p
    refine ⟨hface p, closure_mono (hface p) (hxcl p), ?_⟩
    intro hi
    exact face_region_subset D (face p) (interior_subset hi) hxm
  · intro F hxF
    have hcover : (OnePoint.some '' Metric.ball x r) ∩ (sphereImage D)ᶜ ⊆ ⋃ p, C p := by
      rintro _ ⟨⟨y,hy,rfl⟩,hyc⟩
      have hyne : planeDet a b y ≠ 0 := by
        intro hy0
        exact hyc ((sphere_image_membership D y).mpr ((hmodel y hy).mpr hy0))
      rcases lt_or_gt_of_ne hyne with hyneg | hypos
      · exact mem_iUnion.mpr ⟨false,y,⟨hy,hyneg⟩,rfl⟩
      · exact mem_iUnion.mpr ⟨true,y,⟨hy,hypos⟩,rfl⟩
    obtain ⟨p,_,hp⟩ := face_contains_local_patch D F (frontier_subset_closure hxF)
      (OnePoint.isOpenEmbedding_coe.isOpenMap.image_mem_nhds (Metric.ball_mem_nhds x hr))
      C (fun p => (hCconn p).isPreconnected) hCsub hcover
    have hFeq : F=face p := (hfaces p).choose_spec.2 F hp
    cases p
    · exact Or.inl hFeq
    · exact Or.inr hFeq


/-- Every actual face has a genuine open halfdisk beside a straight interior
piece of the drawing, with its center away from graph vertices. -/
theorem every_face_has_local_side [Finite V] (D : PlaneEmbedding G) (he : G.edgeSet.Nonempty)
    (F : Face D) :
    ∃ (x a b : Point) (r : ℝ) (p : Bool),
      a ≠ b ∧ 0 < r ∧ planeDet a b x=0 ∧ x ∉ Set.range D.point ∧
      (∀ y ∈ Metric.ball x r, y ∈ planeImage D ↔ planeDet a b y=0) ∧
      OnePoint.some '' lineHalfBall a b x r p ⊆ faceRegion D F ∧
      OnePoint.some x ∈ frontier (faceRegion D F) := by
  obtain ⟨x,a,b,hxF,hxV,hab,U,hU,hxU,hlocal⟩ :=
    SegmentRegularity.face_frontier_regular_line D he F
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU x hxU
  have hmodel : ∀ y ∈ Metric.ball x r, y ∈ planeImage D ↔ planeDet a b y=0 :=
    fun y hy => (hlocal y (hball hy)).trans (mem_plane_line_iff hab y)
  have hxm : x ∈ planeImage D :=
    (sphere_image_membership D x).mp (face_frontier_subset_image D F hxF)
  have hx : planeDet a b x=0 := (hmodel x (Metric.mem_ball_self hr)).mp hxm
  let C : Bool → Set Sphere := fun p => OnePoint.some '' lineHalfBall a b x r p
  have hCconn (p : Bool) : IsPreconnected (C p) :=
    (lineHalfBall_convex a b x r p).isPreconnected.image _
      OnePoint.continuous_coe.continuousOn
  have hCsub (p : Bool) : C p ⊆ (sphereImage D)ᶜ := by
    rintro _ ⟨y,hy,rfl⟩ hym
    have hy0 := (hmodel y hy.1).mp ((sphere_image_membership D y).mp hym)
    cases p
    · have hyneg : planeDet a b y < 0 := hy.2
      exact (ne_of_lt hyneg) hy0
    · have hypos : 0 < planeDet a b y := hy.2
      exact (ne_of_gt hypos) hy0
  have hcover : (OnePoint.some '' Metric.ball x r) ∩ (sphereImage D)ᶜ ⊆ ⋃ p, C p := by
    rintro _ ⟨⟨y,hy,rfl⟩,hyc⟩
    have hyne : planeDet a b y ≠ 0 := by
      intro hy0
      exact hyc ((sphere_image_membership D y).mpr ((hmodel y hy).mpr hy0))
    rcases lt_or_gt_of_ne hyne with hyneg | hypos
    · exact mem_iUnion.mpr ⟨false,y,⟨hy,hyneg⟩,rfl⟩
    · exact mem_iUnion.mpr ⟨true,y,⟨hy,hypos⟩,rfl⟩
  obtain ⟨p,_,hp⟩ := face_contains_local_patch D F (frontier_subset_closure hxF)
    (OnePoint.isOpenEmbedding_coe.isOpenMap.image_mem_nhds (Metric.ball_mem_nhds x hr))
    C hCconn hCsub hcover
  exact ⟨x,a,b,r,p,hab,hr,hx,hxV,hmodel,hp,hxF⟩


/-- The ambient straight-ray model includes pairwise distinct incident directions. -/
theorem vertex_straight_rays :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.vertex_straight_raysType := by
  intro V _ G D v
  obtain ⟨q,r,hr,hq,hedge,hmodel⟩ := plane_vertex_locally_segments D v
  refine ⟨q,r,hr,hq,hedge,hmodel,?_⟩
  exact incident_segments_not_sameRay D v q (fun w => (hq w).1) (fun w => (hq w).2)

/-- The ordinary argument of a plane direction, with values in `(-π,π]`. -/
abbrev planeDirectionAngle := @FiniteCombinatorics.Graph.Plane.FaceSideAux.directionAngle

lemma planeDirectionAngle_eq_implies_sameRay {a b : Point}
    (h : planeDirectionAngle a = planeDirectionAngle b) : SameRay ℝ a b := by
  have hc : SameRay ℝ (Complex.equivRealProdCLM.symm a)
      (Complex.equivRealProdCLM.symm b) := Complex.sameRay_of_arg_eq h
  have hreal := hc.map Complex.equivRealProdCLM.toLinearEquiv.toLinearMap
  change SameRay ℝ (Complex.equivRealProdCLM (Complex.equivRealProdCLM.symm a))
    (Complex.equivRealProdCLM (Complex.equivRealProdCLM.symm b)) at hreal
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hreal

section SortedAngles
variable {α : Type*} [Finite α] (θ : α → ℝ) (hθ : Function.Injective θ)

/-- Every member of a finite family, listed in increasing angular order. -/
def angleList : List α := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : LinearOrder α := LinearOrder.lift' θ hθ
  exact Finset.univ.sort (· ≤ ·)

lemma angleList_nodup : (angleList θ hθ).Nodup := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let : LinearOrder α := LinearOrder.lift' θ hθ
  exact Finset.sort_nodup _ _

@[simp] lemma mem_angleList (a : α) : a ∈ angleList θ hθ := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let : LinearOrder α := LinearOrder.lift' θ hθ
  change a ∈ Finset.univ.sort (· ≤ ·)
  simp

lemma angleList_pairwise : (angleList θ hθ).Pairwise (fun a b => θ a < θ b) := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let : LinearOrder α := LinearOrder.lift' θ hθ
  exact Finset.sortedLT_sort Finset.univ |>.pairwise

/-- The cyclic successor in the actual increasing angle list, including the wraparound. -/
def angleTurn : Equiv.Perm α := by
  classical
  exact (angleList θ hθ).formPerm

lemma angleTurn_isCycleOn : (angleTurn θ hθ).IsCycleOn Set.univ := by
  classical
  have h := (angleList_nodup θ hθ).isCycleOn_formPerm
  have hall : {a : α | a ∈ angleList θ hθ} = Set.univ := by ext a; simp
  simpa only [angleTurn, hall] using h

lemma angleTurn_apply_getElem (i : ℕ) (hi : i < (angleList θ hθ).length) :
    angleTurn θ hθ ((angleList θ hθ)[i]) =
      (angleList θ hθ)[(i + 1) % (angleList θ hθ).length]'(Nat.mod_lt _ (Nat.zero_le i |>.trans_lt hi)) := by
  classical
  exact List.formPerm_apply_getElem _ (angleList_nodup θ hθ) i hi

end SortedAngles

section DrawingRotation
variable [Finite V]

/-- A concrete straight endpoint for each initial edge direction, chosen from the ambient
local straight-segment theorem. -/
def vertexSegmentEndpoints (D : PlaneEmbedding G) (v : V) : G.neighborSet v → Point :=
  Classical.choose (plane_vertex_locally_segments D v)

lemma vertexSegmentEndpoints_properties (D : PlaneEmbedding G) (v : V)
    (w : G.neighborSet v) :
    vertexSegmentEndpoints D v w ≠ D.point v ∧
      segment ℝ (D.point v) (vertexSegmentEndpoints D v w) ⊆ D.edge (incidentEdge v w) :=
  (Classical.choose_spec (Classical.choose_spec (plane_vertex_locally_segments D v))).2.1 w

/-- Initial outgoing edge angles in the fixed orientation of the plane. -/
def vertexNeighborAngle (D : PlaneEmbedding G) (v : V) (w : G.neighborSet v) : ℝ :=
  planeDirectionAngle (vertexSegmentEndpoints D v w - D.point v)

lemma vertexNeighborAngle_injective (D : PlaneEmbedding G) (v : V) :
    Function.Injective (vertexNeighborAngle D v) := by
  intro w z hwz
  by_contra hne
  exact incident_segments_not_sameRay D v (vertexSegmentEndpoints D v)
    (fun a => (vertexSegmentEndpoints_properties D v a).1)
    (fun a => (vertexSegmentEndpoints_properties D v a).2) w z hne
    (planeDirectionAngle_eq_implies_sameRay hwz)

/-- The cyclic rotation induced by the actual straight edge directions in the drawing. -/
def drawingRotation (D : PlaneEmbedding G) : RotationSystem G where
  turn v := angleTurn (vertexNeighborAngle D v) (vertexNeighborAngle_injective D v)
  cyclic v := angleTurn_isCycleOn (vertexNeighborAngle D v) (vertexNeighborAngle_injective D v)


end DrawingRotation

/-- The constructed neighbor rotations are exactly the cyclic orders of the
actual initial straight directions, in ambient neighborhoods of each vertex. -/
theorem drawing_rotation_geometry :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.drawing_rotation_geometryType := by
  intro V _ G D
  refine ⟨drawingRotation D, ?_⟩
  intro v
  obtain ⟨r,hr,hq,hedge,hmodel⟩ := Classical.choose_spec (plane_vertex_locally_segments D v)
  refine ⟨vertexSegmentEndpoints D v,r,hr,hq,hedge,hmodel,?_⟩
  refine ⟨angleList (vertexNeighborAngle D v) (vertexNeighborAngle_injective D v),
    angleList_nodup _ _, mem_angleList _ _, angleList_pairwise _ _, rfl⟩


def angleDirection (t : ℝ) : Point := (Real.cos t,Real.sin t)

def polarAt (c : Point) (z : ℝ × ℝ) : Point := c + z.1 • angleDirection z.2

abbrev angularSector := @FiniteCombinatorics.Graph.Plane.FaceSideAux.angularSector

lemma continuous_angleDirection : Continuous angleDirection := by
  exact Real.continuous_cos.prodMk Real.continuous_sin

lemma continuous_polarAt (c : Point) : Continuous (polarAt c) := by
  exact continuous_const.add
    (continuous_fst.smul (continuous_angleDirection.comp continuous_snd))

lemma angleDirection_norm_le_one (t : ℝ) : ‖angleDirection t‖ ≤ 1 := by
  rw [angleDirection,Prod.norm_def]
  exact max_le (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one t)
    (by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one t)

lemma angleDirection_ne_zero (t : ℝ) : angleDirection t ≠ 0 := by
  intro h
  have hc : Real.cos t=0 := congrArg Prod.fst h
  have hs : Real.sin t=0 := congrArg Prod.snd h
  have hsq := Real.sin_sq_add_cos_sq t
  rw [hc,hs] at hsq
  norm_num at hsq

lemma angularSector_nonempty (c : Point) {R α β : ℝ} (hR : 0<R) (hαβ : α<β) :
    (angularSector c R α β).Nonempty := by
  exact ((nonempty_Ioo.mpr hR).prod (nonempty_Ioo.mpr hαβ)).image _

lemma angularSector_isPreconnected (c : Point) (R α β : ℝ) :
    IsPreconnected (angularSector c R α β) := by
  exact ((convex_Ioo (0:ℝ) R).isPreconnected.prod (convex_Ioo α β).isPreconnected).image _
    (continuous_polarAt c).continuousOn

lemma angularSector_isConnected (c : Point) {R α β : ℝ} (hR : 0<R) (hαβ : α<β) :
    IsConnected (angularSector c R α β) :=
  ⟨angularSector_nonempty c hR hαβ,angularSector_isPreconnected c R α β⟩

lemma angularSector_subset_ball (c : Point) (R α β : ℝ) :
    angularSector c R α β ⊆ Metric.ball c R := by
  rintro _ ⟨⟨ρ,t⟩,⟨hρ,ht⟩,rfl⟩
  change dist (c + ρ • angleDirection t) c < R
  rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hρ.1]
  exact (mul_le_of_le_one_right hρ.1.le (angleDirection_norm_le_one t)).trans_lt hρ.2

lemma angularSector_center_notMem (c : Point) (R α β : ℝ) :
    c ∉ angularSector c R α β := by
  rintro ⟨⟨ρ,t⟩,⟨hρ,ht⟩,hc⟩
  have hzero : ρ • angleDirection t=0 := by
    change c + ρ • angleDirection t=c at hc
    exact add_left_cancel (hc.trans (add_zero c).symm)
  exact (smul_ne_zero hρ.1.ne' (angleDirection_ne_zero t)) hzero

lemma angularSector_avoids_rays {ι : Type*} (c : Point) (q : ι → Point) (R α β : ℝ)
    (hgap : ∀t∈Ioo α β, ∀i, ¬ SameRay ℝ (angleDirection t) (q i-c)) :
    Disjoint (angularSector c R α β) ({c} ∪ ⋃i, segment ℝ c (q i)) := by
  apply disjoint_left.mpr
  intro y hy hygraph
  rcases hygraph with hc | hygraph
  · change y=c at hc
    rw [hc] at hy
    exact angularSector_center_notMem c R α β hy
  · obtain ⟨i,hyi⟩ := mem_iUnion.mp hygraph
    have hray : SameRay ℝ (y-c) (q i-c) := by
      simpa only [vsub_eq_sub] using (mem_segment_iff_wbtw.mp hyi).sameRay_vsub_left
    obtain ⟨⟨ρ,t⟩,⟨hρ,ht⟩,rfl⟩ := hy
    change SameRay ℝ (c + ρ • angleDirection t-c) (q i-c) at hray
    rw [add_sub_cancel_left] at hray
    have hray' := hray.pos_smul_left (inv_pos.mpr hρ.1)
    have hray'' : SameRay ℝ (angleDirection t) (q i-c) := by
      simpa only [smul_smul,inv_mul_cancel₀ hρ.1.ne',one_smul] using hray'
    exact hgap t ht i hray''

lemma angularSector_center_mem_closure (c : Point) {R α β : ℝ}
    (hR : 0<R) (hαβ : α<β) : c ∈ closure (angularSector c R α β) := by
  obtain ⟨t,ht⟩ := nonempty_Ioo.mpr hαβ
  let f : ℝ → Point := fun ρ => c + ρ • angleDirection t
  have hf : Continuous f := by fun_prop
  have h0 : (0:ℝ) ∈ closure (Ioo (0:ℝ) R) := by
    rw [closure_Ioo hR.ne]
    exact ⟨le_rfl,hR.le⟩
  have hmaps : f '' Ioo (0:ℝ) R ⊆ angularSector c R α β := by
    rintro y ⟨ρ,hρ,rfl⟩
    exact ⟨(ρ,t),⟨hρ,ht⟩,rfl⟩
  have hc := closure_mono hmaps (mem_closure_image hf.continuousAt h0)
  have hf0 : f 0=c := by simp only [f,zero_smul,add_zero]
  rwa [hf0] at hc

lemma angularSector_left_boundary_mem_closure (c : Point) {R α β ρ : ℝ}
    (hρ : ρ ∈ Ioo (0:ℝ) R) (hαβ : α<β) :
    c + ρ • angleDirection α ∈ closure (angularSector c R α β) := by
  let f : ℝ → Point := fun t => c + ρ • angleDirection t
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_const.add ((continuous_const : Continuous (fun _ : ℝ => ρ)).smul continuous_angleDirection)
  have hα : α ∈ closure (Ioo α β) := by
    rw [closure_Ioo hαβ.ne]
    exact ⟨le_rfl,hαβ.le⟩
  have hmaps : f '' Ioo α β ⊆ angularSector c R α β := by
    rintro y ⟨t,ht,rfl⟩
    exact ⟨(ρ,t),⟨hρ,ht⟩,rfl⟩
  exact closure_mono hmaps (mem_closure_image hf.continuousAt hα)

lemma angularSector_right_boundary_mem_closure (c : Point) {R α β ρ : ℝ}
    (hρ : ρ ∈ Ioo (0:ℝ) R) (hαβ : α<β) :
    c + ρ • angleDirection β ∈ closure (angularSector c R α β) := by
  let f : ℝ → Point := fun t => c + ρ • angleDirection t
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_const.add ((continuous_const : Continuous (fun _ : ℝ => ρ)).smul continuous_angleDirection)
  have hβ : β ∈ closure (Ioo α β) := by
    rw [closure_Ioo hαβ.ne]
    exact ⟨hαβ.le,le_rfl⟩
  have hmaps : f '' Ioo α β ⊆ angularSector c R α β := by
    rintro y ⟨t,ht,rfl⟩
    exact ⟨(ρ,t),⟨hρ,ht⟩,rfl⟩
  exact closure_mono hmaps (mem_closure_image hf.continuousAt hβ)

section AngularSectorFaces
variable [Finite V]

lemma angularSector_subset_plane_complement {ι : Type*} (D : PlaneEmbedding G)
    (c : Point) (q : ι → Point) (R α β : ℝ)
    (hmodel : planeImage D ∩ Metric.ball c R =
      ({c} ∪ ⋃i, segment ℝ c (q i)) ∩ Metric.ball c R)
    (hgap : ∀t∈Ioo α β, ∀i, ¬SameRay ℝ (angleDirection t) (q i-c)) :
    angularSector c R α β ⊆ (planeImage D)ᶜ := by
  intro y hy hym
  have hyball := angularSector_subset_ball c R α β hy
  have hygraph : y ∈ {c} ∪ ⋃i, segment ℝ c (q i) := by
    have hyint : y ∈ planeImage D ∩ Metric.ball c R := ⟨hym,hyball⟩
    rw [hmodel] at hyint
    exact hyint.1
  exact Set.disjoint_left.mp (angularSector_avoids_rays c q R α β hgap) hy hygraph

lemma existsUnique_angularSector_face {ι : Type*} (D : PlaneEmbedding G)
    (c : Point) (q : ι → Point) {R α β : ℝ} (hR : 0<R) (hαβ : α<β)
    (hmodel : planeImage D ∩ Metric.ball c R =
      ({c} ∪ ⋃i, segment ℝ c (q i)) ∩ Metric.ball c R)
    (hgap : ∀t∈Ioo α β, ∀i, ¬SameRay ℝ (angleDirection t) (q i-c)) :
    ∃! F : Face D, OnePoint.some '' angularSector c R α β ⊆ faceRegion D F := by
  apply existsUnique_face_of_preconnected D
    ((angularSector_isConnected c hR hαβ).image _ OnePoint.continuous_coe.continuousOn)
  rintro _ ⟨y,hy,rfl⟩ hym
  exact angularSector_subset_plane_complement D c q R α β hmodel hgap hy
    ((sphere_image_membership D y).mp hym)

lemma angularSector_face_center_frontier (D : PlaneEmbedding G)
    (c : Point) {R α β : ℝ} (hR : 0<R) (hαβ : α<β) (hc : c ∈ planeImage D)
    (F : Face D) (hF : OnePoint.some '' angularSector c R α β ⊆ faceRegion D F) :
    OnePoint.some c ∈ frontier (faceRegion D F) := by
  have hcl : OnePoint.some c ∈ closure (OnePoint.some '' angularSector c R α β) :=
    mem_closure_image OnePoint.continuous_coe.continuousAt
      (angularSector_center_mem_closure c hR hαβ)
  refine ⟨closure_mono hF hcl,?_⟩
  intro hi
  exact face_region_subset D F (interior_subset hi) ((sphere_image_membership D c).mpr hc)


end AngularSectorFaces

lemma sameRay_trigDirection_angle {d : Point} (hd : d ≠ 0) {t : ℝ}
    (ht : t ∈ Ioc (-Real.pi) Real.pi)
    (h : SameRay ℝ (Real.cos t,Real.sin t) d) :
    (Complex.equivRealProdCLM.symm d).arg=t := by
  have h' := h.map Complex.equivRealProdCLM.symm.toLinearEquiv.toLinearMap
  have hu : Complex.equivRealProdCLM.symm (Real.cos t,Real.sin t) ≠ 0 := by
    intro hu
    have hzero : (Real.cos t,Real.sin t)=(0:Point) := by
      apply Complex.equivRealProdCLM.symm.injective
      simpa only [map_zero] using hu
    have hc : Real.cos t=0 := congrArg Prod.fst hzero
    have hs : Real.sin t=0 := congrArg Prod.snd hzero
    have hsq := Real.sin_sq_add_cos_sq t
    rw [hc,hs] at hsq
    norm_num at hsq
  have hd' : Complex.equivRealProdCLM.symm d ≠ 0 := by
    intro hz
    apply hd
    apply Complex.equivRealProdCLM.symm.injective
    simpa only [map_zero] using hz
  rcases Complex.sameRay_iff.mp h' with hzero | hzero | harg
  · exact (hu hzero).elim
  · exact (hd' hzero).elim
  · change (Complex.equivRealProdCLM.symm (Real.cos t,Real.sin t)).arg =
      (Complex.equivRealProdCLM.symm d).arg at harg
    rw [Complex.equivRealProdCLM_symm_apply] at harg
    simp only [Complex.ofReal_cos,Complex.ofReal_sin] at harg
    rw [Complex.arg_cos_add_sin_mul_I ht] at harg
    exact harg.symm

lemma consecutive_angle_gap {A : Type*} (θ : A → ℝ) (L : List A)
    (hL : L.Pairwise (fun a b => θ a < θ b))
    (hmem : ∀a, a ∈ L) (i : ℕ) (hi : i+1 < L.length) {t : ℝ}
    (ht : t ∈ Ioo (θ (L[i]'(by omega))) (θ L[i+1])) :
    ∀a, θ a ≠ t := by
  intro a hat
  obtain ⟨j,hj,hja⟩ := List.mem_iff_getElem.mp (hmem a)
  have hpair := List.pairwise_iff_getElem.mp hL
  by_cases hji : j ≤ i
  · have hle : θ L[j] ≤ θ (L[i]'(by omega)) := by
      rcases lt_or_eq_of_le hji with hji | rfl
      · exact (hpair j i hj (by omega) hji).le
      · exact le_rfl
    rw [hja,hat] at hle
    exact (not_le_of_gt ht.1) hle
  · have hij : i + 1 ≤ j := by omega
    have hle : θ L[i+1] ≤ θ L[j] := by
      rcases lt_or_eq_of_le hij with hij | h
      · exact (hpair (i+1) j hi hj hij).le
      · subst j
        exact le_rfl
    rw [hja,hat] at hle
    exact (not_le_of_gt ht.2) hle

section ActualAngularGaps
variable [Finite V]

lemma consecutive_vertex_angle_no_ray (D : PlaneEmbedding G) (v : V)
    (i : ℕ) (hi : i+1 < (angleList (vertexNeighborAngle D v)
      (vertexNeighborAngle_injective D v)).length) :
    let L := angleList (vertexNeighborAngle D v) (vertexNeighborAngle_injective D v)
    ∀ t ∈ Ioo (vertexNeighborAngle D v (L[i]'(by exact Nat.lt_of_succ_lt hi)))
      (vertexNeighborAngle D v (L[i+1]'(by exact hi))),
      ∀ w, ¬SameRay ℝ (Real.cos t,Real.sin t)
        (vertexSegmentEndpoints D v w-D.point v) := by
  let θ := vertexNeighborAngle D v
  let L := angleList θ (vertexNeighborAngle_injective D v)
  have hiL : i+1 < L.length := hi
  change ∀t∈Ioo (θ (L[i]'(by omega))) (θ L[i+1]),
    ∀w, ¬SameRay ℝ (Real.cos t,Real.sin t) (vertexSegmentEndpoints D v w-D.point v)
  intro t ht w hsame
  have hlow : -Real.pi < θ (L[i]'(by omega)) := Complex.neg_pi_lt_arg _
  have hhigh : θ L[i+1] ≤ Real.pi := Complex.arg_le_pi _
  have htarg : t∈Ioc (-Real.pi) Real.pi := ⟨hlow.trans ht.1,ht.2.le.trans hhigh⟩
  have hwne : vertexSegmentEndpoints D v w-D.point v ≠ 0 :=
    sub_ne_zero.mpr (vertexSegmentEndpoints_properties D v w).1
  have hwangle : θ w=t := sameRay_trigDirection_angle hwne htarg hsame
  exact consecutive_angle_gap θ L (angleList_pairwise _ _) (mem_angleList _ _)
    i hi ht w hwangle

lemma consecutive_vertex_sector_face (D : PlaneEmbedding G) (v : V)
    (i : ℕ) (hi : i+1 < (angleList (vertexNeighborAngle D v)
      (vertexNeighborAngle_injective D v)).length) :
    let L := angleList (vertexNeighborAngle D v) (vertexNeighborAngle_injective D v)
    ∃ R : ℝ, 0<R ∧ ∃! F : Face D,
      OnePoint.some '' angularSector (D.point v) R
        (vertexNeighborAngle D v (L[i]'(by exact Nat.lt_of_succ_lt hi)))
        (vertexNeighborAngle D v (L[i+1]'(by exact hi))) ⊆ faceRegion D F ∧
      OnePoint.some (D.point v) ∈ frontier (faceRegion D F) := by
  let θ := vertexNeighborAngle D v
  let L := angleList θ (vertexNeighborAngle_injective D v)
  have hiL : i+1 < L.length := hi
  obtain ⟨R,hR,hq,hedge,hmodel⟩ := Classical.choose_spec (plane_vertex_locally_segments D v)
  have hmodel' : planeImage D ∩ Metric.ball (D.point v) R =
      ({D.point v} ∪ ⋃w, segment ℝ (D.point v) (vertexSegmentEndpoints D v w)) ∩
        Metric.ball (D.point v) R := hmodel
  have hpair : L.Pairwise (fun a b => θ a < θ b) := angleList_pairwise _ _
  have hlt : θ L[i] < θ L[i+1] :=
    List.pairwise_iff_getElem.mp hpair i (i+1) (by omega) hiL (by omega)
  have hgap : ∀t∈Ioo (θ L[i]) (θ L[i+1]),
      ∀w, ¬SameRay ℝ (angleDirection t) (vertexSegmentEndpoints D v w-D.point v) :=
    consecutive_vertex_angle_no_ray D v i hi
  obtain ⟨F,hF,huniq⟩ := existsUnique_angularSector_face D (D.point v)
    (vertexSegmentEndpoints D v) hR hlt hmodel' hgap
  refine ⟨R,hR,F,⟨hF,?_⟩,?_⟩
  · exact angularSector_face_center_frontier D (D.point v) hR hlt
      (Or.inl (Set.mem_range_self v)) F hF
  · intro F' hF'
    exact huniq F' hF'.1

lemma sorted_angle_extrema {A : Type*} (θ : A → ℝ) (L : List A)
    (hL : L.Pairwise (fun a b => θ a < θ b)) (hmem : ∀a, a∈L)
    (hpos : 0<L.length) (a : A) :
    θ (L[0]'hpos) ≤ θ a ∧ θ a ≤ θ (L[L.length-1]'(by omega)) := by
  obtain ⟨j,hj,hja⟩ := List.mem_iff_getElem.mp (hmem a)
  have hpair := List.pairwise_iff_getElem.mp hL
  have hlo : θ L[0] ≤ θ L[j] := by
    by_cases hj0 : j=0
    · subst j
      exact le_rfl
    · exact (hpair 0 j hpos hj (by omega)).le
  have hhi : θ L[j] ≤ θ (L[L.length-1]'(by omega)) := by
    by_cases hjlast : j=L.length-1
    · subst j
      exact le_rfl
    · exact (hpair j (L.length-1) hj (by omega) (by omega)).le
  simpa only [hja] using And.intro hlo hhi

lemma wrap_vertex_angle_no_ray (D : PlaneEmbedding G) (v : V)
    (hpos : 0 < (angleList (vertexNeighborAngle D v)
      (vertexNeighborAngle_injective D v)).length) :
    let L := angleList (vertexNeighborAngle D v) (vertexNeighborAngle_injective D v)
    ∀t∈Ioo (vertexNeighborAngle D v (L[L.length-1]'(by dsimp [L]; omega)))
      (vertexNeighborAngle D v (L[0]'(by exact hpos)) + 2*Real.pi),
      ∀w, ¬SameRay ℝ (Real.cos t,Real.sin t)
        (vertexSegmentEndpoints D v w-D.point v) := by
  let θ := vertexNeighborAngle D v
  let L := angleList θ (vertexNeighborAngle_injective D v)
  have hposL : 0<L.length := hpos
  change ∀t∈Ioo (θ (L[L.length-1]'(by omega))) (θ L[0]+2*Real.pi),
    ∀w, ¬SameRay ℝ (Real.cos t,Real.sin t) (vertexSegmentEndpoints D v w-D.point v)
  intro t ht w hsame
  have hpair : L.Pairwise (fun a b => θ a < θ b) := angleList_pairwise _ _
  have hminmax := sorted_angle_extrema θ L hpair (mem_angleList _ _) hposL w
  have hwne : vertexSegmentEndpoints D v w-D.point v ≠ 0 :=
    sub_ne_zero.mpr (vertexSegmentEndpoints_properties D v w).1
  by_cases htpi : t ≤ Real.pi
  · have hlast : -Real.pi < θ (L[L.length-1]'(by omega)) := Complex.neg_pi_lt_arg _
    have htarg : t∈Ioc (-Real.pi) Real.pi := ⟨hlast.trans ht.1,htpi⟩
    have hwangle : θ w=t := sameRay_trigDirection_angle hwne htarg hsame
    rw [hwangle] at hminmax
    exact (not_le_of_gt ht.1) hminmax.2
  · have hfirst : θ L[0] ≤ Real.pi := Complex.arg_le_pi _
    have htarg : t-2*Real.pi∈Ioc (-Real.pi) Real.pi := by
      constructor <;> linarith [ht.2]
    have hsame' : SameRay ℝ (Real.cos (t-2*Real.pi),Real.sin (t-2*Real.pi))
        (vertexSegmentEndpoints D v w-D.point v) := by
      simpa only [Real.cos_sub_two_pi,Real.sin_sub_two_pi] using hsame
    have hwangle : θ w=t-2*Real.pi := sameRay_trigDirection_angle hwne htarg hsame'
    rw [hwangle] at hminmax
    have : t-2*Real.pi < θ L[0] := by linarith [ht.2]
    exact (not_le_of_gt this) hminmax.1

lemma wrap_vertex_sector_face (D : PlaneEmbedding G) (v : V)
    (hpos : 0 < (angleList (vertexNeighborAngle D v)
      (vertexNeighborAngle_injective D v)).length) :
    let L := angleList (vertexNeighborAngle D v) (vertexNeighborAngle_injective D v)
    ∃ R : ℝ, 0<R ∧ ∃! F : Face D,
      OnePoint.some '' angularSector (D.point v) R
        (vertexNeighborAngle D v (L[L.length-1]'(by dsimp [L]; omega)))
        (vertexNeighborAngle D v (L[0]'(by exact hpos)) + 2*Real.pi) ⊆ faceRegion D F ∧
      OnePoint.some (D.point v) ∈ frontier (faceRegion D F) := by
  let θ := vertexNeighborAngle D v
  let L := angleList θ (vertexNeighborAngle_injective D v)
  have hposL : 0<L.length := hpos
  obtain ⟨R,hR,hq,hedge,hmodel⟩ := Classical.choose_spec (plane_vertex_locally_segments D v)
  have hmodel' : planeImage D ∩ Metric.ball (D.point v) R =
      ({D.point v} ∪ ⋃w, segment ℝ (D.point v) (vertexSegmentEndpoints D v w)) ∩
        Metric.ball (D.point v) R := hmodel
  have hlo : -Real.pi < θ L[0] := Complex.neg_pi_lt_arg _
  have hhi : θ (L[L.length-1]'(by omega)) ≤ Real.pi := Complex.arg_le_pi _
  have hlt : θ (L[L.length-1]'(by omega)) < θ L[0]+2*Real.pi := by linarith
  have hgap : ∀t∈Ioo (θ (L[L.length-1]'(by omega))) (θ L[0]+2*Real.pi),
      ∀w, ¬SameRay ℝ (angleDirection t) (vertexSegmentEndpoints D v w-D.point v) :=
    wrap_vertex_angle_no_ray D v hpos
  obtain ⟨F,hF,huniq⟩ := existsUnique_angularSector_face D (D.point v)
    (vertexSegmentEndpoints D v) hR hlt hmodel' hgap
  refine ⟨R,hR,F,⟨hF,?_⟩,?_⟩
  · exact angularSector_face_center_frontier D (D.point v) hR hlt
      (Or.inl (Set.mem_range_self v)) F hF
  · intro F' hF'
    exact huniq F' hF'.1


end ActualAngularGaps

/-- Actual faces that share a point are equal. -/
lemma face_eq_of_mem_regions [Finite V] (D : PlaneEmbedding G) {F H : Face D}
    {x : Sphere} (hxF : x ∈ faceRegion D F) (hxH : x ∈ faceRegion D H) : F = H := by
  let y : SphereComplement D := ⟨x, face_region_subset D F hxF⟩
  exact ((faceRegion_mem_iff D F y).mp hxF).symm.trans
    ((faceRegion_mem_iff D H y).mp hxH)

lemma angularSector_mono_radius (c : Point) {R S : ℝ} (hRS : R ≤ S) (α β : ℝ) :
    angularSector c R α β ⊆ angularSector c S α β := by
  rintro y ⟨⟨ρ,t⟩,⟨hρ,ht⟩,rfl⟩
  exact ⟨(ρ,t),⟨⟨hρ.1,hρ.2.trans_le hRS⟩,ht⟩,rfl⟩

/-- Shrinking a sector's radial size cannot change its actual face label. -/
lemma angularSector_face_independent_radius [Finite V] (D : PlaneEmbedding G)
    (c : Point) {R S α β : ℝ} (hR : 0 < R) (hS : 0 < S) (hαβ : α < β)
    {F H : Face D}
    (hF : OnePoint.some '' angularSector c R α β ⊆ faceRegion D F)
    (hH : OnePoint.some '' angularSector c S α β ⊆ faceRegion D H) : F = H := by
  obtain ⟨x,hx⟩ := angularSector_nonempty c (lt_min hR hS) hαβ
  apply face_eq_of_mem_regions D
    (hF ⟨x,angularSector_mono_radius c (min_le_left R S) α β hx,rfl⟩)
    (hH ⟨x,angularSector_mono_radius c (min_le_right R S) α β hx,rfl⟩)

open FiniteCombinatorics.Graph.Plane.FaceSideAux (sectorEndAngle)

lemma outgoing_vertex_sector_face [Finite V] (D : PlaneEmbedding G) (v : V) (w : G.neighborSet v) :
    ∃ R : ℝ, 0<R ∧ ∃! F : Face D,
      OnePoint.some '' angularSector (D.point v) R (vertexNeighborAngle D v w)
        (sectorEndAngle (vertexNeighborAngle D v w)
          (vertexNeighborAngle D v ((drawingRotation D).turn v w))) ⊆ faceRegion D F ∧
      OnePoint.some (D.point v) ∈ frontier (faceRegion D F) := by
  let θ := vertexNeighborAngle D v
  let L := angleList θ (vertexNeighborAngle_injective D v)
  have hmem : w∈L := mem_angleList _ _ w
  obtain ⟨j,hj,hjw⟩ := List.mem_iff_getElem.mp hmem
  have hpos : 0<L.length := by omega
  have hturn : (drawingRotation D).turn v w =
      L[(j+1)%L.length]'(Nat.mod_lt _ hpos) := by
    rw [←hjw]
    exact angleTurn_apply_getElem θ (vertexNeighborAngle_injective D v) j hj
  have hpair : L.Pairwise (fun a b => θ a < θ b) := angleList_pairwise _ _
  by_cases hnext : j+1<L.length
  · have hturn' : (drawingRotation D).turn v w = L[j+1] := by
      simpa only [Nat.mod_eq_of_lt hnext] using hturn
    have hlt : θ w < θ ((drawingRotation D).turn v w) := by
      rw [hturn',←hjw]
      exact List.pairwise_iff_getElem.mp hpair j (j+1) hj hnext (by omega)
    have hEnd : sectorEndAngle (θ w) (θ ((drawingRotation D).turn v w)) = θ L[j+1] := by
      rw [sectorEndAngle,ite_eq_left hlt,hturn']
    have H := consecutive_vertex_sector_face D v j hnext
    change ∃ R : ℝ, 0<R ∧ ∃! F : Face D,
      OnePoint.some '' angularSector (D.point v) R (θ w)
        (sectorEndAngle (θ w) (θ ((drawingRotation D).turn v w))) ⊆ faceRegion D F ∧
      OnePoint.some (D.point v) ∈ frontier (faceRegion D F)
    rw [hEnd,←hjw]
    exact H
  · have hjlast : j=L.length-1 := by omega
    have hjnext : j+1=L.length := by omega
    have hturn' : (drawingRotation D).turn v w = L[0] := by
      simpa only [hjnext,Nat.mod_self] using hturn
    have hnotlt : ¬θ w < θ ((drawingRotation D).turn v w) := by
      have hmin := (sorted_angle_extrema θ L hpair (mem_angleList _ _) hpos w).1
      rw [hturn']
      exact not_lt_of_ge hmin
    have hEnd : sectorEndAngle (θ w) (θ ((drawingRotation D).turn v w)) = θ L[0]+2*Real.pi := by
      rw [sectorEndAngle,ite_eq_right hnotlt,hturn']
    have H := wrap_vertex_sector_face D v hpos
    change ∃ R : ℝ, 0<R ∧ ∃! F : Face D,
      OnePoint.some '' angularSector (D.point v) R (θ w)
        (sectorEndAngle (θ w) (θ ((drawingRotation D).turn v w))) ⊆ faceRegion D F ∧
      OnePoint.some (D.point v) ∈ frontier (faceRegion D F)
    rw [hEnd,←hjw]
    simpa only [hjlast] using H

/-- Radius of a proved complementary sector after an outgoing edge direction. -/
def vertexSectorRadius [Finite V] (D : PlaneEmbedding G) (v : V) (w : G.neighborSet v) : ℝ :=
  (outgoing_vertex_sector_face D v w).choose

/-- The actual face of that sector. Its existence comes from polygonal geometry. -/
def vertexSectorFace [Finite V] (D : PlaneEmbedding G) (v : V)
    (w : G.neighborSet v) : Face D :=
  (outgoing_vertex_sector_face D v w).choose_spec.2.choose

lemma vertexSectorFace_geometry [Finite V] (D : PlaneEmbedding G) (v : V)
    (w : G.neighborSet v) :
    0 < vertexSectorRadius D v w ∧
    OnePoint.some '' angularSector (D.point v) (vertexSectorRadius D v w)
      (vertexNeighborAngle D v w)
      (sectorEndAngle (vertexNeighborAngle D v w)
        (vertexNeighborAngle D v ((drawingRotation D).turn v w))) ⊆
          faceRegion D (vertexSectorFace D v w) ∧
    OnePoint.some (D.point v) ∈ frontier (faceRegion D (vertexSectorFace D v w)) := by
  have h := (outgoing_vertex_sector_face D v w).choose_spec
  exact ⟨h.1,h.2.choose_spec.1⟩

/-- Label an incoming dart by the sector reached after its reversed direction
at the head. The global compatibility theorems below identify it with the actual
right face along the complete edge. -/
def drawingSideLabel [Finite V] (D : PlaneEmbedding G) (d : G.Dart) : Face D :=
  vertexSectorFace D d.snd ⟨d.fst,d.adj.symm⟩

lemma drawingSideLabel_geometry [Finite V] (D : PlaneEmbedding G) (d : G.Dart) :
    let w : G.neighborSet d.snd := ⟨d.fst,d.adj.symm⟩
    ∃ r : ℝ, 0 < r ∧
      OnePoint.some '' angularSector (D.point d.snd) r (vertexNeighborAngle D d.snd w)
        (sectorEndAngle (vertexNeighborAngle D d.snd w)
          (vertexNeighborAngle D d.snd ((drawingRotation D).turn d.snd w))) ⊆
            faceRegion D (drawingSideLabel D d) ∧
      OnePoint.some (D.point d.snd) ∈ frontier (faceRegion D (drawingSideLabel D d)) := by
  let w : G.neighborSet d.snd := ⟨d.fst,d.adj.symm⟩
  exact ⟨vertexSectorRadius D d.snd w,vertexSectorFace_geometry D d.snd w⟩

/-- Both the actual angular rotation and the actual local face labels are
constructed from the drawing. Compatibility along whole edges is proved below. -/
theorem drawing_sector_label_exists :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.drawing_sector_label_existsType := by
  intro V _ G D
  refine ⟨drawingRotation D,drawingSideLabel D,vertexSegmentEndpoints D,?_,?_⟩
  · intro v
    obtain ⟨r,hr,hq,hedge,hmodel⟩ := Classical.choose_spec (plane_vertex_locally_segments D v)
    refine ⟨r,hr,hq,hmodel,?_⟩
    refine ⟨angleList (vertexNeighborAngle D v) (vertexNeighborAngle_injective D v),
      angleList_nodup _ _, mem_angleList _ _, angleList_pairwise _ _, rfl⟩
  · intro d
    exact drawingSideLabel_geometry D d

lemma angularSector_open (c : Point) (R α β : ℝ) :
    IsOpen (angularSector c R α β) := by
  let f : ℂ → Point := fun z => c + Complex.equivRealProdCLM (Complex.exp z)
  let U : Set ℂ := {z | Real.exp z.re < R ∧ z.im ∈ Ioo α β}
  have hf : IsOpenMap f :=
    (isOpenMap_add_left c).comp
      (Complex.equivRealProdCLM.toHomeomorph.isOpenMap.comp Complex.isOpenMap_exp)
  have hU : IsOpen U :=
    (isOpen_lt (Real.continuous_exp.comp Complex.continuous_re) continuous_const).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  have heq : angularSector c R α β = f '' U := by
    ext y
    constructor
    · rintro ⟨⟨ρ,t⟩,⟨hρ,ht⟩,rfl⟩
      refine ⟨⟨Real.log ρ,t⟩,?_,?_⟩
      · exact ⟨by change Real.exp (Real.log ρ) < R; simpa only [Real.exp_log hρ.1] using hρ.2,ht⟩
      · ext <;> simp [f,Complex.exp_re,Complex.exp_im,Real.exp_log hρ.1]
    · rintro ⟨z,hz,rfl⟩
      refine ⟨(Real.exp z.re,z.im),⟨⟨Real.exp_pos _,hz.1⟩,hz.2⟩,?_⟩
      ext <;> simp [f,Complex.exp_re,Complex.exp_im]
  rw [heq]
  exact hf U hU

lemma planeDet_polar (c : Point) (L ρ α t : ℝ) :
    planeDet c (c + L • angleDirection α) (c + ρ • angleDirection t) =
      L * ρ * Real.sin (t - α) := by
  simp only [planeDet, FiniteCombinatorics.Graph.Plane.FaceSideAux.planeDet,
    angleDirection, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, add_sub_cancel_left, Real.sin_sub]
  ring

/-- The sector immediately counterclockwise from a ray meets the positive
half of every small disk centered at a nonzero point of that ray. -/
lemma angularSector_meets_left_halfBall (c : Point) {L ρ R α β r : ℝ}
    (hL : 0 < L) (hρ : ρ ∈ Ioo (0 : ℝ) R) (hαβ : α < β) (hr : 0 < r) :
    (angularSector c R α β ∩
      lineHalfBall c (c + L • angleDirection α) (c + ρ • angleDirection α) r true).Nonempty := by
  let γ := min β (α + Real.pi)
  have hαγ : α < γ := lt_min hαβ (by linarith [Real.pi_pos])
  let f : ℝ → Point := fun t => c + ρ • angleDirection t
  have hf : Continuous f := continuous_const.add
    ((continuous_const : Continuous (fun _ : ℝ => ρ)).smul continuous_angleDirection)
  have hα : α ∈ closure (Ioo α γ) := by
    rw [closure_Ioo hαγ.ne]
    exact ⟨le_rfl, hαγ.le⟩
  have hcl : f α ∈ closure (f '' Ioo α γ) :=
    mem_closure_image hf.continuousAt hα
  obtain ⟨y, ⟨t, ht, rfl⟩, hyd⟩ := Metric.mem_closure_iff.mp hcl r hr
  refine ⟨f t, ⟨(ρ,t),⟨hρ,⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩⟩,rfl⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · change dist (f t) (f α) < r
    simpa only [dist_comm] using hyd
  · change 0 < planeDet c (c + L • angleDirection α) (c + ρ • angleDirection t)
    rw [planeDet_polar]
    apply mul_pos (mul_pos hL hρ.1)
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [ht.1]
    · have := ht.2.trans_le (min_le_right β (α + Real.pi))
      linarith

/-- The sector immediately clockwise from its last ray meets the negative
half of every small disk centered at a nonzero point of that ray. -/
lemma angularSector_meets_right_halfBall (c : Point) {L ρ R α β r : ℝ}
    (hL : 0 < L) (hρ : ρ ∈ Ioo (0 : ℝ) R) (hαβ : α < β) (hr : 0 < r) :
    (angularSector c R α β ∩
      lineHalfBall c (c + L • angleDirection β) (c + ρ • angleDirection β) r false).Nonempty := by
  let γ := max α (β - Real.pi)
  have hγβ : γ < β := max_lt hαβ (by linarith [Real.pi_pos])
  let f : ℝ → Point := fun t => c + ρ • angleDirection t
  have hf : Continuous f := continuous_const.add
    ((continuous_const : Continuous (fun _ : ℝ => ρ)).smul continuous_angleDirection)
  have hβ : β ∈ closure (Ioo γ β) := by
    rw [closure_Ioo hγβ.ne]
    exact ⟨hγβ.le, le_rfl⟩
  have hcl : f β ∈ closure (f '' Ioo γ β) :=
    mem_closure_image hf.continuousAt hβ
  obtain ⟨y, ⟨t, ht, rfl⟩, hyd⟩ := Metric.mem_closure_iff.mp hcl r hr
  refine ⟨f t, ⟨(ρ,t),⟨hρ,⟨(le_max_left _ _).trans_lt ht.1,ht.2⟩⟩,rfl⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · change dist (f t) (f β) < r
    simpa only [dist_comm] using hyd
  · change planeDet c (c + L • angleDirection β) (c + ρ • angleDirection t) < 0
    rw [planeDet_polar]
    apply mul_neg_of_pos_of_neg (mul_pos hL hρ.1)
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · linarith [ht.2]
    · have := (le_max_right α (β - Real.pi)).trans_lt ht.1
      linarith

lemma directionAngle_polar_decomposition (d : Point) :
    ‖Complex.equivRealProdCLM.symm d‖ • angleDirection (planeDirectionAngle d) = d := by
  apply Prod.ext
  · exact Complex.norm_mul_cos_arg (Complex.equivRealProdCLM.symm d)
  · exact Complex.norm_mul_sin_arg (Complex.equivRealProdCLM.symm d)

lemma directionAngle_magnitude_pos {d : Point} (hd : d ≠ 0) :
    0 < ‖Complex.equivRealProdCLM.symm d‖ := by
  apply norm_pos_iff.mpr
  exact fun h => hd (Complex.equivRealProdCLM.symm.injective (by simpa only [map_zero] using h))

lemma sector_face_eq_left_halfBall {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (c : Point) {L ρ R α β r : ℝ}
    (hL : 0 < L) (hρ : ρ ∈ Ioo (0 : ℝ) R) (hαβ : α < β) (hr : 0 < r)
    {F H : Face D}
    (hF : OnePoint.some '' angularSector c R α β ⊆ faceRegion D F)
    (hH : OnePoint.some ''
      lineHalfBall c (c + L • angleDirection α) (c + ρ • angleDirection α) r true ⊆
        faceRegion D H) : F = H := by
  obtain ⟨x,hxF,hxH⟩ := angularSector_meets_left_halfBall c hL hρ hαβ hr
  exact face_eq_of_mem_regions D (hF ⟨x,hxF,rfl⟩) (hH ⟨x,hxH,rfl⟩)

lemma sector_face_eq_right_halfBall {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (c : Point) {L ρ R α β r : ℝ}
    (hL : 0 < L) (hρ : ρ ∈ Ioo (0 : ℝ) R) (hαβ : α < β) (hr : 0 < r)
    {F H : Face D}
    (hF : OnePoint.some '' angularSector c R α β ⊆ faceRegion D F)
    (hH : OnePoint.some ''
      lineHalfBall c (c + L • angleDirection β) (c + ρ • angleDirection β) r false ⊆
        faceRegion D H) : F = H := by
  obtain ⟨x,hxF,hxH⟩ := angularSector_meets_right_halfBall c hL hρ hαβ hr
  exact face_eq_of_mem_regions D (hF ⟨x,hxF,rfl⟩) (hH ⟨x,hxH,rfl⟩)


variable {V : Type u} {G : SimpleGraph V}

/-- A finite family of positive radii has a common positive lower bound,
including the empty family. -/
lemma finite_positive_radius {α : Type*} [Finite α] (R : α → ℝ)
    (hR : ∀ a, 0 < R a) : ∃ r : ℝ, 0 < r ∧ ∀ a, r ≤ R a := by
  classical
  letI := Fintype.ofFinite α
  have h : ∀ s : Finset α, ∃ r : ℝ, 0 < r ∧ ∀ a ∈ s, r ≤ R a := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨r, hr, hrs⟩ := ih
      refine ⟨min r (R a), lt_min hr (hR a), ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hrs b hb)
  obtain ⟨r, hr, hrs⟩ := h Finset.univ
  exact ⟨r, hr, fun a => hrs a (Finset.mem_univ a)⟩

lemma drawing_common_vertex_radius_exists [Finite V] (D : PlaneEmbedding G) (v : V) :
    ∃ r : ℝ, 0 < r ∧
      (∀ w, vertexSegmentEndpoints D v w ≠ D.point v ∧
        segment ℝ (D.point v) (vertexSegmentEndpoints D v w) ⊆
          D.edge (incidentEdge v w)) ∧
      planeImage D ∩ Metric.ball (D.point v) r =
        ({D.point v} ∪ ⋃ w, segment ℝ (D.point v) (vertexSegmentEndpoints D v w)) ∩
          Metric.ball (D.point v) r ∧
      (∀ w, r ≤ vertexSectorRadius D v w) := by
  obtain ⟨R, hR, hq, hedge, hmodel⟩ :=
    Classical.choose_spec (plane_vertex_locally_segments D v)
  obtain ⟨S, hS, hSr⟩ := finite_positive_radius (vertexSectorRadius D v)
    (fun w => (vertexSectorFace_geometry D v w).1)
  refine ⟨min R S, lt_min hR hS, hq, ?_, ?_⟩
  · have hball : Metric.ball (D.point v) (min R S) ⊆ Metric.ball (D.point v) R :=
      Metric.ball_subset_ball (min_le_left _ _)
    ext x
    constructor
    · rintro ⟨hx, hxr⟩
      exact ⟨(hmodel ▸ (show x ∈ planeImage D ∩ Metric.ball (D.point v) R from
        ⟨hx, hball hxr⟩)).1, hxr⟩
    · rintro ⟨hx, hxr⟩
      exact ⟨((hmodel.symm) ▸ (show x ∈
        ({D.point v} ∪ ⋃ w, segment ℝ (D.point v) (vertexSegmentEndpoints D v w)) ∩
          Metric.ball (D.point v) R from ⟨hx, hball hxr⟩)).1, hxr⟩
  · exact fun w => (min_le_right _ _).trans (hSr w)

/-- A common radius controls the local star and every complementary sector at
one vertex. -/
def drawingVertexRadius [Finite V] (D : PlaneEmbedding G) (v : V) : ℝ :=
  (drawing_common_vertex_radius_exists D v).choose

lemma drawingVertexRadius_geometry [Finite V] (D : PlaneEmbedding G) (v : V) :
    0 < drawingVertexRadius D v ∧
      (∀ w, vertexSegmentEndpoints D v w ≠ D.point v ∧
        segment ℝ (D.point v) (vertexSegmentEndpoints D v w) ⊆
          D.edge (incidentEdge v w)) ∧
      planeImage D ∩ Metric.ball (D.point v) (drawingVertexRadius D v) =
        ({D.point v} ∪ ⋃ w, segment ℝ (D.point v) (vertexSegmentEndpoints D v w)) ∩
          Metric.ball (D.point v) (drawingVertexRadius D v) ∧
      (∀ w, drawingVertexRadius D v ≤ vertexSectorRadius D v w) :=
  (drawing_common_vertex_radius_exists D v).choose_spec

lemma drawingSideLabel_common_radius [Finite V] (D : PlaneEmbedding G) (d : G.Dart) :
    let w : G.neighborSet d.snd := ⟨d.fst,d.adj.symm⟩
    OnePoint.some '' angularSector (D.point d.snd) (drawingVertexRadius D d.snd)
      (vertexNeighborAngle D d.snd w)
      (FiniteCombinatorics.Graph.Plane.FaceSideAux.sectorEndAngle
        (vertexNeighborAngle D d.snd w)
        (vertexNeighborAngle D d.snd ((drawingRotation D).turn d.snd w))) ⊆
          faceRegion D (drawingSideLabel D d) := by
  dsimp only
  intro x hx
  apply (vertexSectorFace_geometry D d.snd ⟨d.fst,d.adj.symm⟩).2.1
  exact Set.image_mono (angularSector_mono_radius _
    ((drawingVertexRadius_geometry D d.snd).2.2.2 ⟨d.fst,d.adj.symm⟩) _ _) hx


variable {V : Type u} {G : SimpleGraph V}

lemma drawingVertexRadius_local_star [Finite V] (D : PlaneEmbedding G) (v : V) :
    0 < drawingVertexRadius D v ∧
      (∀ w, vertexSegmentEndpoints D v w ≠ D.point v ∧
        segment ℝ (D.point v) (vertexSegmentEndpoints D v w) ⊆
          D.edge (incidentEdge v w)) ∧
      planeImage D ∩ Metric.ball (D.point v) (drawingVertexRadius D v) =
        ({D.point v} ∪ ⋃ w, segment ℝ (D.point v) (vertexSegmentEndpoints D v w)) ∩
          Metric.ball (D.point v) (drawingVertexRadius D v) ∧
      FiniteCombinatorics.Graph.Plane.FaceSideAux.IsAngularTurn (D.point v)
        (vertexSegmentEndpoints D v) ((drawingRotation D).turn v) := by
  have h := drawingVertexRadius_geometry D v
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  exact ⟨angleList (vertexNeighborAngle D v) (vertexNeighborAngle_injective D v),
    angleList_nodup _ _, mem_angleList _ _, angleList_pairwise _ _, rfl⟩

/-- The remaining geometric obligations for this fixed, concretely constructed
rotation and face labeling suffice for the complete directed-side conclusion. -/
theorem face_sides_of_drawing_label_compatibility
    (hsurj : ∀ {W : Type u} [Finite W] {H : SimpleGraph W} (D : PlaneEmbedding H),
      H.Connected → 3 ≤ Nat.card W → Function.Surjective (drawingSideLabel D))
    (hinv : ∀ {W : Type u} [Finite W] {H : SimpleGraph W} (D : PlaneEmbedding H),
      H.Connected → 3 ≤ Nat.card W → ∀ d,
        drawingSideLabel D (sideSuccessor (drawingRotation D) d) = drawingSideLabel D d) :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.face_sidesType.{u} := by
  intro V _ G D hc hv
  refine ⟨drawingRotation D, drawingSideLabel D, vertexSegmentEndpoints D,
    drawingVertexRadius D, drawingVertexRadius_local_star D,
    drawingSideLabel_common_radius D, hsurj D hc hv, hinv D hc hv, ?_, ?_⟩
  · intro d
    exact ⟨boundary_length_ge_three hc hv (drawingRotation D) d,
      fun hb => ⟨boundaryLength_even hb (drawingRotation D) d,
        boundary_length_ge_four hc hv hb (drawingRotation D) d⟩,
      boundary_walk_orbit (drawingRotation D) d⟩
  · exact face_bounds_of_assignment D hc hv (drawingRotation D) (drawingSideLabel D)
      (hsurj D hc hv) (hinv D hc hv)

/-- The full directed-side conclusion implies exactly the unconditional numerical
bounds reserved for this goal. -/
theorem face_bounds_of_face_sides
    (h : FiniteCombinatorics.Graph.Plane.FaceSideAux.face_sidesType.{u}) :
    Specs.FiniteCombinatorics.Graph.Plane.FaceSides.face_boundsType.{u} := by
  intro V _ G D hc hv
  obtain ⟨R, label, q, r, hstar, hsector, hsurj, hinv, hwalk, hfinite, hthree, hfour⟩ :=
    h D hc hv
  exact ⟨hthree, hfour⟩


lemma angularSector_meets_center_left_halfBall (c : Point) {L R α β r : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hαβ : α < β) (hr : 0 < r) :
    (angularSector c R α β ∩
      lineHalfBall c (c + L • angleDirection α) c r true).Nonempty := by
  obtain ⟨t,ht⟩ := nonempty_Ioo.mpr (lt_min hαβ (by linarith [Real.pi_pos]) :
    α < min β (α + Real.pi))
  let ρ := min R r / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρR : ρ < R := by dsimp [ρ]; linarith [min_le_left R r]
  have hρr : ρ < r := by dsimp [ρ]; linarith [min_le_right R r]
  let y := c + ρ • angleDirection t
  have hy : y ∈ angularSector c R α β :=
    ⟨(ρ,t),⟨⟨hρ,hρR⟩,⟨ht.1,ht.2.trans_le (min_le_left _ _)⟩⟩,rfl⟩
  refine ⟨y,hy,?_,?_⟩
  · change dist (c + ρ • angleDirection t) c < r
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    exact (mul_le_of_le_one_right hρ.le (angleDirection_norm_le_one t)).trans_lt hρr
  · change 0 < planeDet c (c + L • angleDirection α) (c + ρ • angleDirection t)
    rw [planeDet_polar]
    apply mul_pos (mul_pos hL hρ)
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [ht.1]
    · have := ht.2.trans_le (min_le_right β (α + Real.pi))
      linarith

lemma angularSector_meets_center_right_halfBall (c : Point) {L R α β r : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hαβ : α < β) (hr : 0 < r) :
    (angularSector c R α β ∩
      lineHalfBall c (c + L • angleDirection β) c r false).Nonempty := by
  obtain ⟨t,ht⟩ := nonempty_Ioo.mpr (max_lt hαβ (by linarith [Real.pi_pos]) :
    max α (β - Real.pi) < β)
  let ρ := min R r / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρR : ρ < R := by dsimp [ρ]; linarith [min_le_left R r]
  have hρr : ρ < r := by dsimp [ρ]; linarith [min_le_right R r]
  let y := c + ρ • angleDirection t
  have hy : y ∈ angularSector c R α β :=
    ⟨(ρ,t),⟨⟨hρ,hρR⟩,⟨(le_max_left _ _).trans_lt ht.1,ht.2⟩⟩,rfl⟩
  refine ⟨y,hy,?_,?_⟩
  · change dist (c + ρ • angleDirection t) c < r
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    exact (mul_le_of_le_one_right hρ.le (angleDirection_norm_le_one t)).trans_lt hρr
  · change planeDet c (c + L • angleDirection β) (c + ρ • angleDirection t) < 0
    rw [planeDet_polar]
    apply mul_neg_of_pos_of_neg (mul_pos hL hρ)
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · linarith [ht.2]
    · have := (le_max_right α (β - Real.pi)).trans_lt ht.1
      linarith

lemma sector_face_eq_center_left_halfBall {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (c : Point) {L R α β r : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hαβ : α < β) (hr : 0 < r)
    {F H : Face D}
    (hF : OnePoint.some '' angularSector c R α β ⊆ faceRegion D F)
    (hH : OnePoint.some '' lineHalfBall c (c + L • angleDirection α) c r true ⊆
        faceRegion D H) : F = H := by
  obtain ⟨x,hxF,hxH⟩ := angularSector_meets_center_left_halfBall c hL hR hαβ hr
  exact face_eq_of_mem_regions D (hF ⟨x,hxF,rfl⟩) (hH ⟨x,hxH,rfl⟩)

lemma sector_face_eq_center_right_halfBall {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (c : Point) {L R α β r : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hαβ : α < β) (hr : 0 < r)
    {F H : Face D}
    (hF : OnePoint.some '' angularSector c R α β ⊆ faceRegion D F)
    (hH : OnePoint.some '' lineHalfBall c (c + L • angleDirection β) c r false ⊆
        faceRegion D H) : F = H := by
  obtain ⟨x,hxF,hxH⟩ := angularSector_meets_center_right_halfBall c hL hR hαβ hr
  exact face_eq_of_mem_regions D (hF ⟨x,hxF,rfl⟩) (hH ⟨x,hxH,rfl⟩)

lemma planeDet_shift_smul (a b x y : Point) (k : ℝ) (hx : planeDet a b x = 0) :
    planeDet x (x + k • (b-a)) y = k * planeDet a b y := by
  dsimp [planeDet,FiniteCombinatorics.Graph.Plane.FaceSideAux.planeDet] at hx ⊢
  nlinarith [mul_eq_zero_of_left hx k]

lemma lineHalfBall_shift_smul (a b x : Point) (k r : ℝ)
    (hx : planeDet a b x = 0) (hk : 0 < k) (positive : Bool) :
    lineHalfBall x (x + k • (b-a)) x r positive = lineHalfBall a b x r positive := by
  ext y
  simp only [lineHalfBall,FiniteCombinatorics.Graph.Plane.FaceSideAux.lineHalfBall,
    mem_inter_iff,mem_ofPred_eq,planeDet_shift_smul a b x y k hx]
  have hneg : k * planeDet a b y < 0 ↔ planeDet a b y < 0 := by
    simpa only [mul_zero] using (mul_lt_mul_iff_of_pos_left hk :
      k * planeDet a b y < k * 0 ↔ planeDet a b y < 0)
  cases positive <;> simp only [Bool.false_eq_true,reduceIte,hneg,mul_pos_iff_of_pos_left hk]



open Set
open FiniteCombinatorics.Graph.Plane.FaceSideAux (sectorEndAngle)

lemma angleDirection_add_two_pi (t : ℝ) :
    angleDirection (t + 2 * Real.pi) = angleDirection t := by
  simp [angleDirection, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Any direction distinct from the finite sorted directions lies in a cyclic
consecutive gap, after adding a full turn if necessary. -/
lemma sorted_cyclic_angle_cover {A : Type*} (θ : A → ℝ) (L : List A)
    (hL : L.Pairwise (fun a b => θ a < θ b)) (hmem : ∀ a, a ∈ L)
    (hpos : 0 < L.length) (hrange : ∀ a, θ a ∈ Ioc (-Real.pi) Real.pi)
    {t : ℝ} (ht : t ∈ Ioc (-Real.pi) Real.pi) (hne : ∀ a, θ a ≠ t) :
    ∃ (j : ℕ) (hj : j < L.length) (t' : ℝ),
      θ (L[j]'hj) < t' ∧
      t' < sectorEndAngle (θ (L[j]'hj))
        (θ (L[(j+1)%L.length]'(Nat.mod_lt _ hpos))) ∧
      angleDirection t' = angleDirection t := by
  classical
  let s : Finset ℕ := (Finset.range L.length).filter fun i =>
    ∃ hi : i < L.length, θ (L[i]'hi) < t
  have hslast : θ (L[0]'hpos) ≤ θ (L[L.length-1]'(by omega)) :=
    (sorted_angle_extrema θ L hL hmem hpos (L[0]'hpos)).2
  have hwrap : sectorEndAngle (θ (L[L.length-1]'(by omega))) (θ (L[0]'hpos)) =
      θ (L[0]'hpos) + 2 * Real.pi := by
    exact if_neg (not_lt_of_ge hslast)
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hjmem : j ∈ s := Finset.max'_mem _ _
    have hj : j < L.length := Finset.mem_range.mp (Finset.mem_filter.mp hjmem).1
    have hjt : θ (L[j]'hj) < t := by
      obtain ⟨hji, hi⟩ := (Finset.mem_filter.mp hjmem).2
      exact hi
    by_cases hjnext : j+1 < L.length
    · have hnt : ¬ θ (L[j+1]'hjnext) < t := by
        intro hnext
        have hnmem : j+1 ∈ s := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hjnext, ⟨hjnext,hnext⟩⟩
        have hmax := Finset.le_max' s (j+1) hnmem
        change j+1 ≤ j at hmax
        omega
      have htlt : t < θ (L[j+1]'hjnext) :=
        lt_of_le_of_ne (le_of_not_gt hnt) (hne _).symm
      refine ⟨j,hj,t,hjt,?_,rfl⟩
      simpa only [Nat.mod_eq_of_lt hjnext, sectorEndAngle, if_pos (hjt.trans htlt)] using htlt
    · have hjlast : j = L.length-1 := by omega
      have hn : (L.length-1+1)%L.length = 0 := by
        rw [show L.length-1+1=L.length by omega, Nat.mod_self]
      have hjt' : θ (L[L.length-1]'(by omega)) < t := by
        simpa only [hjlast] using hjt
      refine ⟨L.length-1,by omega,t,hjt',?_,rfl⟩
      simp only [hn,hwrap]
      linarith [(hrange (L[0]'hpos)).1, ht.2]
  · have hfirst : t < θ (L[0]'hpos) := by
      have hnot : ¬ θ (L[0]'hpos) < t := by
        intro hfirst
        exact hs ⟨0, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hpos, ⟨hpos,hfirst⟩⟩⟩
      exact lt_of_le_of_ne (le_of_not_gt hnot) (hne _).symm
    have hn : (L.length-1+1)%L.length = 0 := by
      rw [show L.length-1+1=L.length by omega, Nat.mod_self]
    refine ⟨L.length-1,by omega,t+2*Real.pi,?_,?_,angleDirection_add_two_pi t⟩
    · linarith [(hrange (L[L.length-1]'(by omega))).2, ht.1]
    · simp only [hn,hwrap]
      linarith

variable {V : Type u} {G : SimpleGraph V}

lemma point_polar_reconstruction (d : Point) :
    ‖Complex.equivRealProdCLM.symm d‖ • angleDirection (planeDirectionAngle d) = d := by
  apply Prod.ext
  · exact Complex.norm_mul_cos_arg (Complex.equivRealProdCLM.symm d)
  · exact Complex.norm_mul_sin_arg (Complex.equivRealProdCLM.symm d)

lemma complex_norm_point_le_twice (d : Point) :
    ‖Complex.equivRealProdCLM.symm d‖ ≤ 2 * ‖d‖ := by
  have h := Complex.norm_le_abs_re_add_abs_im (Complex.equivRealProdCLM.symm d)
  change ‖Complex.equivRealProdCLM.symm d‖ ≤ |d.1|+|d.2| at h
  rw [Prod.norm_def]
  calc
    _ ≤ |d.1|+|d.2| := h
    _ ≤ 2 * max ‖d.1‖ ‖d.2‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      nlinarith [le_max_left |d.1| |d.2|, le_max_right |d.1| |d.2|]

/-- Complementary directions at a vertex are covered by the actual consecutive
angular sectors of its rotation, with a common radial bound. -/
lemma drawing_angularSector_cover [Finite V] (D : PlaneEmbedding G) (v : V)
    [Nonempty (G.neighborSet v)] {R : ℝ} {x : Point}
    (hx : ‖Complex.equivRealProdCLM.symm (x-D.point v)‖ < R)
    (hnray : ∀ w, ¬ SameRay ℝ (x-D.point v) (vertexSegmentEndpoints D v w-D.point v)) :
    ∃ w : G.neighborSet v,
      x ∈ angularSector (D.point v) R (vertexNeighborAngle D v w)
        (sectorEndAngle (vertexNeighborAngle D v w)
          (vertexNeighborAngle D v ((drawingRotation D).turn v w))) := by
  let θ := vertexNeighborAngle D v
  let L := angleList θ (vertexNeighborAngle_injective D v)
  have hpos : 0 < L.length := by
    obtain ⟨w⟩ := ‹Nonempty (G.neighborSet v)›
    exact List.length_pos_of_mem (mem_angleList θ (vertexNeighborAngle_injective D v) w)
  have hrange (w) : θ w ∈ Ioc (-Real.pi) Real.pi :=
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  let t := planeDirectionAngle (x-D.point v)
  have ht : t ∈ Ioc (-Real.pi) Real.pi :=
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have hne (w) : θ w ≠ t := by
    intro he
    exact hnray w (planeDirectionAngle_eq_implies_sameRay he.symm)
  obtain ⟨j,hj,t',hjlt,ht'lt,heq⟩ := sorted_cyclic_angle_cover θ L
    (angleList_pairwise _ _) (mem_angleList _ _) hpos hrange ht hne
  refine ⟨L[j],?_,⟩
  have hturn : (drawingRotation D).turn v (L[j]'hj) =
      L[(j+1)%L.length]'(Nat.mod_lt _ hpos) :=
    angleTurn_apply_getElem θ (vertexNeighborAngle_injective D v) j hj
  have hd : x-D.point v ≠ 0 := by
    intro he
    obtain ⟨w⟩ := ‹Nonempty (G.neighborSet v)›
    exact hnray w (he ▸ SameRay.zero_left _)
  have hcomplex : Complex.equivRealProdCLM.symm (x-D.point v) ≠ 0 := by
    intro hzero
    apply hd
    exact Complex.equivRealProdCLM.symm.injective (by simpa using hzero)
  refine ⟨(‖Complex.equivRealProdCLM.symm (x-D.point v)‖,t'),
    ⟨⟨norm_pos_iff.mpr hcomplex,hx⟩,⟨hjlt,?_⟩⟩,?_⟩
  · simpa only [hturn] using ht'lt
  · change D.point v + ‖Complex.equivRealProdCLM.symm (x-D.point v)‖ • angleDirection t' = x
    rw [heq, point_polar_reconstruction]
    exact add_sub_cancel _ _

/-- On a fixed ray, a point no farther from its center than the endpoint
belongs to the corresponding segment. -/
lemma mem_segment_of_sameRay_norm_le {c q x : Point} (hq : q ≠ c)
    (hray : SameRay ℝ (x-c) (q-c)) (hnorm : ‖x-c‖ ≤ ‖q-c‖) :
    x ∈ segment ℝ c q := by
  obtain ⟨t, ht, htx⟩ := hray.symm.exists_nonneg_left (sub_ne_zero.mpr hq)
  have hqn : 0 < ‖q-c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
  have hnorm' : t * ‖q-c‖ ≤ ‖q-c‖ := by
    simpa only [← htx, norm_smul_of_nonneg ht] using hnorm
  have ht1 : t ≤ 1 := by nlinarith
  rw [segment_eq_image_lineMap]
  refine ⟨t,⟨ht,ht1⟩,?_⟩
  rw [AffineMap.lineMap_apply_module',htx]
  exact sub_add_cancel _ _

/-- A sufficiently short complementary displacement is distinct from every
outgoing ray; finite endpoint lengths give a common neighborhood. -/
lemma drawing_no_ray_neighborhood [Finite V] (D : PlaneEmbedding G) (v : V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.ball (D.point v) ε,
      x ∉ planeImage D → ∀ w,
        ¬ SameRay ℝ (x-D.point v) (vertexSegmentEndpoints D v w-D.point v) := by
  obtain ⟨ε,hε,hεq⟩ := finite_positive_radius
    (fun w => ‖vertexSegmentEndpoints D v w-D.point v‖)
    (fun w => norm_pos_iff.mpr (sub_ne_zero.mpr (vertexSegmentEndpoints_properties D v w).1))
  refine ⟨ε,hε,?_⟩
  intro x hx hxc w hray
  have hnorm : ‖x-D.point v‖ ≤ ‖vertexSegmentEndpoints D v w-D.point v‖ :=
    ((show ‖x-D.point v‖ < ε from hx).trans_le (hεq w)).le
  have hxseg := mem_segment_of_sameRay_norm_le
    (vertexSegmentEndpoints_properties D v w).1 hray hnorm
  exact hxc (Or.inr (mem_iUnion.mpr ⟨incidentEdge v w,
    (vertexSegmentEndpoints_properties D v w).2 hxseg⟩))

/-- The actual angular sectors of the chosen vertex labels cover a
neighborhood of that vertex in the drawing complement. -/
lemma drawing_sector_cover_neighborhood [Finite V] (D : PlaneEmbedding G) (v : V)
    [Nonempty (G.neighborSet v)] :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (D.point v) ε ∩ (planeImage D)ᶜ ⊆
        ⋃ w, angularSector (D.point v) (drawingVertexRadius D v)
          (vertexNeighborAngle D v w)
          (sectorEndAngle (vertexNeighborAngle D v w)
            (vertexNeighborAngle D v ((drawingRotation D).turn v w))) := by
  obtain ⟨δ,hδ,hnray⟩ := drawing_no_ray_neighborhood D v
  let ε := min δ (drawingVertexRadius D v / 2)
  have hR : 0 < drawingVertexRadius D v := (drawingVertexRadius_geometry D v).1
  refine ⟨ε, lt_min hδ (by positivity), ?_⟩
  rintro x ⟨hx,hxc⟩
  have hxδ : x ∈ Metric.ball (D.point v) δ :=
    Metric.ball_subset_ball (min_le_left _ _) hx
  have hnorm : ‖x-D.point v‖ < drawingVertexRadius D v / 2 :=
    (show ‖x-D.point v‖ < ε from hx).trans_le (min_le_right _ _)
  have hcomplex : ‖Complex.equivRealProdCLM.symm (x-D.point v)‖ <
      drawingVertexRadius D v :=
    (complex_norm_point_le_twice _).trans_lt (by linarith)
  obtain ⟨w,hw⟩ := drawing_angularSector_cover D v hcomplex (hnray x hxδ hxc)
  exact mem_iUnion.mpr ⟨w,hw⟩

/-- An actual face approaching a nonisolated vertex contains one of its
constructed angular sectors, and hence equals its sector label. -/
lemma face_eq_vertexSectorFace_of_vertex_frontier [Finite V] (D : PlaneEmbedding G)
    (v : V) [Nonempty (G.neighborSet v)] (F : Face D)
    (hvF : OnePoint.some (D.point v) ∈ frontier (faceRegion D F)) :
    ∃ w : G.neighborSet v, F = vertexSectorFace D v w := by
  obtain ⟨ε,hε,hcover⟩ := drawing_sector_cover_neighborhood D v
  let C : G.neighborSet v → Set Sphere := fun w =>
    OnePoint.some '' angularSector (D.point v) (drawingVertexRadius D v)
      (vertexNeighborAngle D v w)
      (sectorEndAngle (vertexNeighborAngle D v w)
        (vertexNeighborAngle D v ((drawingRotation D).turn v w)))
  have hCF (w : G.neighborSet v) : C w ⊆ faceRegion D (vertexSectorFace D v w) := by
    intro x hx
    apply (vertexSectorFace_geometry D v w).2.1
    exact Set.image_mono (angularSector_mono_radius _
      ((drawingVertexRadius_geometry D v).2.2.2 w) _ _) hx
  have hCs (w : G.neighborSet v) : C w ⊆ (sphereImage D)ᶜ :=
    fun _ hx => face_region_subset D _ (hCF w hx)
  have hCconn (w : G.neighborSet v) : IsPreconnected (C w) :=
    (angularSector_isPreconnected _ _ _ _).image _ OnePoint.continuous_coe.continuousOn
  have hcover' : (OnePoint.some '' Metric.ball (D.point v) ε) ∩ (sphereImage D)ᶜ ⊆ ⋃ w, C w := by
    rintro _ ⟨⟨x,hx,rfl⟩,hxc⟩
    have hxpc : x ∉ planeImage D :=
      fun hxg => hxc ((sphere_image_membership D x).mpr hxg)
    obtain ⟨w,hw⟩ := mem_iUnion.mp (hcover ⟨hx,hxpc⟩)
    exact mem_iUnion.mpr ⟨w,x,hw,rfl⟩
  obtain ⟨w, ⟨x,hx⟩, hw⟩ := face_contains_local_patch D F
    (frontier_subset_closure hvF)
    (OnePoint.isOpenEmbedding_coe.isOpenMap.image_mem_nhds
      (Metric.ball_mem_nhds (D.point v) hε)) C hCconn hCs hcover'
  exact ⟨w, face_eq_of_mem_regions D (hw hx) (hCF w hx)⟩



namespace PolygonalGeometry
open Set

/-- An injective continuous arc contains exactly the straight segment between two
of its parameter values whenever that segment is contained in the whole arc. -/
theorem subarc_image_eq_segment
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    (s t : unitInterval) (hst : s < t)
    (hseg : segment ℝ (p s) (p t) ⊆ range p) :
    p '' Icc s t = segment ℝ (p s) (p t) := by
  have hind := hp.isClosedEmbedding hpi |>.isEmbedding.isInducing
  have heq : p '' (p ⁻¹' segment ℝ (p s) (p t)) = segment ℝ (p s) (p t) :=
    image_preimage_eq_of_subset hseg
  have hc : IsPreconnected (p ⁻¹' segment ℝ (p s) (p t)) := by
    apply hind.isPreconnected_image.mp
    rw [heq]
    exact (convex_segment _ _).isPreconnected
  have hsub : p '' Icc s t ⊆ segment ℝ (p s) (p t) := by
    rintro _ ⟨z,hz,rfl⟩
    exact hc.Icc_subset (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _) hz
  apply Subset.antisymm hsub
  have hne : p s ≠ p t := hpi.ne hst.ne
  let q : unitInterval → ℝ := SegmentRegularity.parameter (p s) (p t) ∘ p
  have hqc : Continuous q := (SegmentRegularity.continuous_parameter _ _).comp hp
  have hq0 : q s = 0 := by
    change SegmentRegularity.parameter (p s) (p t) (p s) = 0
    simpa only [AffineMap.lineMap_apply_zero] using
      SegmentRegularity.parameter_lineMap _ _ hne 0
  have hq1 : q t = 1 := by
    change SegmentRegularity.parameter (p s) (p t) (p t) = 1
    simpa only [AffineMap.lineMap_apply_one] using
      SegmentRegularity.parameter_lineMap _ _ hne 1
  have hI : Icc (0:ℝ) 1 ⊆ q '' Icc s t := by
    apply (isPreconnected_Icc.image q hqc.continuousOn).Icc_subset
    · exact ⟨s,⟨le_rfl,hst.le⟩,hq0⟩
    · exact ⟨t,⟨hst.le,le_rfl⟩,hq1⟩
  intro y hy
  rw [segment_eq_image_lineMap] at hy
  obtain ⟨k,hk,rfl⟩ := hy
  obtain ⟨z,hz,hqz⟩ := hI hk
  refine ⟨z,hz,?_⟩
  have hpz := hsub (mem_image_of_mem p hz)
  rw [segment_eq_image_lineMap] at hpz
  obtain ⟨j,hj,hjz⟩ := hpz
  have hjk : j = k := by
    change SegmentRegularity.parameter (p s) (p t) (p z) = k at hqz
    rw [← hjz, SegmentRegularity.parameter_lineMap _ _ hne] at hqz
    exact hqz
  rw [← hjz,hjk]

/-- At an interior parameter, a simple arc locally star convex in the ambient
plane has a genuine two-segment ambient model. -/
theorem arc_interior_locally_two_segments
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    (t : unitInterval) (ht0 : 0 < t) (ht1 : t < 1)
    (hstar : ∃ r : ℝ, 0 < r ∧
      StarConvex ℝ (p t) (range p ∩ Metric.ball (p t) r)) :
    ∃ (s u : unitInterval) (δ : ℝ), s < t ∧ t < u ∧ 0 < δ ∧
      p '' Icc s t = segment ℝ (p s) (p t) ∧
      p '' Icc t u = segment ℝ (p t) (p u) ∧
      segment ℝ (p t) (p s) ∩ segment ℝ (p t) (p u) = {p t} ∧
      range p ∩ Metric.ball (p t) δ =
        (segment ℝ (p t) (p s) ∪ segment ℝ (p t) (p u)) ∩ Metric.ball (p t) δ := by
  obtain ⟨r,hr,hstar⟩ := hstar
  have hneigh : p ⁻¹' Metric.ball (p t) r ∈ nhds t :=
    hp.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hr)
  obtain ⟨ρ,hρ,hρsub⟩ := Metric.mem_nhds_iff.mp hneigh
  let ε : ℝ := min (ρ/2) (min ((t:ℝ)/2) ((1-(t:ℝ))/2))
  have ht0r : 0 < (t:ℝ) := ht0
  have ht1r : (t:ℝ) < 1 := ht1
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hερ : ε < ρ := (min_le_left _ _).trans_lt (by linarith)
  have hεt : ε ≤ (t:ℝ)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ (1-(t:ℝ))/2 := (min_le_right _ _).trans (min_le_right _ _)
  let s : unitInterval := ⟨(t:ℝ)-ε,by constructor <;> linarith [t.property.2]⟩
  let u : unitInterval := ⟨(t:ℝ)+ε,by constructor <;> linarith [t.property.1]⟩
  have hst : s < t := by change (t:ℝ)-ε < (t:ℝ); linarith
  have htu : t < u := by change (t:ℝ) < (t:ℝ)+ε; linarith
  have hsρ : s ∈ Metric.ball t ρ := by
    change dist ((t:ℝ)-ε) (t:ℝ) < ρ
    rw [Real.dist_eq]
    have he : (t:ℝ)-ε-(t:ℝ) = -ε := by ring
    rw [he,abs_neg,abs_of_pos hε]
    exact hερ
  have huρ : u ∈ Metric.ball t ρ := by
    change dist ((t:ℝ)+ε) (t:ℝ) < ρ
    rw [Real.dist_eq]
    have he : (t:ℝ)+ε-(t:ℝ) = ε := by ring
    rw [he,abs_of_pos hε]
    exact hερ
  have hsseg : segment ℝ (p t) (p s) ⊆ range p :=
    fun _ hy => (hstar.segment_subset ⟨mem_range_self _,hρsub hsρ⟩ hy).1
  have huseg : segment ℝ (p t) (p u) ⊆ range p :=
    fun _ hy => (hstar.segment_subset ⟨mem_range_self _,hρsub huρ⟩ hy).1
  have hleft : p '' Icc s t = segment ℝ (p s) (p t) :=
    subarc_image_eq_segment p hp hpi s t hst (by simpa [segment_symm] using hsseg)
  have hright : p '' Icc t u = segment ℝ (p t) (p u) :=
    subarc_image_eq_segment p hp hpi t u htu huseg
  let K : Set Point := p '' Icc 0 s ∪ p '' Icc u 1
  have hK : IsClosed K :=
    ((isCompact_Icc.image hp).union (isCompact_Icc.image hp)).isClosed
  have htK : p t ∉ K := by
    rintro (⟨z,hz,hzt⟩ | ⟨z,hz,hzt⟩)
    · exact (not_le_of_gt hst) ((hpi hzt) ▸ hz.2)
    · exact (not_le_of_gt htu) ((hpi hzt) ▸ hz.1)
  obtain ⟨δ,hδ,hδsub⟩ := Metric.isOpen_iff.mp hK.isOpen_compl (p t) htK
  refine ⟨s,u,δ,hst,htu,hδ,hleft,hright,?_,?_⟩
  · rw [segment_symm ℝ (p t) (p s),← hleft,← hright]
    ext y
    constructor
    · rintro ⟨⟨z,hz,rfl⟩,⟨w,hw,hwz⟩⟩
      have he : w = z := hpi hwz
      have hzt : z = t := le_antisymm hz.2 (he ▸ hw.1)
      simpa only [hzt,mem_singleton_iff]
    · rintro rfl
      exact ⟨⟨t,⟨hst.le,le_rfl⟩,rfl⟩,⟨t,⟨le_rfl,htu.le⟩,rfl⟩⟩
  · ext y
    constructor
    · rintro ⟨⟨z,rfl⟩,hzδ⟩
      have hsz : s ≤ z := by
        by_contra h
        exact hδsub hzδ (Or.inl ⟨z,⟨z.property.1,(le_of_not_ge h)⟩,rfl⟩)
      have hzu : z ≤ u := by
        by_contra h
        exact hδsub hzδ (Or.inr ⟨z,⟨(le_of_not_ge h),z.property.2⟩,rfl⟩)
      refine ⟨?_,hzδ⟩
      rcases le_total z t with hzt | htz
      · left
        rw [segment_symm,← hleft]
        exact ⟨z,⟨hsz,hzt⟩,rfl⟩
      · right
        rw [← hright]
        exact ⟨z,⟨htz,hzu⟩,rfl⟩
    · rintro ⟨(hy|hy),hyδ⟩
      · exact ⟨hsseg hy,hyδ⟩
      · exact ⟨huseg hy,hyδ⟩

/-- Polygonality is imposed on the image only; no assumption on the speed or
piecewise linearity of the supplied parametrization is used. -/
theorem polygonal_arc_interior_locally_two_segments
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    (hpoly : IsPolygonal (range p))
    (t : unitInterval) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ (s u : unitInterval) (δ : ℝ), s < t ∧ t < u ∧ 0 < δ ∧
      p '' Icc s t = segment ℝ (p s) (p t) ∧
      p '' Icc t u = segment ℝ (p t) (p u) ∧
      segment ℝ (p t) (p s) ∩ segment ℝ (p t) (p u) = {p t} ∧
      range p ∩ Metric.ball (p t) δ =
        (segment ℝ (p t) (p s) ∪ segment ℝ (p t) (p u)) ∩ Metric.ball (p t) δ := by
  obtain ⟨n,A,B,hpoly⟩ := hpoly
  apply arc_interior_locally_two_segments p hp hpi t ht0 ht1
  rw [hpoly]
  apply finite_closed_convex_union_locally_starConvex
    (fun i => segment ℝ (A i) (B i))
  · intro i
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  · exact fun i => convex_segment _ _
  · rw [← hpoly]
    exact mem_range_self t

end PolygonalGeometry

open Set

/-- Away from the vertex images, a sufficiently small ambient ball isolates
one whole original edge from every other edge of the drawing. -/
theorem plane_image_locally_edge
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (e : G.edgeSet) (x : Point) (he : x ∈ D.edge e)
    (hn : x ∉ range D.point) :
    ∃ r : ℝ, 0 < r ∧ planeImage D ∩ Metric.ball x r = D.edge e ∩ Metric.ball x r := by
  classical
  let K : Set Point := range D.point ∪ ⋃ f : {f : G.edgeSet // f ≠ e}, D.edge f.val
  have hK : IsClosed K :=
    ((finite_range D.point).isCompact.union
      (isCompact_iUnion fun f : {f : G.edgeSet // f ≠ e} => edge_compact D f.val)).isClosed
  have hxK : x ∉ K := by
    rintro (hx | hx)
    · exact hn hx
    · obtain ⟨f,hf⟩ := mem_iUnion.mp hx
      exact f.property (edge_eq_of_common_nonvertex D hf he hn)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl x hxK
  refine ⟨r,hr,?_⟩
  ext y
  constructor
  · rintro ⟨hy,hyr⟩
    refine ⟨?_,hyr⟩
    rcases hy with hy | hy
    · exact False.elim (hball hyr (Or.inl hy))
    · obtain ⟨f,hf⟩ := mem_iUnion.mp hy
      by_cases hfe : f = e
      · exact hfe ▸ hf
      · exact False.elim (hball hyr (Or.inr (mem_iUnion.mpr ⟨⟨f,hfe⟩,hf⟩)))
  · rintro ⟨hy,hyr⟩
    exact ⟨Or.inr (mem_iUnion.mpr ⟨e,hy⟩),hyr⟩

/-- The whole drawing, at every nonvertex edge point, has exactly the two
straight rays determined by the two ordered portions of that edge. -/
theorem plane_edge_interior_locally_two_segments
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (e : G.edgeSet) (x : Point) (he : x ∈ D.edge e)
    (hn : x ∉ range D.point) :
    ∃ (a b : Point) (r : ℝ), a ≠ x ∧ b ≠ x ∧ 0 < r ∧
      segment ℝ x a ⊆ D.edge e ∧ segment ℝ x b ⊆ D.edge e ∧
      segment ℝ x a ∩ segment ℝ x b = {x} ∧
      planeImage D ∩ Metric.ball x r =
        (segment ℝ x a ∪ segment ℝ x b) ∩ Metric.ball x r := by
  obtain ⟨⟨v,w⟩,hvw⟩ := Sym2.mk_surjective e.val
  have hadj : G.Adj v w := by simpa [← hvw] using e.property
  have heq : e = ⟨s(v,w),hadj⟩ := Subtype.ext hvw.symm
  obtain ⟨hpoly,p,hpi,hps⟩ := D.edge_arc v w hadj
  have hpr : range p = D.edge e := by simpa [← heq] using hps
  obtain ⟨t,htx⟩ := hpr ▸ he
  have ht0 : 0 < t := by
    apply lt_of_le_of_ne (show (0 : unitInterval) ≤ t from t.property.1)
    intro ht
    apply hn
    refine ⟨v,?_⟩
    rw [← htx,← ht,p.source]
  have ht1 : t < 1 := by
    apply lt_of_le_of_ne (show t ≤ (1 : unitInterval) from t.property.2)
    intro ht
    apply hn
    refine ⟨w,?_⟩
    rw [← htx,ht,p.target]
  have hpoly' : IsPolygonal (range p) := by rwa [hpr,heq]
  obtain ⟨s,u,δ,hst,htu,hδ,hleft,hright,hsep,hlocal⟩ :=
    PolygonalGeometry.polygonal_arc_interior_locally_two_segments
      p p.continuous hpi hpoly' t ht0 ht1
  obtain ⟨ρ,hρ,hlocalD⟩ := plane_image_locally_edge D e x he hn
  have hsegleft : segment ℝ x (p s) ⊆ D.edge e := by
    rw [← hpr,← htx,segment_symm,← hleft]
    exact image_subset_range p _
  have hsegright : segment ℝ x (p u) ⊆ D.edge e := by
    rw [← hpr,← htx,← hright]
    exact image_subset_range p _
  refine ⟨p s,p u,min δ ρ,?_,?_,lt_min hδ hρ,hsegleft,hsegright,?_,?_⟩
  · intro h
    exact hst.ne (hpi (h.trans htx.symm))
  · intro h
    exact htu.ne (hpi (htx.trans h.symm))
  · simpa only [htx] using hsep
  · rw [hpr,htx] at hlocal
    ext y
    constructor
    · rintro ⟨hy,hyr⟩
      have hyρ : y ∈ Metric.ball x ρ := Metric.ball_subset_ball (min_le_right _ _) hyr
      have hyδ : y ∈ Metric.ball x δ := Metric.ball_subset_ball (min_le_left _ _) hyr
      have hye : y ∈ D.edge e := (hlocalD ▸ (show y ∈ planeImage D ∩ Metric.ball x ρ from ⟨hy,hyρ⟩)).1
      exact ⟨(hlocal ▸ (show y ∈ D.edge e ∩ Metric.ball x δ from ⟨hye,hyδ⟩)).1,hyr⟩
    · rintro ⟨hy,hyr⟩
      have hye : y ∈ D.edge e := hy.elim (fun h => hsegleft h) (fun h => hsegright h)
      exact ⟨Or.inr (mem_iUnion.mpr ⟨e,hye⟩),hyr⟩



open Set
open FiniteCombinatorics.Graph.Plane.FaceSideAux (sectorEndAngle)

lemma directionAngle_lt_sectorEndAngle (a b : Point) :
    planeDirectionAngle a < sectorEndAngle (planeDirectionAngle a) (planeDirectionAngle b) := by
  unfold sectorEndAngle
  split_ifs with h
  · exact h
  · have ha := Complex.arg_le_pi (Complex.equivRealProdCLM.symm a)
    have hb := Complex.neg_pi_lt_arg (Complex.equivRealProdCLM.symm b)
    change planeDirectionAngle a ≤ Real.pi at ha
    change -Real.pi < planeDirectionAngle b at hb
    linarith

lemma two_direction_sector_no_ray (a b : Point) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ t ∈ Ioo (planeDirectionAngle a)
      (sectorEndAngle (planeDirectionAngle a) (planeDirectionAngle b)),
      ¬ SameRay ℝ (angleDirection t) a ∧ ¬ SameRay ℝ (angleDirection t) b := by
  intro t ht
  let α := planeDirectionAngle a
  let β := planeDirectionAngle b
  change t ∈ Ioo α (sectorEndAngle α β) at ht
  have ha0 : -Real.pi < α := Complex.neg_pi_lt_arg _
  have ha1 : α ≤ Real.pi := Complex.arg_le_pi _
  have hb0 : -Real.pi < β := Complex.neg_pi_lt_arg _
  have hb1 : β ≤ Real.pi := Complex.arg_le_pi _
  by_cases hαβ : α < β
  · rw [sectorEndAngle,ite_eq_left hαβ] at ht
    have htarg : t ∈ Ioc (-Real.pi) Real.pi := ⟨ha0.trans ht.1,ht.2.le.trans hb1⟩
    constructor
    · intro h
      have he := sameRay_trigDirection_angle ha htarg h
      change α = t at he
      exact ht.1.ne he
    · intro h
      have he := sameRay_trigDirection_angle hb htarg h
      change β = t at he
      exact ht.2.ne he.symm
  · rw [sectorEndAngle,ite_eq_right hαβ] at ht
    have hβα : β ≤ α := le_of_not_gt hαβ
    by_cases htpi : t ≤ Real.pi
    · have htarg : t ∈ Ioc (-Real.pi) Real.pi := ⟨ha0.trans ht.1,htpi⟩
      constructor
      · intro h
        have he := sameRay_trigDirection_angle ha htarg h
        change α = t at he
        exact ht.1.ne he
      · intro h
        have he := sameRay_trigDirection_angle hb htarg h
        change β = t at he
        exact (not_le_of_gt ht.1) (he ▸ hβα)
    · have htarg : t-2*Real.pi ∈ Ioc (-Real.pi) Real.pi := by
        constructor <;> linarith [ht.2]
      have hshift (d : Point) (h : SameRay ℝ (angleDirection t) d) :
          SameRay ℝ (angleDirection (t-2*Real.pi)) d := by
        simpa only [angleDirection,Real.cos_sub_two_pi,Real.sin_sub_two_pi] using h
      constructor
      · intro h
        have he := sameRay_trigDirection_angle ha htarg (hshift a h)
        change α = t-2*Real.pi at he
        linarith [ht.2]
      · intro h
        have he := sameRay_trigDirection_angle hb htarg (hshift b h)
        change β = t-2*Real.pi at he
        linarith [ht.2]

lemma existsUnique_two_ray_sector_face
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (c a b : Point) {r : ℝ} (ha : a ≠ c) (hb : b ≠ c) (hr : 0 < r)
    (hmodel : planeImage D ∩ Metric.ball c r =
      (segment ℝ c a ∪ segment ℝ c b) ∩ Metric.ball c r) :
    ∃! F : Face D,
      OnePoint.some '' angularSector c r (planeDirectionAngle (a-c))
        (sectorEndAngle (planeDirectionAngle (a-c)) (planeDirectionAngle (b-c))) ⊆
          faceRegion D F := by
  let q : Bool → Point := fun i => if i then b else a
  have hmodel' : planeImage D ∩ Metric.ball c r =
      ({c} ∪ ⋃ i, segment ℝ c (q i)) ∩ Metric.ball c r := by
    rw [hmodel]
    congr 1
    ext y
    constructor
    · rintro (h|h)
      · exact Or.inr (mem_iUnion.mpr ⟨false,h⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨true,h⟩)
    · rintro (h|h)
      · exact Or.inl ((mem_singleton_iff.mp h) ▸ left_mem_segment ℝ c a)
      · obtain ⟨i,hi⟩ := mem_iUnion.mp h
        cases i
        · exact Or.inl hi
        · exact Or.inr hi
  apply existsUnique_angularSector_face D c q hr (directionAngle_lt_sectorEndAngle _ _) hmodel'
  intro t ht i
  have hgap := two_direction_sector_no_ray (a-c) (b-c) (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb) t ht
  cases i
  · exact hgap.1
  · exact hgap.2

/-- An oriented interior chart of an original edge carries a uniquely determined
actual face in the counterclockwise sector from its backward to its forward ray. -/
theorem oriented_edge_interior_sector_face
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (e : G.edgeSet) (p : unitInterval → Point) (hp : Continuous p)
    (hpi : Function.Injective p) (hpr : range p = D.edge e)
    (hpoly : IsPolygonal (range p))
    (t : unitInterval) (ht0 : 0 < t) (ht1 : t < 1)
    (hn : p t ∉ range D.point) :
    ∃ (s u : unitInterval) (r : ℝ), s < t ∧ t < u ∧ 0 < r ∧
      p '' Icc s t = segment ℝ (p s) (p t) ∧
      p '' Icc t u = segment ℝ (p t) (p u) ∧
      segment ℝ (p t) (p s) ∩ segment ℝ (p t) (p u) = {p t} ∧
      planeImage D ∩ Metric.ball (p t) r =
        (segment ℝ (p t) (p s) ∪ segment ℝ (p t) (p u)) ∩ Metric.ball (p t) r ∧
      ∃! F : Face D,
        OnePoint.some '' angularSector (p t) r (planeDirectionAngle (p s-p t))
          (sectorEndAngle (planeDirectionAngle (p s-p t)) (planeDirectionAngle (p u-p t))) ⊆
            faceRegion D F := by
  obtain ⟨s,u,δ,hst,htu,hδ,hleft,hright,hsep,hlocal⟩ :=
    PolygonalGeometry.polygonal_arc_interior_locally_two_segments p hp hpi hpoly t ht0 ht1
  obtain ⟨ρ,hρ,hlocalD⟩ := plane_image_locally_edge D e (p t) (hpr ▸ mem_range_self t) hn
  have hsegleft : segment ℝ (p t) (p s) ⊆ D.edge e := by
    rw [← hpr,segment_symm,← hleft]
    exact image_subset_range p _
  have hsegright : segment ℝ (p t) (p u) ⊆ D.edge e := by
    rw [← hpr,← hright]
    exact image_subset_range p _
  have hmodel : planeImage D ∩ Metric.ball (p t) (min δ ρ) =
      (segment ℝ (p t) (p s) ∪ segment ℝ (p t) (p u)) ∩ Metric.ball (p t) (min δ ρ) := by
    rw [hpr] at hlocal
    ext y
    constructor
    · rintro ⟨hy,hyr⟩
      have hyρ : y ∈ Metric.ball (p t) ρ := Metric.ball_subset_ball (min_le_right _ _) hyr
      have hyδ : y ∈ Metric.ball (p t) δ := Metric.ball_subset_ball (min_le_left _ _) hyr
      have hye : y ∈ D.edge e := (hlocalD ▸ (show y ∈ planeImage D ∩ Metric.ball (p t) ρ from ⟨hy,hyρ⟩)).1
      exact ⟨(hlocal ▸ (show y ∈ D.edge e ∩ Metric.ball (p t) δ from ⟨hye,hyδ⟩)).1,hyr⟩
    · rintro ⟨hy,hyr⟩
      have hye : y ∈ D.edge e := hy.elim (fun h => hsegleft h) (fun h => hsegright h)
      exact ⟨Or.inr (mem_iUnion.mpr ⟨e,hye⟩),hyr⟩
  refine ⟨s,u,min δ ρ,hst,htu,lt_min hδ hρ,hleft,hright,hsep,hmodel,?_⟩
  exact existsUnique_two_ray_sector_face D (p t) (p s) (p u)
    (hpi.ne hst.ne) (hpi.ne htu.ne') (lt_min hδ hρ) hmodel



namespace PolygonalGeometry
open Set
open FiniteCombinatorics.Graph.Plane.FaceSideAux (sectorEndAngle)

/-- The direction of an ordered straight subarc before a parameter is independent
of the size of that subarc. -/
theorem backward_subarc_sameRay
    {T : Type*} [LinearOrder T] (p : T → Point) (hpi : Function.Injective p)
    {s₁ s₂ t : T} (hs₁ : s₁ < t) (hs₂ : s₂ < t)
    (h₁ : p '' Icc s₁ t = segment ℝ (p s₁) (p t))
    (h₂ : p '' Icc s₂ t = segment ℝ (p s₂) (p t)) :
    SameRay ℝ (p s₁ - p t) (p s₂ - p t) := by
  let r := max s₁ s₂
  have hrt : r < t := max_lt hs₁ hs₂
  have h₁r : p r ∈ segment ℝ (p t) (p s₁) := by
    rw [segment_symm, ← h₁]
    exact ⟨r, ⟨le_max_left _ _, hrt.le⟩, rfl⟩
  have h₂r : p r ∈ segment ℝ (p t) (p s₂) := by
    rw [segment_symm, ← h₂]
    exact ⟨r, ⟨le_max_right _ _, hrt.le⟩, rfl⟩
  have hrne : p r - p t ≠ 0 := sub_ne_zero.mpr (hpi.ne hrt.ne)
  have hR₁ : SameRay ℝ (p r - p t) (p s₁ - p t) :=
    (mem_segment_iff_wbtw.mp h₁r).sameRay_vsub_left
  have hR₂ : SameRay ℝ (p r - p t) (p s₂ - p t) :=
    (mem_segment_iff_wbtw.mp h₂r).sameRay_vsub_left
  exact hR₁.symm.trans hR₂ (fun h => (hrne h).elim)

/-- The forward direction of an ordered straight subarc is independent of its size. -/
theorem forward_subarc_sameRay
    {T : Type*} [LinearOrder T] (p : T → Point) (hpi : Function.Injective p)
    {t u₁ u₂ : T} (hu₁ : t < u₁) (hu₂ : t < u₂)
    (h₁ : p '' Icc t u₁ = segment ℝ (p t) (p u₁))
    (h₂ : p '' Icc t u₂ = segment ℝ (p t) (p u₂)) :
    SameRay ℝ (p u₁ - p t) (p u₂ - p t) := by
  let r := min u₁ u₂
  have htr : t < r := lt_min hu₁ hu₂
  have h₁r : p r ∈ segment ℝ (p t) (p u₁) := by
    rw [← h₁]
    exact ⟨r, ⟨htr.le, min_le_left _ _⟩, rfl⟩
  have h₂r : p r ∈ segment ℝ (p t) (p u₂) := by
    rw [← h₂]
    exact ⟨r, ⟨htr.le, min_le_right _ _⟩, rfl⟩
  have hrne : p r - p t ≠ 0 := sub_ne_zero.mpr (hpi.ne htr.ne')
  have hR₁ : SameRay ℝ (p r - p t) (p u₁ - p t) :=
    (mem_segment_iff_wbtw.mp h₁r).sameRay_vsub_left
  have hR₂ : SameRay ℝ (p r - p t) (p u₂ - p t) :=
    (mem_segment_iff_wbtw.mp h₂r).sameRay_vsub_left
  exact hR₁.symm.trans hR₂ (fun h => (hrne h).elim)

/-- Nonzero directions on the same ray have exactly the same principal argument. -/
theorem directionAngle_eq_of_sameRay {a b : Point}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : SameRay ℝ a b) :
    planeDirectionAngle a = planeDirectionAngle b := by
  have h' := h.map Complex.equivRealProdCLM.symm.toLinearEquiv.toLinearMap
  have ha' : Complex.equivRealProdCLM.symm a ≠ 0 := by
    simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using ha
  have hb' : Complex.equivRealProdCLM.symm b ≠ 0 := by
    simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using hb
  exact (Complex.sameRay_iff.mp h').resolve_left ha' |>.resolve_left hb'

theorem backward_subarc_directionAngle_eq
    {T : Type*} [LinearOrder T] (p : T → Point) (hpi : Function.Injective p)
    {s₁ s₂ t : T} (hs₁ : s₁ < t) (hs₂ : s₂ < t)
    (h₁ : p '' Icc s₁ t = segment ℝ (p s₁) (p t))
    (h₂ : p '' Icc s₂ t = segment ℝ (p s₂) (p t)) :
    planeDirectionAngle (p s₁ - p t) = planeDirectionAngle (p s₂ - p t) :=
  directionAngle_eq_of_sameRay (sub_ne_zero.mpr (hpi.ne hs₁.ne))
    (sub_ne_zero.mpr (hpi.ne hs₂.ne)) (backward_subarc_sameRay p hpi hs₁ hs₂ h₁ h₂)

theorem forward_subarc_directionAngle_eq
    {T : Type*} [LinearOrder T] (p : T → Point) (hpi : Function.Injective p)
    {t u₁ u₂ : T} (hu₁ : t < u₁) (hu₂ : t < u₂)
    (h₁ : p '' Icc t u₁ = segment ℝ (p t) (p u₁))
    (h₂ : p '' Icc t u₂ = segment ℝ (p t) (p u₂)) :
    planeDirectionAngle (p u₁ - p t) = planeDirectionAngle (p u₂ - p t) :=
  directionAngle_eq_of_sameRay (sub_ne_zero.mpr (hpi.ne hu₁.ne'))
    (sub_ne_zero.mpr (hpi.ne hu₂.ne')) (forward_subarc_sameRay p hpi hu₁ hu₂ h₁ h₂)

/-- The actual face of the right sector of an oriented arc is independent of
all choices in the ordered two-ray chart. Only the proved straight-subarc
identities and positivity of the radii are needed for this uniqueness. -/
theorem ordered_subarc_sector_face_independent
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    {T : Type*} [LinearOrder T] (p : T → Point) (hpi : Function.Injective p)
    {s₁ s₂ t u₁ u₂ : T}
    (hs₁ : s₁ < t) (hs₂ : s₂ < t) (hu₁ : t < u₁) (hu₂ : t < u₂)
    (hb₁ : p '' Icc s₁ t = segment ℝ (p s₁) (p t))
    (hb₂ : p '' Icc s₂ t = segment ℝ (p s₂) (p t))
    (hf₁ : p '' Icc t u₁ = segment ℝ (p t) (p u₁))
    (hf₂ : p '' Icc t u₂ = segment ℝ (p t) (p u₂))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    {F₁ F₂ : Face D}
    (hF₁ : OnePoint.some '' angularSector (p t) r₁
      (planeDirectionAngle (p s₁ - p t))
      (sectorEndAngle (planeDirectionAngle (p s₁ - p t))
        (planeDirectionAngle (p u₁ - p t))) ⊆ faceRegion D F₁)
    (hF₂ : OnePoint.some '' angularSector (p t) r₂
      (planeDirectionAngle (p s₂ - p t))
      (sectorEndAngle (planeDirectionAngle (p s₂ - p t))
        (planeDirectionAngle (p u₂ - p t))) ⊆ faceRegion D F₂) : F₁ = F₂ := by
  have hb := backward_subarc_directionAngle_eq p hpi hs₁ hs₂ hb₁ hb₂
  have hf := forward_subarc_directionAngle_eq p hpi hu₁ hu₂ hf₁ hf₂
  rw [← hb, ← hf] at hF₂
  apply angularSector_face_independent_radius D (p t) hr₁ hr₂ _ hF₁ hF₂
  dsimp [sectorEndAngle]
  split_ifs with h
  · exact h
  · have hlow : -Real.pi < planeDirectionAngle (p s₁ - p t) := Complex.neg_pi_lt_arg _
    have hhigh : planeDirectionAngle (p u₁ - p t) ≤ Real.pi := Complex.arg_le_pi _
    have hlow' : -Real.pi < planeDirectionAngle (p u₁ - p t) := Complex.neg_pi_lt_arg _
    have hhigh' : planeDirectionAngle (p s₁ - p t) ≤ Real.pi := Complex.arg_le_pi _
    linarith

end PolygonalGeometry


namespace PolygonalGeometry
open Set

/-- Every ordered subinterval of a straight injective arc is precisely its
endpoint segment, without assuming constant speed. -/
theorem straight_subarc_refine
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    {a b s t : unitInterval} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hbig : p '' Icc a b = segment ℝ (p a) (p b)) :
    p '' Icc s t = segment ℝ (p s) (p t) := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  apply subarc_image_eq_segment p hp hpi s t hst
  have hsm : p s ∈ segment ℝ (p a) (p b) := by
    rw [← hbig]
    exact ⟨s, ⟨has, hst.le.trans htb⟩, rfl⟩
  have htm : p t ∈ segment ℝ (p a) (p b) := by
    rw [← hbig]
    exact ⟨t, ⟨has.trans hst.le, htb⟩, rfl⟩
  exact ((convex_segment _ _).segment_subset hsm htm).trans (by
    rw [← hbig]
    exact image_subset_range p _)

/-- At an interior parameter of a straight subarc, every ordered chart has the
same backward and forward directions as that oriented straight segment. -/
theorem ordered_chart_inside_straight_subarc_sameRay
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    {a b s t u : unitInterval} (hat : a < t) (htb : t < b)
    (hst : s < t) (htu : t < u)
    (hbig : p '' Icc a b = segment ℝ (p a) (p b))
    (hback : p '' Icc s t = segment ℝ (p s) (p t))
    (hfront : p '' Icc t u = segment ℝ (p t) (p u)) :
    SameRay ℝ (p s - p t) (p a - p b) ∧
    SameRay ℝ (p u - p t) (p b - p a) := by
  have hat' : p '' Icc a t = segment ℝ (p a) (p t) :=
    straight_subarc_refine p hp hpi le_rfl hat.le htb.le hbig
  have htb' : p '' Icc t b = segment ℝ (p t) (p b) :=
    straight_subarc_refine p hp hpi hat.le htb.le le_rfl hbig
  have htm : p t ∈ segment ℝ (p a) (p b) := by
    rw [← hbig]
    exact ⟨t, ⟨hat.le, htb.le⟩, rfl⟩
  have htm' : p t ∈ segment ℝ (p b) (p a) := by rwa [segment_symm]
  have hb := backward_subarc_sameRay p hpi hst hat hback hat'
  have hf := forward_subarc_sameRay p hpi htu htb hfront htb'
  have hb' : SameRay ℝ (p a - p t) (p a - p b) :=
    (mem_segment_iff_wbtw.mp htm').sameRay_vsub_right.symm
  have hf' : SameRay ℝ (p b - p t) (p b - p a) :=
    (mem_segment_iff_wbtw.mp htm).sameRay_vsub_right.symm
  exact ⟨hb.trans hb' (fun h => (sub_ne_zero.mpr (hpi.ne hat.ne) h).elim),
    hf.trans hf' (fun h => (sub_ne_zero.mpr (hpi.ne htb.ne') h).elim)⟩

/-- The argument version of ordered_chart_inside_straight_subarc_sameRay. -/
theorem ordered_chart_inside_straight_subarc_directionAngle
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    {a b s t u : unitInterval} (hat : a < t) (htb : t < b)
    (hst : s < t) (htu : t < u)
    (hbig : p '' Icc a b = segment ℝ (p a) (p b))
    (hback : p '' Icc s t = segment ℝ (p s) (p t))
    (hfront : p '' Icc t u = segment ℝ (p t) (p u)) :
    planeDirectionAngle (p s - p t) = planeDirectionAngle (p a - p b) ∧
    planeDirectionAngle (p u - p t) = planeDirectionAngle (p b - p a) := by
  have h := ordered_chart_inside_straight_subarc_sameRay p hp hpi hat htb hst htu
    hbig hback hfront
  exact ⟨directionAngle_eq_of_sameRay (sub_ne_zero.mpr (hpi.ne hst.ne))
      (sub_ne_zero.mpr (hpi.ne (hat.trans htb).ne)) h.1,
    directionAngle_eq_of_sameRay (sub_ne_zero.mpr (hpi.ne htu.ne'))
      (sub_ne_zero.mpr (hpi.ne (hat.trans htb).ne')) h.2⟩

end PolygonalGeometry

lemma finite_star_arm_line_neighborhood {ι : Type*} [Finite ι]
    (S : Set Point) (c : Point) (q : ι → Point) (R : ℝ)
    (hmodel : S ∩ Metric.ball c R =
      ({c} ∪ ⋃ j, segment ℝ c (q j)) ∩ Metric.ball c R)
    (hsep : ∀ i j, i ≠ j → segment ℝ c (q i) ∩ segment ℝ c (q j) ⊆ {c})
    (i : ι) (x : Point) (hxseg : x ∈ segment ℝ c (q i))
    (hxc : x ≠ c) (hxq : x ≠ q i) (hxR : x ∈ Metric.ball c R) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball x r,
      y ∈ S ↔ planeDet c (q i) y = 0 := by
  classical
  have hci : c ≠ q i := by
    intro h
    exact hxc (by simpa only [← h,segment_same,mem_singleton_iff] using hxseg)
  let K : Set Point := {c} ∪ ⋃ j : {j : ι // j ≠ i}, segment ℝ c (q j.val)
  have hsegclosed (j : ι) : IsClosed (segment ℝ c (q j)) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  have hK : IsClosed K := isClosed_singleton.union
    (isClosed_iUnion_of_finite fun j => hsegclosed j.val)
  have hxK : x ∉ K := by
    rintro (hx | hx)
    · exact hxc hx
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact hxc (hsep i j.val j.property.symm ⟨hxseg,hj⟩)
  obtain ⟨U,hU,hxU,hline⟩ := SegmentRegularity.segment_has_line_neighborhood c (q i) x hxseg hxc hxq
  have hN : (Metric.ball c R ∩ U ∩ Kᶜ) ∈ nhds x :=
    Filter.inter_mem (Filter.inter_mem (Metric.isOpen_ball.mem_nhds hxR) (hU.mem_nhds hxU))
      (hK.isOpen_compl.mem_nhds hxK)
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨r,hr,?_⟩
  intro y hyr
  have hyR := (hrsub hyr).1.1
  constructor
  · intro hyS
    have hyStar : y ∈ {c} ∪ ⋃ j, segment ℝ c (q j) :=
      (hmodel ▸ (show y ∈ S ∩ Metric.ball c R from ⟨hyS,hyR⟩)).1
    have hyseg : y ∈ segment ℝ c (q i) := by
      rcases hyStar with hyc | hyStar
      · exact False.elim ((hrsub hyr).2 (Or.inl hyc))
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hyStar
        by_cases hji : j = i
        · exact hji ▸ hj
        · exact False.elim ((hrsub hyr).2 (Or.inr (mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩)))
    exact (mem_plane_line_iff hci y).mp (SegmentRegularity.segment_subset_line c (q i) hyseg)
  · intro hyline
    have hyseg : y ∈ segment ℝ c (q i) :=
      hline y (hrsub hyr).1.2 ((mem_plane_line_iff hci y).mpr hyline)
    exact ((hmodel.symm) ▸ (show y ∈
      ({c} ∪ ⋃ j, segment ℝ c (q j)) ∩ Metric.ball c R from
      ⟨Or.inr (mem_iUnion.mpr ⟨i,hyseg⟩),hyR⟩)).1


open Set

/-- Every noncentral interior point of a branch of a two-ray drawing chart has
an ambient straight-line chart of the whole drawing. -/
theorem two_ray_branch_interior_locally_line
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (c a b y : Point) {R : ℝ} (hca : c ≠ a)
    (hmodel : planeImage D ∩ Metric.ball c R =
      (segment ℝ c a ∪ segment ℝ c b) ∩ Metric.ball c R)
    (hsep : segment ℝ c a ∩ segment ℝ c b = {c})
    (hy : y ∈ segment ℝ c a) (hyc : y ≠ c) (hya : y ≠ a)
    (hyR : y ∈ Metric.ball c R) :
    ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ Metric.ball y r, z ∈ planeImage D ↔ planeDet c a z = 0 := by
  obtain ⟨U,hUo,hyU,hU⟩ :=
    SegmentRegularity.segment_has_line_neighborhood c a y hy hyc hya
  have hbclosed : IsClosed (segment ℝ c b) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  have hyb : y ∉ segment ℝ c b := by
    intro hyb
    have : y ∈ ({c} : Set Point) := hsep ▸ (show y ∈ segment ℝ c a ∩ segment ℝ c b from ⟨hy,hyb⟩)
    exact hyc (mem_singleton_iff.mp this)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp
    ((hUo.inter Metric.isOpen_ball).inter hbclosed.isOpen_compl) y ⟨⟨hyU,hyR⟩,hyb⟩
  refine ⟨r,hr,?_⟩
  intro z hz
  have hzU := (hball hz).1.1
  have hzR := (hball hz).1.2
  have hzb := (hball hz).2
  constructor
  · intro hzgraph
    have hzrays : z ∈ segment ℝ c a ∪ segment ℝ c b :=
      (hmodel ▸ (show z ∈ planeImage D ∩ Metric.ball c R from ⟨hzgraph,hzR⟩)).1
    have hza : z ∈ segment ℝ c a := hzrays.resolve_right hzb
    exact (mem_plane_line_iff hca z).mp (SegmentRegularity.segment_subset_line c a hza)
  · intro hzline
    have hza : z ∈ segment ℝ c a := hU z hzU ((mem_plane_line_iff hca z).mpr hzline)
    exact (hmodel.symm ▸ (show z ∈ (segment ℝ c a ∪ segment ℝ c b) ∩ Metric.ball c R from
      ⟨Or.inl hza,hzR⟩)).1


open Set
open FiniteCombinatorics.Graph.Plane.FaceSideAux (sectorEndAngle)

/-- The actual face selected by an ordered straight chart of an oriented arc.
The sector runs counterclockwise from the backward ray to the forward ray. -/
def ArcRightSectorFace {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) {T : Type*} [LinearOrder T]
    (p : T → Point) (t : T) (F : Face D) : Prop :=
  ∃ (s u : T) (r : ℝ), s < t ∧ t < u ∧ 0 < r ∧
    p '' Icc s t = segment ℝ (p s) (p t) ∧
    p '' Icc t u = segment ℝ (p t) (p u) ∧
    OnePoint.some '' angularSector (p t) r (planeDirectionAngle (p s-p t))
      (sectorEndAngle (planeDirectionAngle (p s-p t)) (planeDirectionAngle (p u-p t))) ⊆
        faceRegion D F

theorem ArcRightSectorFace.unique
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    {T : Type*} [LinearOrder T] (p : T → Point) (hpi : Function.Injective p)
    {t : T} {F H : Face D} (hF : ArcRightSectorFace D p t F)
    (hH : ArcRightSectorFace D p t H) : F = H := by
  obtain ⟨s,u,r,hs,hu,hr,hb,hf,hF⟩ := hF
  obtain ⟨s',u',r',hs',hu',hr',hb',hf',hH⟩ := hH
  exact PolygonalGeometry.ordered_subarc_sector_face_independent D p hpi
    hs hs' hu hu' hb hb' hf hf' hr hr' hF hH

theorem existsUnique_arcRightSectorFace
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (e : G.edgeSet) (p : unitInterval → Point) (hp : Continuous p)
    (hpi : Function.Injective p) (hpr : range p = D.edge e)
    (hpoly : IsPolygonal (range p))
    (t : unitInterval) (ht0 : 0 < t) (ht1 : t < 1)
    (hn : p t ∉ range D.point) :
    ∃! F : Face D, ArcRightSectorFace D p t F := by
  obtain ⟨s,u,r,hs,hu,hr,hb,hf,_,_,F,hF,_⟩ :=
    oriented_edge_interior_sector_face D e p hp hpi hpr hpoly t ht0 ht1 hn
  have hFR : ArcRightSectorFace D p t F := ⟨s,u,r,hs,hu,hr,hb,hf,hF⟩
  exact ⟨F,hFR,fun H hH => ArcRightSectorFace.unique D p hpi hH hFR⟩

lemma edge_path_interior_nonvertex
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (v w : V) (h : G.Adj v w) (p : _root_.Path (D.point v) (D.point w))
    (hpi : Function.Injective p) (hpr : range p = D.edge ⟨s(v,w),h⟩)
    (t : unitInterval) (ht0 : 0 < t) (ht1 : t < 1) :
    p t ∉ range D.point := by
  rintro ⟨z,hz⟩
  have hze : z ∈ s(v,w) := (D.vertex_edge ⟨s(v,w),h⟩ z).mp
    (hz.symm ▸ (hpr ▸ mem_range_self t))
  rcases Sym2.mem_iff.mp hze with rfl | rfl
  · have ht : t = 0 := hpi (hz.symm.trans p.source.symm)
    exact ht0.ne' ht
  · have ht : t = 1 := hpi (hz.symm.trans p.target.symm)
    exact ht1.ne ht

/-- Canonical actual right-side face at each interior parameter of an original
oriented edge. Its construction uses image polygonality only. -/
def edgeInteriorRightFace
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (v w : V) (h : G.Adj v w) (p : _root_.Path (D.point v) (D.point w))
    (hpi : Function.Injective p) (hpr : range p = D.edge ⟨s(v,w),h⟩)
    (t : Ioo (0 : unitInterval) 1) : Face D :=
  (existsUnique_arcRightSectorFace D ⟨s(v,w),h⟩ p p.continuous hpi hpr
    (hpr.symm ▸ (D.edge_arc v w h).1) t.val t.property.1 t.property.2
    (edge_path_interior_nonvertex D v w h p hpi hpr t.val t.property.1 t.property.2)).choose

theorem edgeInteriorRightFace_geometry
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (v w : V) (h : G.Adj v w) (p : _root_.Path (D.point v) (D.point w))
    (hpi : Function.Injective p) (hpr : range p = D.edge ⟨s(v,w),h⟩)
    (t : Ioo (0 : unitInterval) 1) :
    ArcRightSectorFace D p t.val (edgeInteriorRightFace D v w h p hpi hpr t) :=
  (existsUnique_arcRightSectorFace D ⟨s(v,w),h⟩ p p.continuous hpi hpr
    (hpr.symm ▸ (D.edge_arc v w h).1) t.val t.property.1 t.property.2
    (edge_path_interior_nonvertex D v w h p hpi hpr t.val t.property.1 t.property.2)).choose_spec.1


open Set
open FiniteCombinatorics.Graph.Plane.FaceSideAux (sectorEndAngle)

lemma angleDirection_sectorEndAngle (α β : ℝ) :
    angleDirection (sectorEndAngle α β) = angleDirection β := by
  unfold sectorEndAngle
  split_ifs
  · rfl
  · exact angleDirection_add_two_pi _

lemma planeDirectionAngle_eq_of_sameRay {x y : Point} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : SameRay ℝ x y) : planeDirectionAngle x = planeDirectionAngle y := by
  have h' := h.map Complex.equivRealProdCLM.symm.toLinearEquiv.toLinearMap
  have hx' : Complex.equivRealProdCLM.symm x ≠ 0 := by simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using hx
  have hy' : Complex.equivRealProdCLM.symm y ≠ 0 := by simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using hy
  exact (Complex.sameRay_iff.mp h').resolve_left hx' |>.resolve_left hy'

lemma two_ray_sector_cover (c a b : Point) (hrays : ¬ SameRay ℝ (a-c) (b-c))
    {R : ℝ} {x : Point} (hx : ‖Complex.equivRealProdCLM.symm (x-c)‖ < R)
    (hxa : ¬ SameRay ℝ (x-c) (a-c)) (hxb : ¬ SameRay ℝ (x-c) (b-c)) :
    x ∈ angularSector c R (planeDirectionAngle (a-c))
        (sectorEndAngle (planeDirectionAngle (a-c)) (planeDirectionAngle (b-c))) ∪
      angularSector c R (planeDirectionAngle (b-c))
        (sectorEndAngle (planeDirectionAngle (b-c)) (planeDirectionAngle (a-c))) := by
  let q : Bool → Point := fun i => if i then b else a
  let θ : Bool → ℝ := fun i => planeDirectionAngle (q i-c)
  have hne : planeDirectionAngle (a-c) ≠ planeDirectionAngle (b-c) :=
    fun h => hrays (planeDirectionAngle_eq_implies_sameRay h)
  have hθ : Function.Injective θ := by
    intro i j hij
    cases i <;> cases j <;> simp_all [θ,q]
  let L := angleList θ hθ
  have hpos : 0 < L.length := List.length_pos_of_mem (mem_angleList θ hθ false)
  let t := planeDirectionAngle (x-c)
  have ht : t ∈ Ioc (-Real.pi) Real.pi := ⟨Complex.neg_pi_lt_arg _,Complex.arg_le_pi _⟩
  have hneq (i) : θ i ≠ t := by
    intro he
    have hsame := planeDirectionAngle_eq_implies_sameRay he.symm
    cases i
    · exact hxa hsame
    · exact hxb hsame
  obtain ⟨j,hj,t',hjt,ht'end,heq⟩ := sorted_cyclic_angle_cover θ L
    (angleList_pairwise _ _) (mem_angleList _ _) hpos
    (fun i => ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩) ht hneq
  have hnotfixed (i : Bool) : angleTurn θ hθ i ≠ i :=
    (angleTurn_isCycleOn θ hθ).apply_ne ⟨false,mem_univ _,true,mem_univ _,by decide⟩ (mem_univ _)
  have hturn (i : Bool) : angleTurn θ hθ i = !i := by
    cases i <;> cases h : angleTurn θ hθ _ <;> simp_all
  have hnext : L[(j+1)%L.length]'(Nat.mod_lt _ hpos) = !(L[j]'hj) := by
    exact (angleTurn_apply_getElem θ hθ j hj).symm.trans (hturn _)
  have hd : x-c ≠ 0 := by
    intro he
    exact hxa (he ▸ SameRay.zero_left _)
  have hcomplex : Complex.equivRealProdCLM.symm (x-c) ≠ 0 := by
    simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using hd
  have hxsector : x ∈ angularSector c R (θ (L[j]'hj))
      (sectorEndAngle (θ (L[j]'hj)) (θ (!(L[j]'hj)))) := by
    refine ⟨(‖Complex.equivRealProdCLM.symm (x-c)‖,t'),
      ⟨⟨norm_pos_iff.mpr hcomplex,hx⟩,⟨hjt,?_⟩⟩,?_⟩
    · simpa only [hnext] using ht'end
    · change c+‖Complex.equivRealProdCLM.symm (x-c)‖ • angleDirection t' = x
      rw [heq,point_polar_reconstruction]
      exact add_sub_cancel _ _
  cases h : (L[j]'hj)
  · exact Or.inl (by simpa only [h,θ,q,Bool.false_eq_true,ite_false,Bool.not_false,ite_true] using hxsector)
  · exact Or.inr (by simpa only [h,θ,q,ite_true,Bool.not_true,Bool.false_eq_true,ite_false] using hxsector)

/-- Either side of a genuine two-ray star approaches both of its bounding
rays throughout the radial range of the sector. -/
lemma two_ray_sector_boundary_mem_closure (c a b : Point) (ha : a ≠ c) (hb : b ≠ c)
    {R : ℝ} {y : Point} (hy : y ≠ c)
    (hyR : ‖Complex.equivRealProdCLM.symm (y-c)‖ < R)
    (hyray : SameRay ℝ (y-c) (a-c) ∨ SameRay ℝ (y-c) (b-c)) :
    y ∈ closure (angularSector c R (planeDirectionAngle (a-c))
      (sectorEndAngle (planeDirectionAngle (a-c)) (planeDirectionAngle (b-c)))) := by
  have hcomplex : Complex.equivRealProdCLM.symm (y-c) ≠ 0 := by
    simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using sub_ne_zero.mpr hy
  have hρ : ‖Complex.equivRealProdCLM.symm (y-c)‖ ∈ Ioo (0:ℝ) R :=
    ⟨norm_pos_iff.mpr hcomplex,hyR⟩
  have hlength := directionAngle_lt_sectorEndAngle (a-c) (b-c)
  rcases hyray with hya | hyb
  · have heq := planeDirectionAngle_eq_of_sameRay (sub_ne_zero.mpr hy) (sub_ne_zero.mpr ha) hya
    have hy' : c + ‖Complex.equivRealProdCLM.symm (y-c)‖ • angleDirection (planeDirectionAngle (a-c)) = y := by
      rw [← heq,point_polar_reconstruction]
      exact add_sub_cancel _ _
    exact hy' ▸ angularSector_left_boundary_mem_closure c hρ hlength
  · have heq := planeDirectionAngle_eq_of_sameRay (sub_ne_zero.mpr hy) (sub_ne_zero.mpr hb) hyb
    have hy' : c + ‖Complex.equivRealProdCLM.symm (y-c)‖ •
        angleDirection (sectorEndAngle (planeDirectionAngle (a-c)) (planeDirectionAngle (b-c))) = y := by
      rw [angleDirection_sectorEndAngle,← heq,point_polar_reconstruction]
      exact add_sub_cancel _ _
    exact hy' ▸ angularSector_right_boundary_mem_closure c hρ hlength

/-- A face approaching the center of an ambient two-ray chart approaches all
sufficiently short portions of both rays. No choice of an oriented side is used. -/
theorem two_ray_frontier_propagation
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (c a b : Point) (ha : a ≠ c) (hb : b ≠ c)
    (hsep : segment ℝ c a ∩ segment ℝ c b = {c})
    {r : ℝ} (hr : 0 < r)
    (hmodel : planeImage D ∩ Metric.ball c r =
      (segment ℝ c a ∪ segment ℝ c b) ∩ Metric.ball c r)
    (F : Face D) (hcF : OnePoint.some c ∈ frontier (faceRegion D F)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ planeImage D ∩ Metric.ball c ε,
      OnePoint.some y ∈ frontier (faceRegion D F) := by
  let A := planeDirectionAngle (a-c)
  let B := planeDirectionAngle (b-c)
  let sector : Bool → Set Point := fun i => if i then
    angularSector c r B (sectorEndAngle B A) else
    angularSector c r A (sectorEndAngle A B)
  have hface (i : Bool) : ∃! H : Face D, OnePoint.some '' sector i ⊆ faceRegion D H := by
    cases i
    · exact existsUnique_two_ray_sector_face D c a b ha hb hr hmodel
    · apply existsUnique_two_ray_sector_face D c b a hb ha hr
      simpa only [union_comm] using hmodel
  let face : Bool → Face D := fun i => (hface i).choose
  have hCF (i : Bool) : OnePoint.some '' sector i ⊆ faceRegion D (face i) :=
    (hface i).choose_spec.1
  have hconn (i : Bool) : IsPreconnected (OnePoint.some '' sector i) := by
    cases i <;> exact (angularSector_isPreconnected _ _ _ _).image _
      OnePoint.continuous_coe.continuousOn
  have hCs (i : Bool) : OnePoint.some '' sector i ⊆ (sphereImage D)ᶜ :=
    fun _ hx => face_region_subset D _ (hCF i hx)
  have har : 0 < ‖a-c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ha)
  have hbr : 0 < ‖b-c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  let ε := min (r/2) (min ‖a-c‖ ‖b-c‖)
  have hε : 0 < ε := lt_min (by positivity) (lt_min har hbr)
  have hεr : ε ≤ r := (min_le_left _ _).trans (by linarith)
  have hnorm (y : Point) (hy : y ∈ Metric.ball c ε) :
      ‖Complex.equivRealProdCLM.symm (y-c)‖ < r := by
    apply (complex_norm_point_le_twice _).trans_lt
    have hy' : ‖y-c‖ < ε := hy
    have he := min_le_left (r/2) (min ‖a-c‖ ‖b-c‖)
    change ε ≤ r/2 at he
    linarith
  have hrays : ¬ SameRay ℝ (a-c) (b-c) :=
    PolygonalGeometry.not_sameRay_of_segment_inter_subset ha hb (by rw [hsep])
  have hcover : (OnePoint.some '' Metric.ball c ε) ∩ (sphereImage D)ᶜ ⊆
      ⋃ i, OnePoint.some '' sector i := by
    rintro _ ⟨⟨y,hy,rfl⟩,hyg⟩
    have hny (q : Point) (hq : q ≠ c) (hbound : ε ≤ ‖q-c‖)
        (hside : segment ℝ c q ⊆ segment ℝ c a ∪ segment ℝ c b) :
        ¬ SameRay ℝ (y-c) (q-c) := by
      intro hsame
      have hym : y ∈ segment ℝ c a ∪ segment ℝ c b :=
        hside (mem_segment_of_sameRay_norm_le hq hsame ((show ‖y-c‖ < ε from hy).le.trans hbound))
      have hyball : y ∈ Metric.ball c r := Metric.ball_subset_ball hεr hy
      have hyg' : y ∈ planeImage D := (hmodel ▸
        (show y ∈ (segment ℝ c a ∪ segment ℝ c b) ∩ Metric.ball c r from ⟨hym,hyball⟩)).1
      exact hyg ((sphere_image_membership D y).mpr hyg')
    have hna : ¬ SameRay ℝ (y-c) (a-c) := hny a ha
      ((min_le_right _ _).trans (min_le_left _ _)) subset_union_left
    have hnb : ¬ SameRay ℝ (y-c) (b-c) := hny b hb
      ((min_le_right _ _).trans (min_le_right _ _)) subset_union_right
    rcases two_ray_sector_cover c a b hrays (hnorm y hy) hna hnb with h | h
    · exact mem_iUnion.mpr ⟨false,y,h,rfl⟩
    · exact mem_iUnion.mpr ⟨true,y,h,rfl⟩
  obtain ⟨i,⟨z,hz⟩,hiF⟩ := face_contains_local_patch D F
    (frontier_subset_closure hcF)
    (OnePoint.isOpenEmbedding_coe.isOpenMap.image_mem_nhds (Metric.ball_mem_nhds c hε))
    (fun i => OnePoint.some '' sector i) hconn hCs hcover
  have hFeq : F = face i := face_eq_of_mem_regions D (hiF hz) (hCF i hz)
  refine ⟨ε,hε,?_⟩
  intro y hy
  by_cases hyc : y = c
  · simpa only [hyc] using hcF
  have hyball : y ∈ Metric.ball c r := Metric.ball_subset_ball hεr hy.2
  have hym : y ∈ segment ℝ c a ∪ segment ℝ c b :=
    (hmodel ▸ (show y ∈ planeImage D ∩ Metric.ball c r from ⟨hy.1,hyball⟩)).1
  have hyrays : SameRay ℝ (y-c) (a-c) ∨ SameRay ℝ (y-c) (b-c) := by
    rcases hym with h | h
    · exact Or.inl (mem_segment_iff_wbtw.mp h).sameRay_vsub_left
    · exact Or.inr (mem_segment_iff_wbtw.mp h).sameRay_vsub_left
  have hycl : y ∈ closure (sector i) := by
    cases i
    · exact two_ray_sector_boundary_mem_closure c a b ha hb hyc (hnorm y hy.2) hyrays
    · exact two_ray_sector_boundary_mem_closure c b a hb ha hyc (hnorm y hy.2) hyrays.symm
  refine ⟨?_,?_⟩
  · rw [hFeq]
    exact closure_mono (hCF i) (mem_closure_image OnePoint.continuous_coe.continuousAt hycl)
  · intro hi
    exact face_region_subset D F (interior_subset hi) ((sphere_image_membership D y).mpr hy.1)


open Set

/-- A closed subset of the unit interval that is locally open at all of its
interior points and contains one interior point is the entire interval. -/
lemma closed_unitInterval_eq_univ_of_interior_open {S : Set unitInterval}
    (hS : IsClosed S)
    (hopen : ∀ t ∈ S, 0 < t → t < 1 → S ∈ nhds t)
    (hne : ∃ t ∈ S, 0 < t ∧ t < 1) : S = univ := by
  let J : Set unitInterval := Ioo 0 1
  let T : Set J := (Subtype.val : J → unitInterval) ⁻¹' S
  letI : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hTclosed : IsClosed T := hS.preimage continuous_subtype_val
  have hTopen : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds
      (hopen t.val ht t.property.1 t.property.2)
  have hTne : T.Nonempty := by
    obtain ⟨t,ht,ht0,ht1⟩ := hne
    exact ⟨⟨t,ht0,ht1⟩,ht⟩
  have hTall : T = univ := (show IsClopen T from ⟨hTclosed,hTopen⟩).eq_univ hTne
  have hJsub : J ⊆ S := by
    intro t ht
    have hmem : (⟨t,ht⟩ : J) ∈ T := by rw [hTall]; trivial
    exact hmem
  have hclosure : closure J = univ := by
    dsimp only [J]
    rw [closure_Ioo (show (0 : unitInterval) ≠ 1 by norm_num)]
    ext t
    simp only [mem_Icc, mem_univ, iff_true]
    exact ⟨t.property.1,t.property.2⟩
  apply subset_antisymm (subset_univ S)
  rw [← hclosure]
  exact hS.closure_subset_iff.mpr hJsub

/-- Frontier incidence along an arc propagates from one interior parameter to
both endpoints whenever it is locally persistent at interior parameters. -/
lemma frontier_arc_all_of_locally_frontier {V : Type u} [Finite V]
    {G : SimpleGraph V} (D : PlaneEmbedding G) (F : Face D)
    (p : unitInterval → Point) (hp : Continuous p)
    (hlocal : ∀ t : unitInterval, 0 < t → t < 1 →
      OnePoint.some (p t) ∈ frontier (faceRegion D F) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ Metric.ball t δ,
        OnePoint.some (p u) ∈ frontier (faceRegion D F))
    (hne : ∃ t : unitInterval, 0 < t ∧ t < 1 ∧
      OnePoint.some (p t) ∈ frontier (faceRegion D F)) :
    ∀ t : unitInterval, OnePoint.some (p t) ∈ frontier (faceRegion D F) := by
  let S := (fun t => OnePoint.some (p t)) ⁻¹' frontier (faceRegion D F)
  have hSclosed : IsClosed S := isClosed_frontier.preimage (OnePoint.continuous_coe.comp hp)
  have hSopen : ∀ t ∈ S, 0 < t → t < 1 → S ∈ nhds t := by
    intro t ht ht0 ht1
    obtain ⟨δ,hδ,hδS⟩ := hlocal t ht0 ht1 ht
    exact Metric.mem_nhds_iff.mpr ⟨δ,hδ,hδS⟩
  have hSne : ∃ t ∈ S, 0 < t ∧ t < 1 := by
    obtain ⟨t,ht0,ht1,htF⟩ := hne
    exact ⟨t,htF,ht0,ht1⟩
  have hall := closed_unitInterval_eq_univ_of_interior_open hSclosed hSopen hSne
  intro t
  have ht : t ∈ S := by rw [hall]; trivial
  exact ht


namespace PolygonalGeometry
open Set

/-- A straight segment issuing from the first endpoint and contained in the arc
is exactly an initial subarc, even when its parametrization has arbitrary speed. -/
theorem exists_initial_straight_subarc_of_segment_subset
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    {q : Point} (hq : q ≠ p 0) (hseg : segment ℝ (p 0) q ⊆ range p) :
    ∃ u : unitInterval, 0 < u ∧ p u = q ∧
      p '' Icc 0 u = segment ℝ (p 0) q := by
  obtain ⟨u,huq⟩ := hseg (right_mem_segment ℝ (p 0) q)
  have hu : 0 < u := by
    apply lt_of_le_of_ne (show (0 : unitInterval) ≤ u from u.property.1)
    intro h
    exact hq (huq.symm.trans (congrArg p h.symm))
  refine ⟨u,hu,huq,?_⟩
  rw [← huq]
  apply subarc_image_eq_segment p hp hpi 0 u hu
  simpa only [huq] using hseg

/-- A straight segment issuing from the final endpoint is a final subarc. -/
theorem exists_final_straight_subarc_of_segment_subset
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    {q : Point} (hq : q ≠ p 1) (hseg : segment ℝ (p 1) q ⊆ range p) :
    ∃ s : unitInterval, s < 1 ∧ p s = q ∧
      p '' Icc s 1 = segment ℝ q (p 1) := by
  obtain ⟨s,hsq⟩ := hseg (right_mem_segment ℝ (p 1) q)
  have hs : s < 1 := by
    apply lt_of_le_of_ne (show s ≤ (1 : unitInterval) from s.property.2)
    intro h
    exact hq (hsq.symm.trans (congrArg p h))
  refine ⟨s,hs,hsq,?_⟩
  rw [← hsq]
  apply subarc_image_eq_segment p hp hpi s 1 hs
  rw [segment_symm]
  simpa only [hsq] using hseg

/-- Any nontrivial straight segment contained in an injective arc and issuing
from its first endpoint has the actual initial arc direction. -/
theorem initial_subarc_sameRay_of_segment_subset
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    {q : Point} (hq : q ≠ p 0) (hseg : segment ℝ (p 0) q ⊆ range p)
    {u : unitInterval} (hu : 0 < u)
    (hsub : p '' Icc 0 u = segment ℝ (p 0) (p u)) :
    SameRay ℝ (p u-p 0) (q-p 0) := by
  obtain ⟨t,htq⟩ := hseg (right_mem_segment ℝ (p 0) q)
  have ht : 0 < t := by
    apply lt_of_le_of_ne (show (0 : unitInterval) ≤ t from t.property.1)
    intro h
    exact hq (htq.symm.trans (congrArg p h.symm))
  have hsub' : p '' Icc 0 t = segment ℝ (p 0) (p t) := by
    apply subarc_image_eq_segment p hp hpi 0 t ht
    simpa only [htq] using hseg
  simpa only [htq] using forward_subarc_sameRay p hpi hu ht hsub hsub'

/-- The corresponding endpoint-independent ray at the final endpoint. -/
theorem final_subarc_sameRay_of_segment_subset
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    {q : Point} (hq : q ≠ p 1) (hseg : segment ℝ (p 1) q ⊆ range p)
    {s : unitInterval} (hs : s < 1)
    (hsub : p '' Icc s 1 = segment ℝ (p s) (p 1)) :
    SameRay ℝ (p s-p 1) (q-p 1) := by
  obtain ⟨t,htq⟩ := hseg (right_mem_segment ℝ (p 1) q)
  have ht : t < 1 := by
    apply lt_of_le_of_ne (show t ≤ (1 : unitInterval) from t.property.2)
    intro h
    exact hq (htq.symm.trans (congrArg p h))
  have hsub' : p '' Icc t 1 = segment ℝ (p t) (p 1) := by
    apply subarc_image_eq_segment p hp hpi t 1 ht
    rw [segment_symm]
    simpa only [htq] using hseg
  simpa only [htq] using backward_subarc_sameRay p hpi hs ht hsub hsub'

lemma initial_subarc_directionAngle_of_segment_subset
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    {q : Point} (hq : q ≠ p 0) (hseg : segment ℝ (p 0) q ⊆ range p)
    {u : unitInterval} (hu : 0 < u)
    (hsub : p '' Icc 0 u = segment ℝ (p 0) (p u)) :
    planeDirectionAngle (p u-p 0) = planeDirectionAngle (q-p 0) :=
  directionAngle_eq_of_sameRay (sub_ne_zero.mpr (hpi.ne hu.ne'))
    (sub_ne_zero.mpr hq) (initial_subarc_sameRay_of_segment_subset p hp hpi hq hseg hu hsub)

lemma final_subarc_directionAngle_of_segment_subset
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    {q : Point} (hq : q ≠ p 1) (hseg : segment ℝ (p 1) q ⊆ range p)
    {s : unitInterval} (hs : s < 1)
    (hsub : p '' Icc s 1 = segment ℝ (p s) (p 1)) :
    planeDirectionAngle (p s-p 1) = planeDirectionAngle (q-p 1) :=
  directionAngle_eq_of_sameRay (sub_ne_zero.mpr (hpi.ne hs.ne))
    (sub_ne_zero.mpr hq) (final_subarc_sameRay_of_segment_subset p hp hpi hq hseg hs hsub)

end PolygonalGeometry

open Set

/-- At every nonvertex edge point, the frontier of an incident face persists
locally along the whole drawing. -/
lemma frontier_persists_near_edge_point {V : Type u} [Finite V]
    {G : SimpleGraph V} (D : PlaneEmbedding G) (F : Face D)
    (e : G.edgeSet) (x : Point) (hxe : x ∈ D.edge e)
    (hxV : x ∉ range D.point) (hxF : OnePoint.some x ∈ frontier (faceRegion D F)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ planeImage D ∩ Metric.ball x ε,
      OnePoint.some y ∈ frontier (faceRegion D F) := by
  obtain ⟨a,b,r,ha,hb,hr,haseg,hbseg,hsep,hmodel⟩ :=
    plane_edge_interior_locally_two_segments D e x hxe hxV
  exact two_ray_frontier_propagation D x a b ha hb hsep hr hmodel F hxF

/-- Every face of a drawing with an edge reaches a vertex: local two-ray
frontier persistence propagates along a complete original edge arc. -/
lemma face_frontier_vertex {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (he : G.edgeSet.Nonempty) (F : Face D) :
    ∃ v : V, Nonempty (G.neighborSet v) ∧
      OnePoint.some (D.point v) ∈ frontier (faceRegion D F) := by
  obtain ⟨e,x,hxF,hxe,hxV⟩ := face_frontier_edge_point D he F
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective e.val
  have hadj : G.Adj a b := by simpa [← hab] using e.property
  let w : G.neighborSet a := ⟨b,hadj⟩
  have heq : e = incidentEdge a w := Subtype.ext hab.symm
  let p : unitInterval → Point := incidentPath D a w
  have hp : Continuous p := (incidentPath D a w).continuous
  have hpr : range p = D.edge e := by
    change range (incidentPath D a w) = D.edge e
    rw [incidentPath_range,heq]
  obtain ⟨t,htx⟩ := hpr ▸ hxe
  have ht0 : 0 < t := by
    apply lt_of_le_of_ne (show (0 : unitInterval) ≤ t from t.property.1)
    intro ht
    apply hxV
    refine ⟨a,?_⟩
    rw [← htx,← ht]
    exact (incidentPath D a w).source.symm
  have ht1 : t < 1 := by
    apply lt_of_le_of_ne (show t ≤ (1 : unitInterval) from t.property.2)
    intro ht
    apply hxV
    refine ⟨b,?_⟩
    rw [← htx,ht]
    exact (incidentPath D a w).target.symm
  have hlocal (s : unitInterval) (hs0 : 0 < s) (hs1 : s < 1)
      (hsF : OnePoint.some (p s) ∈ frontier (faceRegion D F)) :
      ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ Metric.ball s δ,
        OnePoint.some (p u) ∈ frontier (faceRegion D F) := by
    have hsV : p s ∉ range D.point := by
      rintro ⟨z,hz⟩
      have hsend := incidentPath_eq_vertex D a w s z hz.symm
      rcases hsend with hsend | hsend
      · exact hs0.ne' hsend
      · exact hs1.ne hsend
    have hse : p s ∈ D.edge e := hpr ▸ mem_range_self s
    obtain ⟨ε,hε,hεF⟩ := frontier_persists_near_edge_point D F e (p s) hse hsV hsF
    have hn : p ⁻¹' Metric.ball (p s) ε ∈ nhds s :=
      hp.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    obtain ⟨δ,hδ,hδp⟩ := Metric.mem_nhds_iff.mp hn
    refine ⟨δ,hδ,?_⟩
    intro u hu
    exact hεF (p u) ⟨Or.inr (mem_iUnion.mpr ⟨e,hpr ▸ mem_range_self u⟩),hδp hu⟩
  have hall := frontier_arc_all_of_locally_frontier D F p hp hlocal
    ⟨t,ht0,ht1,by simpa only [htx] using hxF⟩
  refine ⟨a,⟨w⟩,?_⟩
  simpa only [p,(incidentPath D a w).source] using hall 0

/-- The concrete angular-sector labeling reaches every actual face of any
finite polygonal drawing that has an edge. -/
theorem drawingSideLabel_surjective_of_edge {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (he : G.edgeSet.Nonempty) :
    Function.Surjective (drawingSideLabel D) := by
  intro F
  obtain ⟨v,hv,hvF⟩ := face_frontier_vertex D he F
  letI : Nonempty (G.neighborSet v) := hv
  obtain ⟨w,hw⟩ := face_eq_vertexSectorFace_of_vertex_frontier D v F hvF
  let d : G.Dart := ⟨(w.val,v),w.property.symm⟩
  refine ⟨d,?_⟩
  exact hw.symm

/-- Connected drawings with at least three vertices have a surjective concrete
directed-side label map. -/
theorem drawingSideLabel_surjective {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (hc : G.Connected) (hv : 3 ≤ Nat.card V) :
    Function.Surjective (drawingSideLabel D) := by
  letI : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a⟩ := hc.nonempty
  obtain ⟨b,hab⟩ := hc.preconnected.exists_adj_of_nontrivial a
  exact drawingSideLabel_surjective_of_edge D ⟨s(a,b),hab⟩


lemma sector_boundary_arm_local_side {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) {ι : Type*} [Finite ι]
    (c : Point) (q : ι → Point) {S R α β γ L : ℝ}
    (hS : 0 < S) (hR : 0 < R) (hαβ : α < β) (hL : 0 < L)
    (hmodel : planeImage D ∩ Metric.ball c S =
      ({c} ∪ ⋃ j, segment ℝ c (q j)) ∩ Metric.ball c S)
    (hsep : ∀ i j, i ≠ j → segment ℝ c (q i) ∩ segment ℝ c (q j) ⊆ {c})
    (i : ι) (hqi : q i = c + L • angleDirection γ)
    (positive : Bool) (hbound : (γ = α ∧ positive = true) ∨ (γ = β ∧ positive = false))
    (F : Face D) (hF : OnePoint.some '' angularSector c R α β ⊆ faceRegion D F) :
    ∃ (x : Point) (r : ℝ), x ∈ segment ℝ c (q i) ∧ x ≠ c ∧ x ≠ q i ∧ 0 < r ∧
      (∀ y ∈ Metric.ball x r, y ∈ planeImage D ↔ planeDet c (q i) y = 0) ∧
      OnePoint.some '' lineHalfBall c (q i) x r positive ⊆ faceRegion D F := by
  let ρ := min (min S R) L / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρL : ρ < L := by dsimp [ρ]; linarith [min_le_right (min S R) L]
  have hρR : ρ < R := by
    dsimp [ρ]
    linarith [(min_le_left (min S R) L).trans (min_le_right S R)]
  have hρS : ρ < S := by
    dsimp [ρ]
    linarith [(min_le_left (min S R) L).trans (min_le_left S R)]
  let x := c + ρ • angleDirection γ
  have hxseg : x ∈ segment ℝ c (q i) := by
    rw [segment_eq_image']
    refine ⟨ρ/L,⟨(div_pos hρ hL).le,(div_le_one hL).mpr hρL.le⟩,?_⟩
    change c + (ρ/L) • (q i-c) = c + ρ • angleDirection γ
    rw [hqi,add_sub_cancel_left,smul_smul,div_mul_cancel₀ _ hL.ne']
  have hxc : x ≠ c := by
    intro h
    have hz : ρ • angleDirection γ = 0 := add_left_cancel (h.trans (add_zero c).symm)
    exact (smul_ne_zero hρ.ne' (angleDirection_ne_zero γ)) hz
  have hxqi : x ≠ q i := by
    intro h
    rw [hqi] at h
    have heq : ρ • angleDirection γ = L • angleDirection γ := add_left_cancel h
    have heq' : ρ = L := (smul_left_injective ℝ (angleDirection_ne_zero γ)) heq
    exact hρL.ne heq'
  have hxcS : x ∈ Metric.ball c S := by
    change dist (c + ρ • angleDirection γ) c < S
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    exact (mul_le_of_le_one_right hρ.le (angleDirection_norm_le_one γ)).trans_lt hρS
  obtain ⟨r,hr,hline⟩ := finite_star_arm_line_neighborhood (planeImage D) c q S
    hmodel hsep i x hxseg hxc hxqi hxcS
  have hcqi : c ≠ q i := by
    intro h
    exact hxc (by simpa only [← h,segment_same,mem_singleton_iff] using hxseg)
  have hxdet : planeDet c (q i) x = 0 :=
    (mem_plane_line_iff hcqi x).mp (SegmentRegularity.segment_subset_line c (q i) hxseg)
  obtain ⟨H,hH,_⟩ := local_line_faces D hcqi hxdet hr hline
  have hFH : F = H positive := by
    have hinter : (angularSector c R α β ∩ lineHalfBall c (q i) x r positive).Nonempty := by
      rcases hbound with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rw [hqi]
        exact angularSector_meets_left_halfBall c hL ⟨hρ,hρR⟩ hαβ hr
      · rw [hqi]
        exact angularSector_meets_right_halfBall c hL ⟨hρ,hρR⟩ hαβ hr
    obtain ⟨z,hzF,hzH⟩ := hinter
    exact face_eq_of_mem_regions D (hF ⟨z,hzF,rfl⟩) ((hH positive).1 ⟨z,hzH,rfl⟩)
  refine ⟨x,r,hxseg,hxc,hxqi,hr,hline,?_⟩
  rw [hFH]
  exact (hH positive).1


lemma vertexSectorFace_left_halfBall {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (v : V) (w : G.neighborSet v) :
    ∃ (x : Point) (r : ℝ),
      x ∈ segment ℝ (D.point v) (vertexSegmentEndpoints D v w) ∧
      x ≠ D.point v ∧ x ≠ vertexSegmentEndpoints D v w ∧ 0 < r ∧
      (∀ y ∈ Metric.ball x r, y ∈ planeImage D ↔
        planeDet (D.point v) (vertexSegmentEndpoints D v w) y = 0) ∧
      OnePoint.some '' lineHalfBall (D.point v) (vertexSegmentEndpoints D v w) x r true ⊆
        faceRegion D (vertexSectorFace D v w) := by
  let c := D.point v
  let q := vertexSegmentEndpoints D v
  let α := vertexNeighborAngle D v w
  let β := sectorEndAngle α (vertexNeighborAngle D v ((drawingRotation D).turn v w))
  let L := ‖Complex.equivRealProdCLM.symm (q w-c)‖
  have hL : 0 < L := directionAngle_magnitude_pos
    (sub_ne_zero.mpr (vertexSegmentEndpoints_properties D v w).1)
  have hqw : q w = c + L • angleDirection α := by
    change q w = c +
      ‖Complex.equivRealProdCLM.symm (q w-c)‖ • angleDirection (planeDirectionAngle (q w-c))
    rw [directionAngle_polar_decomposition,add_sub_cancel]
  exact sector_boundary_arm_local_side D c q (drawingVertexRadius_geometry D v).1
    (vertexSectorFace_geometry D v w).1
    (directionAngle_lt_sectorEndAngle _ _) hL
    (drawingVertexRadius_geometry D v).2.2.1
    (incident_segments_inter_subset D v q (fun j => (vertexSegmentEndpoints_properties D v j).2))
    w hqw true (Or.inl ⟨rfl,rfl⟩) (vertexSectorFace D v w)
    (vertexSectorFace_geometry D v w).2.1

lemma vertexSectorFace_right_halfBall {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (v : V) (w : G.neighborSet v) :
    let w' := (drawingRotation D).turn v w
    ∃ (x : Point) (r : ℝ),
      x ∈ segment ℝ (D.point v) (vertexSegmentEndpoints D v w') ∧
      x ≠ D.point v ∧ x ≠ vertexSegmentEndpoints D v w' ∧ 0 < r ∧
      (∀ y ∈ Metric.ball x r, y ∈ planeImage D ↔
        planeDet (D.point v) (vertexSegmentEndpoints D v w') y = 0) ∧
      OnePoint.some '' lineHalfBall (D.point v) (vertexSegmentEndpoints D v w') x r false ⊆
        faceRegion D (vertexSectorFace D v w) := by
  let c := D.point v
  let q := vertexSegmentEndpoints D v
  let w' := (drawingRotation D).turn v w
  let α := vertexNeighborAngle D v w
  let β := sectorEndAngle α (vertexNeighborAngle D v w')
  let L := ‖Complex.equivRealProdCLM.symm (q w'-c)‖
  have hL : 0 < L := directionAngle_magnitude_pos
    (sub_ne_zero.mpr (vertexSegmentEndpoints_properties D v w').1)
  have hqw : q w' = c + L • angleDirection β := by
    change q w' = c + L • angleDirection (sectorEndAngle α (vertexNeighborAngle D v w'))
    rw [angleDirection_sectorEndAngle]
    change q w' = c +
      ‖Complex.equivRealProdCLM.symm (q w'-c)‖ • angleDirection (planeDirectionAngle (q w'-c))
    rw [directionAngle_polar_decomposition,add_sub_cancel]
  exact sector_boundary_arm_local_side D c q (drawingVertexRadius_geometry D v).1
    (vertexSectorFace_geometry D v w).1
    (directionAngle_lt_sectorEndAngle _ _) hL
    (drawingVertexRadius_geometry D v).2.2.1
    (incident_segments_inter_subset D v q (fun j => (vertexSegmentEndpoints_properties D v j).2))
    w' hqw false (Or.inr ⟨rfl,rfl⟩) (vertexSectorFace D v w)
    (vertexSectorFace_geometry D v w).2.1


lemma ArcRightSectorFace.eq_halfBall_on_straight_subarc
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    {a t b : unitInterval} (hat : a < t) (htb : t < b)
    (hbig : p '' Icc a b = segment ℝ (p a) (p b))
    {F H : Face D} (hF : ArcRightSectorFace D p t F)
    {r : ℝ} (hr : 0 < r)
    (hH : OnePoint.some '' lineHalfBall (p b) (p a) (p t) r true ⊆ faceRegion D H) :
    F = H := by
  obtain ⟨s,u,R,hs,hu,hR,hback,hfront,hF⟩ := hF
  have hθ := PolygonalGeometry.ordered_chart_inside_straight_subarc_directionAngle
    p hp hpi hat htb hs hu hbig hback hfront
  rw [hθ.1,hθ.2] at hF
  let d := p a-p b
  let L := ‖Complex.equivRealProdCLM.symm d‖
  have hd : d ≠ 0 := sub_ne_zero.mpr (hpi.ne (hat.trans htb).ne)
  have hL : 0 < L := directionAngle_magnitude_pos hd
  have hld : L • angleDirection (planeDirectionAngle d) = d := directionAngle_polar_decomposition d
  have hpt : p t ∈ segment ℝ (p b) (p a) := by
    rw [segment_symm,← hbig]
    exact ⟨t,⟨hat.le,htb.le⟩,rfl⟩
  have hx : planeDet (p b) (p a) (p t) = 0 :=
    (mem_plane_line_iff (hpi.ne (hat.trans htb).ne') (p t)).mp
      (SegmentRegularity.segment_subset_line _ _ hpt)
  apply sector_face_eq_center_left_halfBall D (p t) hL hR
    (directionAngle_lt_sectorEndAngle _ _) hr hF
  rw [hld]
  have hshift : lineHalfBall (p t) (p t+d) (p t) r true =
      lineHalfBall (p b) (p a) (p t) r true := by
    simpa only [one_smul] using
      lineHalfBall_shift_smul (p b) (p a) (p t) 1 r hx zero_lt_one true
  rw [hshift]
  exact hH

lemma planeDet_reverse (a b y : Point) : planeDet b a y = -planeDet a b y := by
  dsimp [planeDet,FiniteCombinatorics.Graph.Plane.FaceSideAux.planeDet]
  ring

lemma lineHalfBall_reverse (a b x : Point) (r : ℝ) :
    lineHalfBall b a x r true = lineHalfBall a b x r false := by
  ext y
  change (y ∈ Metric.ball x r ∧ 0 < planeDet b a y) ↔
    (y ∈ Metric.ball x r ∧ planeDet a b y < 0)
  rw [planeDet_reverse a b y,neg_pos]

lemma ordered_sector_eq_left_branch_face
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    {s t u v : unitInterval} (hst : s < t) (htu : t < u)
    (hsv : s < v) (hvt : v < t)
    (hleft : p '' Icc s t = segment ℝ (p s) (p t))
    {R : ℝ} (hR : 0 < R)
    (hmodel : planeImage D ∩ Metric.ball (p t) R =
      (segment ℝ (p t) (p s) ∪ segment ℝ (p t) (p u)) ∩ Metric.ball (p t) R)
    (hsep : segment ℝ (p t) (p s) ∩ segment ℝ (p t) (p u) = {p t})
    (hyR : p v ∈ Metric.ball (p t) R)
    (hnear : ‖Complex.equivRealProdCLM.symm (p v-p t)‖ < R)
    {F H : Face D}
    (hF : OnePoint.some '' angularSector (p t) R (planeDirectionAngle (p s-p t))
      (sectorEndAngle (planeDirectionAngle (p s-p t)) (planeDirectionAngle (p u-p t))) ⊆
        faceRegion D F)
    (hH : ArcRightSectorFace D p v H) : F = H := by
  have hy : p v ∈ segment ℝ (p t) (p s) := by
    rw [segment_symm,← hleft]
    exact ⟨v,⟨hsv.le,hvt.le⟩,rfl⟩
  have hys : p v ≠ p s := hpi.ne hsv.ne'
  have hyt : p v ≠ p t := hpi.ne hvt.ne
  obtain ⟨r,hr,hline⟩ := two_ray_branch_interior_locally_line D (p t) (p s) (p u) (p v)
    (hpi.ne hst.ne') hmodel hsep hy hyt hys hyR
  have hyline : planeDet (p t) (p s) (p v) = 0 :=
    (mem_plane_line_iff (hpi.ne hst.ne') _).mp (SegmentRegularity.segment_subset_line _ _ hy)
  obtain ⟨faces,hfaces,_⟩ := local_line_faces D (hpi.ne hst.ne') hyline hr hline
  have hHH : H = faces true := ArcRightSectorFace.eq_halfBall_on_straight_subarc D p hp hpi
    hsv hvt hleft hH hr (hfaces true).1
  have hd : p s-p t ≠ 0 := sub_ne_zero.mpr (hpi.ne hst.ne)
  have hyd : p v-p t ≠ 0 := sub_ne_zero.mpr hyt
  let L := ‖Complex.equivRealProdCLM.symm (p s-p t)‖
  let ρ := ‖Complex.equivRealProdCLM.symm (p v-p t)‖
  have hL : 0 < L := directionAngle_magnitude_pos hd
  have hρ : ρ ∈ Ioo (0:ℝ) R := ⟨directionAngle_magnitude_pos hyd,hnear⟩
  have hθ : planeDirectionAngle (p v-p t) = planeDirectionAngle (p s-p t) :=
    PolygonalGeometry.directionAngle_eq_of_sameRay hyd hd (mem_segment_iff_wbtw.mp hy).sameRay_vsub_left
  have hsPolar : p t + L • angleDirection (planeDirectionAngle (p s-p t)) = p s := by
    rw [directionAngle_polar_decomposition]
    exact add_sub_cancel _ _
  have hyPolar : p t + ρ • angleDirection (planeDirectionAngle (p s-p t)) = p v := by
    rw [← hθ,directionAngle_polar_decomposition]
    exact add_sub_cancel _ _
  have hFF : F = faces true := by
    apply sector_face_eq_left_halfBall D (p t) hL hρ
      (directionAngle_lt_sectorEndAngle _ _) hr hF
    rw [hsPolar,hyPolar]
    exact (hfaces true).1
  exact hFF.trans hHH.symm

lemma ordered_sector_eq_right_branch_face
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    {s t u v : unitInterval} (hst : s < t) (htu : t < u)
    (htv : t < v) (hvu : v < u)
    (hright : p '' Icc t u = segment ℝ (p t) (p u))
    {R : ℝ} (hR : 0 < R)
    (hmodel : planeImage D ∩ Metric.ball (p t) R =
      (segment ℝ (p t) (p s) ∪ segment ℝ (p t) (p u)) ∩ Metric.ball (p t) R)
    (hsep : segment ℝ (p t) (p s) ∩ segment ℝ (p t) (p u) = {p t})
    (hyR : p v ∈ Metric.ball (p t) R)
    (hnear : ‖Complex.equivRealProdCLM.symm (p v-p t)‖ < R)
    {F H : Face D}
    (hF : OnePoint.some '' angularSector (p t) R (planeDirectionAngle (p s-p t))
      (sectorEndAngle (planeDirectionAngle (p s-p t)) (planeDirectionAngle (p u-p t))) ⊆
        faceRegion D F)
    (hH : ArcRightSectorFace D p v H) : F = H := by
  have hy : p v ∈ segment ℝ (p t) (p u) := by
    rw [← hright]
    exact ⟨v,⟨htv.le,hvu.le⟩,rfl⟩
  have hyu : p v ≠ p u := hpi.ne hvu.ne
  have hyt : p v ≠ p t := hpi.ne htv.ne'
  have hmodel' : planeImage D ∩ Metric.ball (p t) R =
      (segment ℝ (p t) (p u) ∪ segment ℝ (p t) (p s)) ∩ Metric.ball (p t) R := by
    rwa [union_comm] at hmodel
  have hsep' : segment ℝ (p t) (p u) ∩ segment ℝ (p t) (p s) = {p t} := by
    rwa [inter_comm] at hsep
  obtain ⟨r,hr,hline⟩ := two_ray_branch_interior_locally_line D (p t) (p u) (p s) (p v)
    (hpi.ne htu.ne) hmodel' hsep' hy hyt hyu hyR
  have hyline : planeDet (p t) (p u) (p v) = 0 :=
    (mem_plane_line_iff (hpi.ne htu.ne) _).mp (SegmentRegularity.segment_subset_line _ _ hy)
  obtain ⟨faces,hfaces,_⟩ := local_line_faces D (hpi.ne htu.ne) hyline hr hline
  have hHH : H = faces false := by
    apply ArcRightSectorFace.eq_halfBall_on_straight_subarc D p hp hpi htv hvu hright hH hr
    rw [lineHalfBall_reverse]
    exact (hfaces false).1
  have hd : p u-p t ≠ 0 := sub_ne_zero.mpr (hpi.ne htu.ne')
  have hyd : p v-p t ≠ 0 := sub_ne_zero.mpr hyt
  let L := ‖Complex.equivRealProdCLM.symm (p u-p t)‖
  let ρ := ‖Complex.equivRealProdCLM.symm (p v-p t)‖
  have hL : 0 < L := directionAngle_magnitude_pos hd
  have hρ : ρ ∈ Ioo (0:ℝ) R := ⟨directionAngle_magnitude_pos hyd,hnear⟩
  have hθ : planeDirectionAngle (p v-p t) = planeDirectionAngle (p u-p t) :=
    PolygonalGeometry.directionAngle_eq_of_sameRay hyd hd (mem_segment_iff_wbtw.mp hy).sameRay_vsub_left
  have huPolar : p t + L • angleDirection
      (sectorEndAngle (planeDirectionAngle (p s-p t)) (planeDirectionAngle (p u-p t))) = p u := by
    rw [angleDirection_sectorEndAngle,directionAngle_polar_decomposition]
    exact add_sub_cancel _ _
  have hyPolar : p t + ρ • angleDirection
      (sectorEndAngle (planeDirectionAngle (p s-p t)) (planeDirectionAngle (p u-p t))) = p v := by
    rw [angleDirection_sectorEndAngle,← hθ,directionAngle_polar_decomposition]
    exact add_sub_cancel _ _
  have hFF : F = faces false := by
    apply sector_face_eq_right_halfBall D (p t) hL hρ
      (directionAngle_lt_sectorEndAngle _ _) hr hF
    rw [huPolar,hyPolar]
    exact (hfaces false).1
  exact hFF.trans hHH.symm

/-- The actual right side of an original polygonal edge is locally constant
through both straight portions and genuine corners. -/
theorem edgeInteriorRightFace_isLocallyConstant
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (v w : V) (h : G.Adj v w) (p : _root_.Path (D.point v) (D.point w))
    (hpi : Function.Injective p) (hpr : range p = D.edge ⟨s(v,w),h⟩) :
    IsLocallyConstant (edgeInteriorRightFace D v w h p hpi hpr) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro t
  have hpoly : IsPolygonal (range p) := hpr.symm ▸ (D.edge_arc v w h).1
  have hn := edge_path_interior_nonvertex D v w h p hpi hpr t.val t.property.1 t.property.2
  obtain ⟨s,u,R,hs,hu,hR,hleft,hright,hsep,hmodel,F,hF,_⟩ :=
    oriented_edge_interior_sector_face D ⟨s(v,w),h⟩ p p.continuous hpi hpr hpoly
      t.val t.property.1 t.property.2 hn
  have hFc : F = edgeInteriorRightFace D v w h p hpi hpr t :=
    ArcRightSectorFace.unique D p hpi ⟨s,u,R,hs,hu,hR,hleft,hright,hF⟩
      (edgeInteriorRightFace_geometry D v w h p hpi hpr t)
  rw [hFc] at hF
  let W : Set unitInterval := Ioo s u ∩
    (p ⁻¹' Metric.ball (p t.val) R ∩
      {z | ‖Complex.equivRealProdCLM.symm (p z-p t.val)‖ < R})
  have hnorm : Continuous (fun z : unitInterval => ‖Complex.equivRealProdCLM.symm (p z-p t.val)‖) := by
    fun_prop
  have hWopen : IsOpen W :=
    isOpen_Ioo.inter ((Metric.isOpen_ball.preimage p.continuous).inter
      (isOpen_lt hnorm continuous_const))
  have htW : t.val ∈ W := by
    refine ⟨⟨hs,hu⟩,Metric.mem_ball_self hR,?_⟩
    change ‖Complex.equivRealProdCLM.symm (p t.val-p t.val)‖ < R
    simpa only [sub_self,map_zero,norm_zero] using hR
  refine ⟨Subtype.val ⁻¹' W,hWopen.preimage continuous_subtype_val,htW,?_⟩
  intro y hy
  have hy' : y.val ∈ W := hy
  obtain ⟨⟨hsy,hyu⟩,hyp,hyN⟩ := hy'
  have hyFace := edgeInteriorRightFace_geometry D v w h p hpi hpr y
  rcases lt_trichotomy y.val t.val with hyt | hyt | hty
  · exact (ordered_sector_eq_left_branch_face D p p.continuous hpi hs hu hsy hyt
      hleft hR hmodel hsep hyp hyN hF hyFace).symm
  · have hyEq : y = t := Subtype.ext hyt
    rw [hyEq]
  · exact (ordered_sector_eq_right_branch_face D p p.continuous hpi hs hu hty hyu
      hright hR hmodel hsep hyp hyN hF hyFace).symm

/-- Each original edge has one constant actual right-side face, even when it
bends and even when its right and left faces coincide. -/
theorem edgeInteriorRightFace_eq
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (v w : V) (h : G.Adj v w) (p : _root_.Path (D.point v) (D.point w))
    (hpi : Function.Injective p) (hpr : range p = D.edge ⟨s(v,w),h⟩)
    (t u : Ioo (0 : unitInterval) 1) :
    edgeInteriorRightFace D v w h p hpi hpr t = edgeInteriorRightFace D v w h p hpi hpr u := by
  letI : PreconnectedSpace (Ioo (0 : unitInterval) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  exact (edgeInteriorRightFace_isLocallyConstant D v w h p hpi hpr).apply_eq_of_preconnectedSpace t u


/-- For the edge from v to w, the sector immediately before that outgoing
edge at v agrees with the sector immediately after its reversed direction at w.
This is exactly the endpoint compatibility needed for successor invariance. -/
lemma drawingSideLabel_successor_of_endpoint_compatibility
    {V : Type u} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (h : ∀ (v : V) (w z : G.neighborSet v), (drawingRotation D).turn v z = w →
      vertexSectorFace D v z = vertexSectorFace D w.val ⟨v,w.property.symm⟩) :
    ∀ d : G.Dart, drawingSideLabel D (sideSuccessor (drawingRotation D) d) =
      drawingSideLabel D d := by
  intro d
  exact (h d.snd ((drawingRotation D).turn d.snd ⟨d.fst,d.adj.symm⟩)
    ⟨d.fst,d.adj.symm⟩ rfl).symm

/-- A version of endpoint compatibility with the next neighbor written directly.
It avoids any obligation to rewrite equality proofs in the neighbor subtype. -/
lemma drawingSideLabel_successor_of_next_sector_compatibility
    {V : Type u} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (h : ∀ (v : V) (z : G.neighborSet v),
      vertexSectorFace D v z =
        vertexSectorFace D ((drawingRotation D).turn v z).val
          ⟨v,((drawingRotation D).turn v z).property.symm⟩) :
    ∀ d : G.Dart, drawingSideLabel D (sideSuccessor (drawingRotation D) d) =
      drawingSideLabel D d := by
  intro d
  exact (h d.snd ⟨d.fst,d.adj.symm⟩).symm

/-- The actual endpoint compatibility, once established for the already
constructed sector labels, completes the unchanged full directed-side theorem. -/
theorem face_sides_of_endpoint_compatibility
    (h : ∀ {W : Type u} [Finite W] {H : SimpleGraph W} (D : PlaneEmbedding H),
      H.Connected → 3 ≤ Nat.card W →
      ∀ (v : W) (w z : H.neighborSet v), (drawingRotation D).turn v z = w →
        vertexSectorFace D v z = vertexSectorFace D w.val ⟨v,w.property.symm⟩) :
    FiniteCombinatorics.Graph.Plane.FaceSideAux.face_sidesType.{u} := by
  apply face_sides_of_drawing_label_compatibility drawingSideLabel_surjective
  intro W _ H D hc hv
  exact drawingSideLabel_successor_of_endpoint_compatibility D (h D hc hv)

namespace FaceSides

/-- This conditional helper has precisely the mandatory numerical conclusion;
the public unconditional target can only follow after proving its premise. -/
theorem face_bounds_of_endpoint_compatibility
    (h : ∀ {W : Type u} [Finite W] {H : SimpleGraph W} (D : PlaneEmbedding H),
      H.Connected → 3 ≤ Nat.card W →
      ∀ (v : W) (w z : H.neighborSet v), (drawingRotation D).turn v z = w →
        vertexSectorFace D v z = vertexSectorFace D w.val ⟨v,w.property.symm⟩) :
    Specs.FiniteCombinatorics.Graph.Plane.FaceSides.face_boundsType.{u} :=
  face_bounds_of_face_sides (face_sides_of_endpoint_compatibility h)

end FaceSides

end FiniteCombinatorics.Graph.Plane

noncomputable section
namespace FiniteCombinatorics.Graph.Plane
open Set

/-- A right-side face at an interior parameter of an initial straight segment
agrees with the negative halfball along that outgoing endpoint segment. -/
theorem exists_initial_right_face_eq_of_halfBall
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    (face : Ioo (0 : unitInterval) 1 → Face D)
    (hface : ∀ t, ArcRightSectorFace D p t.val (face t))
    {q x : Point} (hq : q ≠ p 0) (hseg : segment ℝ (p 0) q ⊆ range p)
    (hx : x ∈ segment ℝ (p 0) q) (hx0 : x ≠ p 0) (hxq : x ≠ q)
    {r : ℝ} (hr : 0 < r) (F : Face D)
    (hF : OnePoint.some '' lineHalfBall (p 0) q x r false ⊆ faceRegion D F) :
    ∃ t, face t = F := by
  obtain ⟨u,hu,huq,hsub⟩ :=
    PolygonalGeometry.exists_initial_straight_subarc_of_segment_subset p hp hpi hq hseg
  obtain ⟨t,ht,htx⟩ := hsub ▸ hx
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
    intro h
    exact hx0 (htx.symm.trans (congrArg p h.symm)))
  have htu : t < u := lt_of_le_of_ne ht.2 (by
    intro h
    exact hxq (htx.symm.trans ((congrArg p h).trans huq)))
  let t' : Ioo (0 : unitInterval) 1 := ⟨t,ht0,htu.trans_le u.property.2⟩
  refine ⟨t',?_⟩
  apply ArcRightSectorFace.eq_halfBall_on_straight_subarc D p hp hpi ht0 htu
    (by simpa only [huq] using hsub) (hface t') hr
  rw [huq,lineHalfBall_reverse,htx]
  exact hF

/-- A right-side face at an interior parameter of a final straight segment
agrees with the positive halfball along that incoming reversed endpoint ray. -/
theorem exists_final_right_face_eq_of_halfBall
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (p : unitInterval → Point) (hp : Continuous p) (hpi : Function.Injective p)
    (face : Ioo (0 : unitInterval) 1 → Face D)
    (hface : ∀ t, ArcRightSectorFace D p t.val (face t))
    {q x : Point} (hq : q ≠ p 1) (hseg : segment ℝ (p 1) q ⊆ range p)
    (hx : x ∈ segment ℝ (p 1) q) (hx1 : x ≠ p 1) (hxq : x ≠ q)
    {r : ℝ} (hr : 0 < r) (F : Face D)
    (hF : OnePoint.some '' lineHalfBall (p 1) q x r true ⊆ faceRegion D F) :
    ∃ t, face t = F := by
  obtain ⟨s,hs,hsq,hsub⟩ :=
    PolygonalGeometry.exists_final_straight_subarc_of_segment_subset p hp hpi hq hseg
  have hx' : x ∈ segment ℝ q (p 1) := by rwa [segment_symm]
  obtain ⟨t,ht,htx⟩ := hsub ▸ hx'
  have hst : s < t := lt_of_le_of_ne ht.1 (by
    intro h
    exact hxq (htx.symm.trans ((congrArg p h.symm).trans hsq)))
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by
    intro h
    exact hx1 (htx.symm.trans (congrArg p h)))
  let t' : Ioo (0 : unitInterval) 1 := ⟨t,s.property.1.trans_lt hst,ht1⟩
  refine ⟨t',?_⟩
  apply ArcRightSectorFace.eq_halfBall_on_straight_subarc D p hp hpi hst ht1
    (by simpa only [hsq] using hsub) (hface t') hr
  rw [hsq,htx]
  exact hF

end FiniteCombinatorics.Graph.Plane

noncomputable section
namespace FiniteCombinatorics.Graph.Plane
open Set

/-- At the source of an oriented edge, the sector ending at that outgoing
edge belongs to the edge's actual right face. -/
theorem edgeInteriorRightFace_source_sector
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (v w : V) (h : G.Adj v w) (p : _root_.Path (D.point v) (D.point w))
    (hpi : Function.Injective p) (hpr : range p = D.edge ⟨s(v,w),h⟩)
    (z : G.neighborSet v) (hz : (drawingRotation D).turn v z = ⟨w,h⟩) :
    ∃ t, edgeInteriorRightFace D v w h p hpi hpr t = vertexSectorFace D v z := by
  obtain ⟨x,r,hx,hxc,hxq,hr,_,hF⟩ := vertexSectorFace_right_halfBall D v z
  rw [hz] at hx hxq hF
  let q := vertexSegmentEndpoints D v ⟨w,h⟩
  have hq : q ≠ p 0 := by
    rw [p.source]
    exact (vertexSegmentEndpoints_properties D v ⟨w,h⟩).1
  have hseg : segment ℝ (p 0) q ⊆ range p := by
    rw [p.source,hpr]
    exact (vertexSegmentEndpoints_properties D v ⟨w,h⟩).2
  apply exists_initial_right_face_eq_of_halfBall D p p.continuous hpi
    (edgeInteriorRightFace D v w h p hpi hpr)
    (edgeInteriorRightFace_geometry D v w h p hpi hpr) hq hseg
    (by simpa only [p.source] using hx) (by simpa only [p.source] using hxc) hxq hr
    (vertexSectorFace D v z)
  simpa only [p.source] using hF

/-- At the target, the sector after the reversed incoming edge belongs to
that edge's actual right face. -/
theorem edgeInteriorRightFace_target_sector
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (v w : V) (h : G.Adj v w) (p : _root_.Path (D.point v) (D.point w))
    (hpi : Function.Injective p) (hpr : range p = D.edge ⟨s(v,w),h⟩) :
    ∃ t, edgeInteriorRightFace D v w h p hpi hpr t =
      vertexSectorFace D w ⟨v,h.symm⟩ := by
  obtain ⟨x,r,hx,hxc,hxq,hr,_,hF⟩ := vertexSectorFace_left_halfBall D w ⟨v,h.symm⟩
  let q := vertexSegmentEndpoints D w ⟨v,h.symm⟩
  have hq : q ≠ p 1 := by
    rw [p.target]
    exact (vertexSegmentEndpoints_properties D w ⟨v,h.symm⟩).1
  have he : incidentEdge w ⟨v,h.symm⟩ = ⟨s(v,w),h⟩ := by
    apply Subtype.ext
    exact Sym2.eq_swap
  have hseg : segment ℝ (p 1) q ⊆ range p := by
    rw [p.target,hpr]
    simpa only [he] using (vertexSegmentEndpoints_properties D w ⟨v,h.symm⟩).2
  apply exists_final_right_face_eq_of_halfBall D p p.continuous hpi
    (edgeInteriorRightFace D v w h p hpi hpr)
    (edgeInteriorRightFace_geometry D v w h p hpi hpr) hq hseg
    (by simpa only [p.target] using hx) (by simpa only [p.target] using hxc) hxq hr
    (vertexSectorFace D w ⟨v,h.symm⟩)
  simpa only [p.target] using hF

end FiniteCombinatorics.Graph.Plane

noncomputable section
namespace FiniteCombinatorics.Graph.Plane
open Set

/-- The sector before an outgoing edge at its source is the same actual face
as the sector after its reversed incoming direction at the target. -/
theorem drawing_vertex_sector_endpoint_compatibility
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)
    (v : V) (w z : G.neighborSet v) (hz : (drawingRotation D).turn v z = w) :
    vertexSectorFace D v z = vertexSectorFace D w.val ⟨v,w.property.symm⟩ := by
  obtain ⟨_,p,hpi,hpr⟩ := D.edge_arc v w.val w.property
  obtain ⟨t,ht⟩ := edgeInteriorRightFace_source_sector D v w.val w.property p hpi hpr z hz
  obtain ⟨u,hu⟩ := edgeInteriorRightFace_target_sector D v w.val w.property p hpi hpr
  exact ht.symm.trans ((edgeInteriorRightFace_eq D v w.val w.property p hpi hpr t u).trans hu)

end FiniteCombinatorics.Graph.Plane

namespace FiniteCombinatorics.Graph.Plane

/-- The successor carries every directed edge side to the same actual face.
No assumption on the topology of the faces is required. -/
theorem drawingSideLabel_successor {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (d : G.Dart) :
    drawingSideLabel D (sideSuccessor (drawingRotation D) d) = drawingSideLabel D d :=
  drawingSideLabel_successor_of_endpoint_compatibility D
    (drawing_vertex_sector_endpoint_compatibility D) d

namespace FaceSides

/-- The angular successor, its exact closed boundary walks, and the surjective
assignment of their directed sides to the actual sphere-complement faces. -/
theorem face_sides : FiniteCombinatorics.Graph.Plane.FaceSideAux.face_sidesType.{u} := by
  apply face_sides_of_drawing_label_compatibility drawingSideLabel_surjective
  intro V _ G D _ _
  exact drawingSideLabel_successor D

/-- The unconditional directed-side bounds of W62, counting both directions
of each bridge even when its two sides belong to the same face. -/
theorem face_bounds : Specs.FiniteCombinatorics.Graph.Plane.FaceSides.face_boundsType.{u} :=
  face_bounds_of_face_sides face_sides

end FaceSides
end FiniteCombinatorics.Graph.Plane

namespace FiniteCombinatorics.Graph.Plane

/-- The actual face assigned to a closed boundary-walk orbit. -/
def drawingOrbitLabel {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) : BoundaryOrbit (drawingRotation D) → Face D :=
  orbitLabel (drawingRotation D) (drawingSideLabel D) (drawingSideLabel_successor D)

@[simp] theorem drawingOrbitLabel_mk {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (d : G.Dart) :
    drawingOrbitLabel D (boundaryOrbitMk (drawingRotation D) d) = drawingSideLabel D d := rfl

/-- Every actual face receives at least one complete boundary-walk orbit. -/
theorem drawingOrbitLabel_surjective {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (hc : G.Connected) (hv : 3 ≤ Nat.card V) :
    Function.Surjective (drawingOrbitLabel D) :=
  orbitLabel_surjective (drawingRotation D) (drawingSideLabel D)
    (drawingSideLabel_successor D) (drawingSideLabel_surjective D hc hv)

end FiniteCombinatorics.Graph.Plane
