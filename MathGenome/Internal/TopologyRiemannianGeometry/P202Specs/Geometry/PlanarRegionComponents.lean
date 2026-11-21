import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionFoundation

/-! Independent statements for the complementary-component and orientation
part of paper.tex 4773–4787. All components refer to the actual complement
in the one-point compactification of the actual Euclidean plane. -/
noncomputable section
open Set Topology

namespace P202Specs.PlanarRegionTopology

/-- The embedded trace in the compactified plane. -/
def sphericalTrace (c : RegularJordanCurve) : Set (OnePoint Plane) :=
  (fun x : Plane => (x : OnePoint Plane)) '' c.trace

/-- Spherical Jordan sides with the side at infinity distinguished. -/
structure SphericalJordanSides (c : RegularJordanCurve) where
  boundedSide : Set (OnePoint Plane)
  unboundedSide : Set (OnePoint Plane)
  bounded_open : IsOpen boundedSide
  unbounded_open : IsOpen unboundedSide
  bounded_connected : IsConnected boundedSide
  unbounded_connected : IsConnected unboundedSide
  disjoint : Disjoint boundedSide unboundedSide
  union_eq : boundedSide ∪ unboundedSide = (sphericalTrace c)ᶜ
  bounded_frontier : frontier boundedSide = sphericalTrace c
  unbounded_frontier : frontier unboundedSide = sphericalTrace c
  infinity_not_bounded : (OnePoint.infty : OnePoint Plane) ∉ boundedSide
  infinity_unbounded : (OnePoint.infty : OnePoint Plane) ∈ unboundedSide

namespace Expected

/-- The full component and universal orientation obligation. The existence of
an induced sign family is a separate conclusion of the local geometry goal. -/
def complementComponents : Prop := ∀ R : PlanarRegion,
  ∃ S : ComplementData R, ∀ s, IsInducedBoundaryOrientation R s → ∀ i,
    (HasSideOnLeft (S.sides.boundedSide i) (R.curve i) (s i) ↔ i = S.sides.outer) ∧
    (HasSideOnLeft (S.sides.boundedSide i) (R.curve i) (-s i) ↔ i ≠ S.sides.outer)

/-- Jordan separation transported to the canonical compactified plane. -/
def sphericalJordanSeparation : Prop := ∀ c : RegularJordanCurve,
  ∃ A B : Set (OnePoint Plane),
    IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
    Disjoint A B ∧ A ∪ B = (sphericalTrace c)ᶜ ∧
    frontier A = sphericalTrace c ∧ frontier B = sphericalTrace c

/-- Each curve bounds a distinct actual complementary component. This is
an intermediate conclusion, without any component-count assumption. -/
def curveOutsideComponents : Prop := ∀ R : PlanarRegion,
  ∃ e : Fin R.boundaryCount ↪ ConnectedComponents (SphericalComplement R),
    ∀ i, frontier (sphericalComponentSet R (e i)) = sphericalTrace (R.curve i)

/-- Exact spherical component count and matching of every frontier. -/
def sphericalComponents : Prop := ∀ R : PlanarRegion,
  ∃ e : Fin R.boundaryCount ≃ ConnectedComponents (SphericalComplement R),
    ∀ i, frontier (sphericalComponentSet R (e i)) = sphericalTrace (R.curve i)

/-- Both planar Jordan sides, including connectedness after removing infinity. -/
def planarJordanSeparation : Prop := ∀ c : RegularJordanCurve,
  ∃ A B : Set Plane,
    IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
    Bornology.IsBounded A ∧ ¬Bornology.IsBounded B ∧ Disjoint A B ∧
    A ∪ B = c.traceᶜ ∧ frontier A = c.trace ∧ frontier B = c.trace

/-- All component, frontier, boundedness and domain-side conclusions. -/
def complementData : Prop := ∀ R : PlanarRegion, Nonempty (ComplementData R)

/-- The left-side half of the orientation rule, for every induced sign choice. -/
def boundedSideOnLeft : Prop := ∀ (R : PlanarRegion) (S : BoundarySides R)
  (s : Fin R.boundaryCount → ℝ), IsInducedBoundaryOrientation R s → ∀ i,
    HasSideOnLeft (S.boundedSide i) (R.curve i) (s i) ↔ i = S.outer

/-- The local smooth-arc assertion: opposite normal directions
enter opposite Jordan sides. This is an obligation, not a region hypothesis. -/
def normalSwitch : Prop := ∀ (c : RegularJordanCurve) (A B : Set Plane),
  IsOpen A → IsOpen B → IsConnected A → IsConnected B →
  Disjoint A B → A ∪ B = c.traceᶜ → frontier A = c.trace → frontier B = c.trace →
  ∀ s : ℝ, (s = 1 ∨ s = -1) →
    (HasSideOnLeft A c s ↔ HasSideOnLeft B c (-s))

/-- Assembly from Jordan data and the local smooth normal-switch statement. -/
def componentsAssembly : Prop := normalSwitch → complementComponents

end Expected
end P202Specs.PlanarRegionTopology
