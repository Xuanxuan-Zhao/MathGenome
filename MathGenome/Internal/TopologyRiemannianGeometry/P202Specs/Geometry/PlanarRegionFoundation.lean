import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.LocallyContractible
import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
Canonical interface and foundational targets for paper.tex 4762–4809.
The region is the closure of the given open domain. Its geometric hypotheses
do not include a surface atlas, a collar, a push, or a separation certificate.

Curves are parametrized by R/Z. Smooth arcs have smooth one-sided extensions
at their finitely many joins. Noncuspidality excludes opposite *directed*
unit tangents, allowing both convex and reflex corners. A finite set of joins
may include smooth points. The local side condition is stated using arbitrarily
small open neighborhoods whose inside and outside portions are connected and
nonempty; no boundary-flattening coordinates are assumed.

`OnePoint Plane` is the ordinary one-point compactification, i.e. the sphere
model with a distinguished point at infinity. `ComplementData` uses actual
connected components of the complement in this space.
-/

noncomputable section
open Set Topology
open scoped ContDiff

namespace P202Specs.PlanarRegionTopology

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev ParameterCircle := AddCircle (1 : ℝ)

/-- Rotation through +pi/2 for the standard plane orientation. -/
def quarterTurn (v : Plane) : Plane := !₂[-v 1, v 0]

/-- The lift to real parameters of a circle-parametrized curve. -/
def realLift (c : C(ParameterCircle, Plane)) (t : ℝ) : Plane := c (t : ParameterCircle)

/-- Local one-sided smooth extensions, with nonzero and nonopposite tangents.
The maps need only be smooth on the displayed open interval. -/
def HasRegularNoncuspidalJoin (c : C(ParameterCircle, Plane)) (t : ℝ) : Prop :=
  ∃ (δ : ℝ) (l r : ℝ → Plane), 0 < δ ∧
    ContDiffOn ℝ ∞ l (Ioo (t - δ) (t + δ)) ∧
    ContDiffOn ℝ ∞ r (Ioo (t - δ) (t + δ)) ∧
    EqOn l (realLift c) (Icc (t - δ) t) ∧
    EqOn r (realLift c) (Icc t (t + δ)) ∧
    deriv l t ≠ 0 ∧ deriv r t ≠ 0 ∧
    NormedSpace.normalize (deriv l t) ≠ -NormedSpace.normalize (deriv r t)

/-- A simple closed piecewise smooth regular curve with finitely many
noncuspidal joins. There is no prescribed choice of its orientation. -/
structure RegularJordanCurve where
  parametrization : C(ParameterCircle, Plane)
  injective : Function.Injective parametrization
  joins : Finset ParameterCircle
  smooth_off_joins : ∀ t : ℝ, (t : ParameterCircle) ∉ joins →
    ContDiffAt ℝ ∞ (realLift parametrization) t
  regular_joins : ∀ t : ℝ, HasRegularNoncuspidalJoin parametrization t

def RegularJordanCurve.trace (c : RegularJordanCurve) : Set Plane :=
  range c.parametrization

/-- Local one-sidedness without assuming any collar or manifold chart. -/
def LocallyOneSided (U : Set Plane) : Prop :=
  ∀ p ∈ frontier U, ∀ O : Set Plane, IsOpen O → p ∈ O →
    ∃ N : Set Plane, IsOpen N ∧ p ∈ N ∧ N ⊆ O ∧
      IsConnected (N ∩ U) ∧ IsConnected (N \ closure U)

/-- Exactly the geometric input of the planar-region lemma. -/
structure PlanarRegion where
  domain : Set Plane
  open_domain : IsOpen domain
  connected_domain : IsConnected domain
  compact_closure : IsCompact (closure domain)
  boundaryCount : ℕ
  boundaryCount_pos : 1 ≤ boundaryCount
  curve : Fin boundaryCount → RegularJordanCurve
  disjoint_curves : Pairwise (fun i j => Disjoint (curve i).trace (curve j).trace)
  boundary_eq : frontier domain = ⋃ i, (curve i).trace
  one_sided : LocallyOneSided domain

def PlanarRegion.carrier (R : PlanarRegion) : Set Plane := closure R.domain
def PlanarRegion.boundary (R : PlanarRegion) : Set Plane := frontier R.domain

/-- The standard closed half-plane, with its usual subspace topology. -/
abbrev HalfPlane := {v : Plane // 0 ≤ v 1}

/-- Local half-plane charts whose chart boundary is exactly the given subset.
The carrier already inherits Hausdorffness and second countability from R². -/
def IsSurfaceWithBoundary (K B : Set Plane) : Prop :=
  ∀ x : K, ∃ e : OpenPartialHomeomorph K HalfPlane,
    x ∈ e.source ∧ ∀ y ∈ e.source, (e y).val 1 = 0 ↔ y.val ∈ B

/-- A genuine closed collar. The image of the parameter interval [0,1)
is open in the carrier, including at parameter zero. Positive parameters
lie in the actual ambient interior, so this includes reflex corners. -/
structure BoundaryCollar (K B : Set Plane) where
  boundary_subset : B ⊆ K
  map : C(B × unitInterval, K)
  embedding : Topology.IsEmbedding map
  at_zero : ∀ x : B, (map (x, 0)).val = x.val
  positive_interior : ∀ (x : B) (t : unitInterval), 0 < (t : ℝ) →
    (map (x, t)).val ∈ interior K
  open_lower_image : IsOpen (map '' {z : B × unitInterval | (z.2 : ℝ) < 1})

/-- The actual interior inclusion, rather than an unspecified equivalence. -/
def interiorInclusion (K : Set Plane) : C(interior K, K) :=
  ⟨fun x => ⟨x.val, interior_subset x.property⟩, continuous_subtype_val.subtype_mk _⟩

def InteriorInclusionEquivalence (K : Set Plane) : Prop :=
  ∃ e : ContinuousMap.HomotopyEquiv (interior K) K,
    e.toFun = interiorInclusion K

/-- A homotopy pushing the entire carrier into its interior at time one,
and keeping points already in the interior there throughout the homotopy.
This is an intermediate construction, not an input to the region theorem. -/
structure InwardPush (K : Set Plane) where
  map : C(unitInterval × K, K)
  at_zero : ∀ x : K, map (0, x) = x
  at_one : ∀ x : K, (map (1, x)).val ∈ interior K
  interior_stays : ∀ (t : unitInterval) (x : K), x.val ∈ interior K →
    (map (t, x)).val ∈ interior K

def sphericalCarrier (R : PlanarRegion) : Set (OnePoint Plane) :=
  (fun x : Plane => (x : OnePoint Plane)) '' R.carrier

def SphericalComplement (R : PlanarRegion) := (sphericalCarrier R)ᶜ

/-- A component as an actual subset of the compactified plane. -/
def sphericalComponentSet (R : PlanarRegion)
    (a : ConnectedComponents (SphericalComplement R)) : Set (OnePoint Plane) :=
  Subtype.val '' {x : SphericalComplement R | ConnectedComponents.mk x = a}

def planarPart (A : Set (OnePoint Plane)) : Set Plane :=
  (fun x : Plane => (x : OnePoint Plane)) ⁻¹' A

/-- Jordan sides of every boundary curve, together with the unique outer
curve. These are conclusions, not input certificates. -/
structure BoundarySides (R : PlanarRegion) where
  boundedSide : Fin R.boundaryCount → Set Plane
  unboundedSide : Fin R.boundaryCount → Set Plane
  bounded_open : ∀ i, IsOpen (boundedSide i)
  unbounded_open : ∀ i, IsOpen (unboundedSide i)
  bounded_connected : ∀ i, IsConnected (boundedSide i)
  unbounded_connected : ∀ i, IsConnected (unboundedSide i)
  bounded : ∀ i, Bornology.IsBounded (boundedSide i)
  unbounded : ∀ i, ¬Bornology.IsBounded (unboundedSide i)
  sides_disjoint : ∀ i, Disjoint (boundedSide i) (unboundedSide i)
  sides_union : ∀ i, boundedSide i ∪ unboundedSide i = (R.curve i).traceᶜ
  bounded_frontier : ∀ i, frontier (boundedSide i) = (R.curve i).trace
  unbounded_frontier : ∀ i, frontier (unboundedSide i) = (R.curve i).trace
  outer : Fin R.boundaryCount
  domain_side : ∀ i, R.domain ⊆ if i = outer then boundedSide i else unboundedSide i

/-- Exactly b spherical complementary components, matched to their own
boundary curves; exactly the outer one is unbounded in the plane. -/
structure ComplementData (R : PlanarRegion) where
  sides : BoundarySides R
  component : Fin R.boundaryCount ≃ ConnectedComponents (SphericalComplement R)
  frontier_component : ∀ i,
    frontier (sphericalComponentSet R (component i)) =
      (fun x : Plane => (x : OnePoint Plane)) '' (R.curve i).trace
  planar_component : ∀ i, planarPart (sphericalComponentSet R (component i)) =
    if i = sides.outer then sides.unboundedSide i else sides.boundedSide i
  infinity_iff : ∀ i, (OnePoint.infty : OnePoint Plane) ∈ sphericalComponentSet R (component i) ↔
    i = sides.outer
  unbounded_iff : ∀ i,
    ¬Bornology.IsBounded (planarPart (sphericalComponentSet R (component i))) ↔
      i = sides.outer

/-- The left side of a directed regular arc is detected by small positive
translations along +pi/2 of its tangent. Joins are excluded from this test.
Changing `s` to `-s` interchanges left and right. -/
def HasSideOnLeft (A : Set Plane) (c : RegularJordanCurve) (s : ℝ) : Prop :=
  ∀ t : ℝ, (t : ParameterCircle) ∉ c.joins →
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      realLift c.parametrization t +
        r • (s • quarterTurn (deriv (realLift c.parametrization) t)) ∈ A

def IsInducedBoundaryOrientation (R : PlanarRegion)
    (s : Fin R.boundaryCount → ℝ) : Prop :=
  ∀ i, (s i = 1 ∨ s i = -1) ∧ HasSideOnLeft R.domain (R.curve i) (s i)

/-- Existence of the induced orientation, and its bounded-side description
for every choice of positively oriented boundary parametrizations. -/
def BoundaryOrientationConclusion (R : PlanarRegion) (S : BoundarySides R) : Prop :=
  (∃ s, IsInducedBoundaryOrientation R s) ∧
    ∀ s, IsInducedBoundaryOrientation R s → ∀ i,
      (HasSideOnLeft (S.boundedSide i) (R.curve i) (s i) ↔ i = S.outer) ∧
      (HasSideOnLeft (S.boundedSide i) (R.curve i) (-s i) ↔ i ≠ S.outer)

namespace Expected

/-- Identification of the distinguished compactified-plane model with S². -/
def compactificationSphere : Prop :=
  Nonempty (OnePoint Plane ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

def parameterCircleSphere : Prop :=
  Nonempty (ParameterCircle ≃ₜ Metric.sphere (0 : Plane) 1)

def basicProperties : Prop := ∀ R : PlanarRegion,
  IsCompact R.carrier ∧ IsConnected R.carrier ∧
    interior R.carrier = R.domain ∧ frontier R.carrier = R.boundary

/-- The elementary strict inequality needed for the graph/flow-box
construction, valid at reflex as well as convex noncuspidal joins. -/
def cornerTransverse : Prop := ∀ u v : Plane, ‖u‖ = 1 → ‖v‖ = 1 → u ≠ -v →
  0 < inner ℝ (u + v) u ∧ 0 < inner ℝ (u + v) v

def inwardPushEquivalence : Prop := ∀ K : Set Plane,
  Nonempty (InwardPush K) → InteriorInclusionEquivalence K

def collaredInteriorEquivalence : Prop := ∀ K B : Set Plane,
  IsClosed K → IsCompact B → B = frontier K →
    Nonempty (BoundaryCollar K B) → InteriorInclusionEquivalence K

/-- Embedding in the ordinary planar topology. -/
def curveEmbedding : Prop := ∀ c : RegularJordanCurve,
  Topology.IsEmbedding c.parametrization

def curveCompact : Prop := ∀ c : RegularJordanCurve, IsCompact c.trace

def traceNonempty : Prop := ∀ c : RegularJordanCurve, c.trace.Nonempty

def boundaryNonempty : Prop := ∀ R : PlanarRegion, R.boundary.Nonempty

def compactBoundary : Prop := ∀ R : PlanarRegion, IsCompact R.boundary

/-- A common strict normal for actual nonzero, nonopposite tangents. -/
def commonNormalDirection : Prop := ∀ u v : Plane, u ≠ 0 → v ≠ 0 →
  NormedSpace.normalize u ≠ -NormedSpace.normalize v →
  ∃ w : Plane, 0 < inner ℝ w (quarterTurn u) ∧ 0 < inner ℝ w (quarterTurn v)

/-- The common normal applies to the local extensions at each actual join. -/
def regularJoinNormal : Prop := ∀ (c : RegularJordanCurve) (t : ℝ),
  ∃ (δ : ℝ) (l r : ℝ → Plane) (w : Plane), 0 < δ ∧
    ContDiffOn ℝ ∞ l (Ioo (t - δ) (t + δ)) ∧
    ContDiffOn ℝ ∞ r (Ioo (t - δ) (t + δ)) ∧
    EqOn l (realLift c.parametrization) (Icc (t - δ) t) ∧
    EqOn r (realLift c.parametrization) (Icc t (t + δ)) ∧
    deriv l t ≠ 0 ∧ deriv r t ≠ 0 ∧
    0 < inner ℝ w (quarterTurn (deriv l t)) ∧
    0 < inner ℝ w (quarterTurn (deriv r t))

/-- The push is constructed from the collar, not assumed as region input. -/
def collarInwardPush : Prop := ∀ K B : Set Plane,
  IsClosed K → IsCompact B → B = frontier K →
  Nonempty (BoundaryCollar K B) → Nonempty (InwardPush K)

def regionInteriorEquivalenceOfCollar : Prop := ∀ R : PlanarRegion,
  Nonempty (BoundaryCollar R.carrier R.boundary) →
    InteriorInclusionEquivalence R.carrier

end Expected
end P202Specs.PlanarRegionTopology
