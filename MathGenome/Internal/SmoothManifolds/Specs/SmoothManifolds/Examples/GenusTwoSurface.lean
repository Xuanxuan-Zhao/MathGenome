import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.GenusTwoAtlas
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.GenusTwoOrientation

/-! Final construction contract for paper.tex 2385–2396. The quotient, disk,
bulk charts, and signed radial seam charts are the canonical upstream objects.
The propositions below require their topology, smooth structure, and intrinsic
orientation together, without assuming any cohomology calculation. -/

namespace Specs.SmoothManifolds.Examples.GenusTwoSurface
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.SphereTorusData
  _root_.SmoothManifolds.GenusTwoData Set

/-- The parent construction retains exactly the canonical upstream quotient. -/
def SurfaceType := Type
def SurfaceValue : SurfaceType := _root_.SmoothManifolds.GenusTwoData.Surface

/-- A coordinate disk in the standard torus has the claimed circle as frontier. -/
def diskGeometryType : Prop :=
  IsOpen removedDisk ∧
  boundaryCircle = quotientProjection 2 ''
    {x : Euclidean 2 | squareSum x = (1 / 8 : ℝ) ^ 2} ∧
  (∀ p, reflectTorus p ∈ removedDisk ↔ p ∈ removedDisk) ∧
  (∀ p, reflectTorus p ∈ boundaryCircle ↔ p ∈ boundaryCircle)

def quotientTopologyType : Prop :=
  Nonempty Surface ∧ CompactSpace Surface ∧ T2Space Surface ∧
    SecondCountableTopology Surface

/-- Exact fibers prohibit collapsing either bulk or identifying extra seam
points. This is a statement about the specified quotient, not an abstract
surface with chosen numerical invariants. -/
def exactFibersType : Prop :=
  (∀ x y : Pieces, projection x = projection y ↔ Glued x y) ∧
  (∀ side : Bool, Function.Injective (sideInclusion side))


/-- This specifies all chart realizations, the generating atlas and its maximal
extension. Orientation is in the upstream intrinsic determinant-ray sense.
Both bulks have their standard ordered angle orientation; a signed radial
chart ordered (angle, signed radius) has negative coordinate determinant on
both sides, so its negative coordinate wedge is positive. -/
def smoothConstructionType : Prop :=
  (∀ (side : Bool) (c : ModelChart 2 .euclidean (FlatTorus 2)),
    c ∈ angleAtlas 2 → ∃ e, IsInteriorChart side c e) ∧
  (∀ a δ ε : ℝ, 0 < δ → δ < 1 / 4 → 0 < ε → ε < 1 / 16 →
    ∃ e, IsSeamChart a δ ε e) ∧
  _root_.SmoothManifolds.AtlasData.IsContDiffAtlas (⊤ : ℕ∞) constructionAtlas ∧
  ∃ S : _root_.SmoothManifolds.AtlasData.SmoothManifold 2 .euclidean Surface,
    S.topologicalManifold.atlas = constructionAtlas ∧
    S.smoothStructure.val = _root_.SmoothManifolds.AtlasData.maximalExtension
      (⊤ : ℕ∞) constructionAtlas ∧
    _root_.SmoothManifolds.BoundaryData.intrinsicBoundary S = ∅ ∧
    ∃ o : _root_.SmoothManifolds.OrientationData.Orientation S,
      ∀ (K : _root_.SmoothManifolds.TangentBundleData.FiberCoordinates S)
        (e : ModelChart 2 .euclidean Surface) (he : e ∈ S.smoothStructure.val),
      (e ∈ bulkAtlas → ∀ p : e.source,
        _root_.SmoothManifolds.OrientationData.IsPositive (o.val p.val)
          (_root_.SmoothManifolds.OrientationData.coordinateVector K e he p)) ∧
      (e ∈ seamAtlas → ∀ p : e.source,
        _root_.SmoothManifolds.OrientationData.IsPositive (o.val p.val)
          (-_root_.SmoothManifolds.OrientationData.coordinateVector K e he p))

/-- A countable cover by the actual prescribed interior and collar charts. -/
def countableChartCoverType : Prop :=
  ∃ C : Set (ModelChart 2 .euclidean Surface), C.Countable ∧ C ⊆ constructionAtlas ∧
    ∀ p : Surface, ∃ c ∈ C, p ∈ c.source

def connectedType : Prop := ConnectedSpace Surface

/-- The complete original construction obligation. The separate theorem
propositions above organize it without changing its hypotheses or conclusion. -/
def fullConstructionType : Prop :=
  diskGeometryType ∧ exactFibersType ∧ quotientTopologyType ∧
    connectedType ∧ smoothConstructionType

end Specs.SmoothManifolds.Examples.GenusTwoSurface
