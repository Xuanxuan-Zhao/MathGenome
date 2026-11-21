import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.SpheresAndTori
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import Mathlib.Topology.Compactness.Compact

/-! Concrete connected-sum data for paper.tex 2385--2396. The torus is the
already shared angle-coordinate presentation R²/Z². The removed disk has
Euclidean radius 1/8 in the angle chart around zero. Only the two boundary
circles are identified; the two interiors remain distinct. This file does not
assume a smooth structure or any topological property of the quotient. -/
namespace SmoothManifolds.GenusTwoData
open ModelData SphereTorusData Set
open scoped BigOperators

/-- Reflection of one coordinate, restricting on the circle to angular
reflection. The second coordinate is retained. -/
def reflectCoordinates (x : Euclidean 2) : Euclidean 2 :=
  fun j => if j = 0 then -(x j) else x j

def reflectTorus (p : FlatTorus 2) : FlatTorus 2 :=
  fun j => if j = 0 then -(p j) else p j

@[simp] theorem reflectTorus_involutive (p : FlatTorus 2) :
    reflectTorus (reflectTorus p) = p := by
  funext j
  by_cases h : j = 0 <;> simp [reflectTorus, h]

/-- The image of an actual open coordinate disk, not a formal puncture. -/
def removedDisk : Set (FlatTorus 2) :=
  quotientProjection 2 '' {x : Euclidean 2 | squareSum x < (1 / 8 : ℝ) ^ 2}

/-- Both copies carry the inherited compact-surface-with-boundary topology. -/
abbrev PuncturedTorus := ↥(removedDiskᶜ)

/-- The frontier in the ambient torus, before choosing an intrinsic boundary
structure on the punctured surface. The equality with the coordinate circle
is a proof obligation below. -/
def boundaryCircle : Set (FlatTorus 2) := frontier removedDisk

/-- Boolean labels distinguish the two copies in their disjoint union. -/
abbrev Pieces := Bool × PuncturedTorus

/-- Equivalence classes have one point off the seam and precisely one point
from each copy on the seam, paired by the specified angular reflection. -/
def Glued (x y : Pieces) : Prop :=
  x = y ∨ (x.1 ≠ y.1 ∧ x.2.val ∈ boundaryCircle ∧
    y.2.val ∈ boundaryCircle ∧ y.2.val = reflectTorus x.2.val)

def gluingSetoid : Setoid Pieces where
  r := Glued
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | ⟨hb, hx, hy, he⟩
      · exact Or.inl h.symm
      · refine Or.inr ⟨Ne.symm hb, hy, hx, ?_⟩
        rw [he, reflectTorus_involutive]
    trans := by
      intro x y z hxy hyz
      rcases hxy with rfl | ⟨hxy, hx, hy, hey⟩
      · exact hyz
      rcases hyz with rfl | ⟨hyz, _, hz, hez⟩
      · exact Or.inr ⟨hxy, hx, hy, hey⟩
      apply Or.inl
      have hb : x.1 = z.1 := by
        cases hx : x.1 <;> cases hy : y.1 <;> cases hz : z.1 <;> simp_all
      have hp : z.2.val = x.2.val := by
        rw [hez, hey, reflectTorus_involutive]
      exact Prod.ext hb (Subtype.ext hp.symm) }

/-- The literal quotient of two standard tori with open disks removed. -/
abbrev Surface := Quotient gluingSetoid

def projection : Pieces → Surface := Quotient.mk gluingSetoid

def sideInclusion (side : Bool) (p : PuncturedTorus) : Surface := projection (side, p)

/-- Interior charts are precisely the standard torus angle charts restricted
to one bulk, transported through the corresponding quotient inclusion. -/
def IsInteriorChart (side : Bool) (c : ModelChart 2 .euclidean (FlatTorus 2))
    (e : ModelChart 2 .euclidean Surface) : Prop :=
  e.source = sideInclusion side ''
    {p : PuncturedTorus | p.val ∈ c.source ∧ p.val ∉ boundaryCircle} ∧
  e.target = {y | y ∈ c.target ∧ c.symm y ∉ removedDisk ∧ c.symm y ∉ boundaryCircle} ∧
  (∀ p : PuncturedTorus, p.val ∈ c.source → p.val ∉ boundaryCircle →
    e (sideInclusion side p) = c p.val) ∧
  (∀ y ∈ e.target, ∃ p : PuncturedTorus,
    p.val = c.symm y ∧ e.symm y = sideInclusion side p)

def bulkAtlas : Set (ModelChart 2 .euclidean Surface) :=
  {e | ∃ side c, c ∈ angleAtlas 2 ∧ IsInteriorChart side c e}

/-- Signed radial coordinates use radius 1/8+|t|. On the negative side the
angular reflection is applied before projecting to the second torus. At zero
the two one-sided formulas represent the same seam point in the quotient. -/
noncomputable def radialCoordinates (s t : ℝ) : Euclidean 2 :=
  fun j => (1 / 8 + |t|) * (anglePoint s).val j

noncomputable def signedRadialTorus (s t : ℝ) : FlatTorus 2 :=
  quotientProjection 2 (if t < 0 then reflectCoordinates (radialCoordinates s t)
    else radialCoordinates s t)

noncomputable def SeamRepresents (s t : ℝ) (z : Surface) : Prop :=
  ∃ p : PuncturedTorus, p.val = signedRadialTorus s t ∧
    z = sideInclusion (decide (t < 0)) p

def seamRectangle (a δ ε : ℝ) : Set (ModelSpace 2 .euclidean) :=
  {y | |y.val 0 - a| < δ ∧ |y.val 1| < ε}

/-- A true open partial homeomorphism with the specified entire inverse,
rather than an assumed smooth gluing certificate. -/
def IsSeamChart (a δ ε : ℝ) (e : ModelChart 2 .euclidean Surface) : Prop :=
  e.source = {z | ∃ y ∈ seamRectangle a δ ε,
    SeamRepresents (y.val 0) (y.val 1) z} ∧
  e.target = seamRectangle a δ ε ∧
  ∀ y ∈ e.target, SeamRepresents (y.val 0) (y.val 1) (e.symm y)

def seamAtlas : Set (ModelChart 2 .euclidean Surface) :=
  {e | ∃ a δ ε, 0 < δ ∧ δ < 1 / 4 ∧ 0 < ε ∧ ε < 1 / 16 ∧ IsSeamChart a δ ε e}

def constructionAtlas : Set (ModelChart 2 .euclidean Surface) := bulkAtlas ∪ seamAtlas

end SmoothManifolds.GenusTwoData

namespace Specs.SmoothManifolds.Examples.GenusTwoAtlas
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.SphereTorusData
  _root_.SmoothManifolds.GenusTwoData Set

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


/-- Full atlas construction on the literal quotient, with the given topology. -/
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
    _root_.SmoothManifolds.BoundaryData.intrinsicBoundary S = ∅

def countableChartCoverType : Prop :=
  ∃ C : Set (ModelChart 2 .euclidean Surface), C.Countable ∧ C ⊆ constructionAtlas ∧
    ∀ p : Surface, ∃ c ∈ C, p ∈ c.source

def connectedType : Prop := ConnectedSpace Surface

/-- The complete original construction obligation. The separate theorem
propositions above organize it without changing its hypotheses or conclusion. -/
def fullConstructionType : Prop :=
  diskGeometryType ∧ exactFibersType ∧ quotientTopologyType ∧
    connectedType ∧ smoothConstructionType

def SurfaceType := Type
def SurfaceValue : SurfaceType := Surface

end Specs.SmoothManifolds.Examples.GenusTwoAtlas
