import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.GraphFundamentalGroup
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.BasicFundamentalGroups
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
Independent definitions and original proposition types for
paper.tex 676–689, 716–740.  The adjunction uses the actual Euclidean disk
and the quotient topology, with no separation condition on the old space.
The finite-CW statement records the actual oriented edge loops and the
two-cell attaching maps. The surface model is a disk with 4g boundary arcs
paired in the order aᵢ,bᵢ,aᵢ⁻¹,bᵢ⁻¹, with the quotient topology.
-/
noncomputable section
open Set Topology
open scoped unitInterval
universe u

namespace P202.Cellular

namespace DiskAttachment
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

/-- Only boundary points of the new disk are identified with the old space. -/
inductive Relation (a : C(Sphere n, X)) : X ⊕ Disk n → X ⊕ Disk n → Prop where
  | glue (z : Sphere n) : Relation a (.inl (a z)) (.inr (boundaryInclusion n z))

def setoid (a : C(Sphere n, X)) : Setoid (X ⊕ Disk n) :=
  Relation.EqvGen.setoid (Relation a)

/-- The topological adjunction `X ∪ₐ Dⁿ`. -/
def Space (a : C(Sphere n, X)) := Quotient (setoid a)

instance (a : C(Sphere n, X)) : TopologicalSpace (Space a) :=
  inferInstanceAs (TopologicalSpace (Quotient (setoid a)))

def quotientMap (a : C(Sphere n, X)) : X ⊕ Disk n → Space a := Quotient.mk _

def inclusion (a : C(Sphere n, X)) : C(X, Space a) :=
  ⟨fun x => quotientMap a (.inl x), continuous_quotient_mk'.comp continuous_inl⟩

def characteristic (a : C(Sphere n, X)) : C(Disk n, Space a) :=
  ⟨fun z => quotientMap a (.inr z), continuous_quotient_mk'.comp continuous_inr⟩

def pointedInclusion (a : C(Sphere n, X)) (x : X) :
    P202Specs.Topology.PointedMap X (Space a) x (inclusion a x) :=
  ⟨inclusion a, rfl⟩

def pointedAttachingMap (a : C(Sphere n, X)) (z : Sphere n) :
    P202Specs.Topology.PointedMap (Sphere n) X z (a z) := ⟨a, rfl⟩

/-- The image of the attaching sphere, transported along an arbitrary path
from the selected basepoint to the attaching basepoint. -/
def attachingHom (a : C(Sphere n, X)) (z : Sphere n) {x : X}
    (d : Path x (a z)) :
    P202Specs.Topology.Pi1 (Sphere n) z →* P202Specs.Topology.Pi1 X x :=
  (P202Specs.Topology.changeBasepoint d).toMonoidHom.comp
    (pointedAttachingMap a z).induced

end DiskAttachment

/-- Labels of the two oriented edges for each handle. -/
abbrev SurfaceGenerator (g : ℕ) := Fin g × Bool

/-- The ordered word `∏ᵢ aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹`. The product is a list product,
so its order does not presume that the free group is commutative. -/
def surfaceRelator (g : ℕ) : FreeGroup (SurfaceGenerator g) :=
  ((List.finRange g).map fun i =>
    FreeGroup.of (i, false) * FreeGroup.of (i, true) *
      (FreeGroup.of (i, false))⁻¹ * (FreeGroup.of (i, true))⁻¹).prod

abbrev SurfacePresentation (g : ℕ) := PresentedGroup ({surfaceRelator g} : Set _)

abbrev OneSkeleton (X : Type u) [TopologicalSpace X] [CWStructure X] := skeletonLT X 2

def vertexInOneSkeleton {X : Type u} [TopologicalSpace X] [CWStructure X]
    (v : GraphVertex X) : OneSkeleton X := oldSkeletonInclusion X 1 v

def edgeInOneSkeleton {X : Type u} [TopologicalSpace X] [CWStructure X]
    (e : Cell X 1) :
    Path (vertexInOneSkeleton ((graphEndpoints X).source e))
      (vertexInOneSkeleton ((graphEndpoints X).target e)) where
  toFun t := diskToSkeleton X CWStructure.boundary_lands 1 e (edgeDiskPoint t)
  continuous_toFun := (graphEdgePath e).continuous.subtype_mk _
  source' := Subtype.ext rfl
  target' := Subtype.ext rfl

/-- These are conclusion data, not additional hypotheses on a finite complex.
They include the graph computation of the actual one-skeleton. -/
structure OneSkeletonPresentation (X : Type u) [TopologicalSpace X] [CWStructure X]
    (x : X) where
  connected : ConnectedSpace (OneSkeleton X)
  tree : Set (Cell X 1)
  spanning : (graphEndpoints X).IsSpanningTree tree
  maximal : Maximal (graphEndpoints X).IsForest tree
  root : GraphVertex X
  basepath : Path x root.val
  paths : ∀ v : GraphVertex X, Path (vertexInOneSkeleton root) (vertexInOneSkeleton v)
  paths_in_tree : ∀ v t, (paths v t).val ∈ graphTreeCarrier tree
  freeEquiv : FreeGroup {e : Cell X 1 // e ∉ tree} ≃*
    P202Specs.Topology.Pi1 (OneSkeleton X) (vertexInOneSkeleton root)
  on_edge : ∀ e : {e : Cell X 1 // e ∉ tree},
    freeEquiv (FreeGroup.of e) = P202Specs.Topology.loopClass
      (((paths ((graphEndpoints X).source e.val)).trans (edgeInOneSkeleton e.val)).trans
        (paths ((graphEndpoints X).target e.val)).symm)
  sphereBasepoint : Sphere 2
  sphereEquiv : P202Specs.Topology.Pi1 (Sphere 2) sphereBasepoint ≃* Multiplicative ℤ
  cellPaths : ∀ c : Cell X 2,
    Path (vertexInOneSkeleton root) (attachingMap 2 c sphereBasepoint)

namespace OneSkeletonPresentation
variable {X : Type u} [TopologicalSpace X] [CWStructure X] {x : X}

def relator (D : OneSkeletonPresentation X x) (c : Cell X 2) :
    FreeGroup {e : Cell X 1 // e ∉ D.tree} :=
  D.freeEquiv.symm (P202Specs.Topology.changeBasepoint (D.cellPaths c)
    ((show P202Specs.Topology.PointedMap (Sphere 2) (OneSkeleton X)
      D.sphereBasepoint (attachingMap 2 c D.sphereBasepoint) from
        ⟨attachingMap 2 c, rfl⟩).induced (D.sphereEquiv.symm (Multiplicative.ofAdd 1))))

def ambientGenerator (D : OneSkeletonPresentation X x)
    (e : {e : Cell X 1 // e ∉ D.tree}) : P202Specs.Topology.Pi1 X x :=
  P202Specs.Topology.changeBasepoint D.basepath
    ((P202Specs.Topology.VanKampen.ambientMap (skeletonLT X 2) D.root.val
      (vertexInOneSkeleton D.root).property).induced (D.freeEquiv (FreeGroup.of e)))

end OneSkeletonPresentation

namespace SurfacePolygon

/-- The standard oriented parametrization of the Euclidean disk boundary. -/
def boundaryPoint (s : ℝ) : Disk 2 :=
  ⟨Complex.orthonormalBasisOneI.repr
    (P202Specs.Topology.BasicFundamentalGroups.circleCover s : ℂ), by
      rw [Metric.mem_closedBall, dist_zero_right,
        Complex.orthonormalBasisOneI.repr.norm_map]
      exact (Circle.norm_coe _).le⟩

def sidePoint (g : ℕ) (i : Fin g) (k : Fin 4) (t : unitInterval) : Disk 2 :=
  boundaryPoint ((4 * (i.val : ℝ) + (k.val : ℝ) + (t : ℝ)) / (4 * (g : ℝ)))

inductive SideRelation (g : ℕ) : Disk 2 → Disk 2 → Prop where
  | a (i : Fin g) (t : unitInterval) :
    SideRelation g (sidePoint g i 0 t) (sidePoint g i 2 (unitInterval.symm t))
  | b (i : Fin g) (t : unitInterval) :
    SideRelation g (sidePoint g i 1 t) (sidePoint g i 3 (unitInterval.symm t))

def setoid (g : ℕ) : Setoid (Disk 2) := Relation.EqvGen.setoid (SideRelation g)

/-- A disk whose marked boundary arcs are paired as an oriented 4g-gon.
This definition does not assume any group calculation or CW structure. -/
def Space (g : ℕ) := Quotient (setoid g)

instance (g : ℕ) : TopologicalSpace (Space g) :=
  inferInstanceAs (TopologicalSpace (Quotient (setoid g)))

def projection (g : ℕ) : C(Disk 2, Space g) :=
  ⟨Quotient.mk _, continuous_quotient_mk'⟩

def basepoint (g : ℕ) : Space g := projection g (boundaryPoint 0)

def sidePath (g : ℕ) (i : Fin g) (k : Fin 4) :
    Path (projection g (sidePoint g i k 0)) (projection g (sidePoint g i k 1)) where
  toFun t := projection g (sidePoint g i k t)
  continuous_toFun := (projection g).continuous.comp (by
    apply Continuous.subtype_mk
    apply Complex.orthonormalBasisOneI.repr.continuous.comp
    apply continuous_subtype_val.comp
    apply P202Specs.Topology.BasicFundamentalGroups.circleCover.continuous.comp
    fun_prop)
  source' := rfl
  target' := rfl

end SurfacePolygon

end P202.Cellular

namespace P202Specs.Topology.AttachedCellPresentations
open P202.Cellular

/-- The general quotient statement for one disk in every dimension at least
two, preserving the actual map induced by inclusion and all basepoint paths. -/
def attachedDiskQuotient : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (n : ℕ), 2 ≤ n → ∀ (a : C(Sphere n, X)) (z : Sphere n)
    (x : X) (d : Path x (a z)),
    ∃ e : Pi1 X x ⧸ Subgroup.normalClosure (Set.range (DiskAttachment.attachingHom a z d)) ≃*
      Pi1 (DiskAttachment.Space a) (DiskAttachment.inclusion a x),
      ∀ b : Pi1 X x, e (QuotientGroup.mk b) =
        (DiskAttachment.pointedInclusion a x).induced b

/-- For a two-cell the kernel is normally generated by its attaching loop.
An integer equivalence chooses either orientation on the actual circle;
the existence of that equivalence is part of the conclusion. -/
def attachedTwoCell : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (a : C(Sphere 2, X)) (z : Sphere 2),
    ∃ η : Pi1 (Sphere 2) z ≃* Multiplicative ℤ,
      ∀ (x : X) (d : Path x (a z)),
      ∃ e : Pi1 X x ⧸ Subgroup.normalClosure
        ({DiskAttachment.attachingHom a z d (η.symm (Multiplicative.ofAdd 1))} : Set _) ≃*
        Pi1 (DiskAttachment.Space a) (DiskAttachment.inclusion a x),
        ∀ b : Pi1 X x, e (QuotientGroup.mk b) =
          (DiskAttachment.pointedInclusion a x).induced b

/-- The induced map itself, rather than an unspecified abstract equivalence,
is an isomorphism for every cell dimension at least three. -/
def attachedHigherCell : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (n : ℕ), 3 ≤ n → ∀ (a : C(Sphere n, X)) (x : X),
    ∃ e : Pi1 X x ≃* Pi1 (DiskAttachment.Space a) (DiskAttachment.inclusion a x),
      ∀ b, e b = (DiskAttachment.pointedInclusion a x).induced b

/-- Finite means finitely many cells in total. Every two-cell gives its actual
attaching relator in the free group of the actual one-skeleton. -/
def finiteCWPresentation : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X]
    [Finite (Σ n, Cell X n)], ConnectedSpace X → ∀ x : X,
    ∃ D : OneSkeletonPresentation X x,
      ∃ e : PresentedGroup (Set.range D.relator) ≃* Pi1 X x,
        ∀ j, e (PresentedGroup.of j) = D.ambientGenerator j

/-- The geometric polygon example for every positive genus, including the
identification of all vertices and the original oriented aᵢ,bᵢ loops. -/
def surfacePolygonPresentation : Prop :=
  ∀ g : ℕ, 1 ≤ g →
    ∃ hvertices : ∀ (i : Fin g) (k : Fin 4) (t : unitInterval),
      t = 0 ∨ t = 1 →
        SurfacePolygon.projection g (SurfacePolygon.sidePoint g i k t) =
          SurfacePolygon.basepoint g,
    ∃ e : SurfacePresentation g ≃*
        Pi1 (SurfacePolygon.Space g) (SurfacePolygon.basepoint g),
      ∀ i : Fin g,
        e (PresentedGroup.of (i, false)) = loopClass
          ((SurfacePolygon.sidePath g i 0).cast
            (hvertices i 0 0 (Or.inl rfl)).symm
            (hvertices i 0 1 (Or.inr rfl)).symm) ∧
        e (PresentedGroup.of (i, true)) = loopClass
          ((SurfacePolygon.sidePath g i 1).cast
            (hvertices i 1 0 (Or.inl rfl)).symm
            (hvertices i 1 1 (Or.inr rfl)).symm)

def torusPolygonGroup : Prop :=
  Nonempty (Pi1 (SurfacePolygon.Space 1) (SurfacePolygon.basepoint 1) ≃*
    Multiplicative (ℤ × ℤ))

/-- Only the algebraic calculation needed in Example 2.6; a separate geometric
bridge to the genus-one polygon remains required. -/
def torusPresentationAlgebra : Prop :=
  ∃ e : SurfacePresentation 1 ≃* Multiplicative (ℤ × ℤ),
    e (PresentedGroup.of (0, false)) = Multiplicative.ofAdd (1, 0) ∧
    e (PresentedGroup.of (0, true)) = Multiplicative.ofAdd (0, 1)

end P202Specs.Topology.AttachedCellPresentations
