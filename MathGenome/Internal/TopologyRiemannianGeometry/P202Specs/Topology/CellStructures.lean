import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import MathGenome.PointSetTopology.Topics.D10Topology.Ch03

/-!
Canonical point-set objects for paper.tex, Definition 2.1 and lines 570–588.
Disks have their Euclidean topology. Neither local finiteness nor a bound on
the dimensions or the number of cells is imposed. The attachment condition
below is a condition on the actual subspace skeleta, not on separately chosen
topologies. The realization constructions below do not assume any CW structure.
-/

noncomputable section
open Set Topology
universe u v w

namespace P202.Cellular

abbrev Disk (n : ℕ) := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
abbrev OpenDisk (n : ℕ) := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1
abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
abbrev Interval := unitInterval

def interiorInclusion (n : ℕ) : OpenDisk n → Disk n :=
  fun x => ⟨x.1, Metric.ball_subset_closedBall x.2⟩

def boundaryInclusion (n : ℕ) : Sphere n → Disk n :=
  fun x => ⟨x.1, Metric.sphere_subset_closedBall x.2⟩

/-- Parametrized cells, before imposing the CW axioms. -/
class CellStructure (X : Type u) [TopologicalSpace X] where
  Cell : ℕ → Type u
  characteristic : ∀ n, Cell n → C(Disk n, X)

variable (X : Type u) [TopologicalSpace X] [CellStructure X]

abbrev Cell := CellStructure.Cell X
abbrev characteristic (n : ℕ) (c : Cell X n) := CellStructure.characteristic n c

def interiorMap (n : ℕ) (c : Cell X n) : OpenDisk n → X :=
  characteristic X n c ∘ interiorInclusion n

def boundaryMap (n : ℕ) (c : Cell X n) : Sphere n → X :=
  characteristic X n c ∘ boundaryInclusion n

def openCell (n : ℕ) (c : Cell X n) : Set X := range (interiorMap X n c)
def closedCell (n : ℕ) (c : Cell X n) : Set X := range (characteristic X n c)

/-- The cells of dimension strictly less than `n`; the case `n = 0` is empty. -/
def skeletonLT (n : ℕ) : Set X := ⋃ (m : ℕ) (_ : m < n) (c : Cell X m), openCell X m c

/-- Integer indexing includes the source convention `X⁻¹ = ∅`. -/
def skeleton (n : ℤ) : Set X :=
  ⋃ (m : ℕ) (_ : (m : ℤ) ≤ n) (c : Cell X m), openCell X m c

abbrev DiskSum := Σ n, Σ _ : Cell X n, Disk n

def diskProjection : DiskSum X → X :=
  fun p => characteristic X p.1 p.2.1 p.2.2

/-- The old skeleton embeds into the next as a subspace. -/
def oldSkeletonInclusion (n : ℕ) : skeletonLT X n → skeletonLT X (n + 1) :=
  fun x => ⟨x.1, by
    rcases mem_iUnion.mp x.2 with ⟨m, hm⟩
    rcases mem_iUnion.mp hm with ⟨hmn, hm⟩
    exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨Nat.lt_succ_of_lt hmn, hm⟩⟩⟩

/-- A whole characteristic disk lands in the next skeleton if its boundary
lands in the old one. This includes the zero-dimensional disk. -/
def diskToSkeleton
    (hb : ∀ n (c : Cell X n), MapsTo (boundaryMap X n c) univ (skeletonLT X n))
    (n : ℕ) (c : Cell X n) : Disk n → skeletonLT X (n + 1) :=
  fun x => ⟨characteristic X n c x, by
    have hx : ‖x.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.2
    rcases lt_or_eq_of_le hx with h | h
    · exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨Nat.lt_succ_self n,
        mem_iUnion.mpr ⟨c, ⟨⟨x.1, by simpa only [Metric.mem_ball, dist_zero_right] using h⟩,
          rfl⟩⟩⟩⟩
    · have hs : x.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using h
      exact (oldSkeletonInclusion X n ⟨_, hb n c (mem_univ ⟨x.1, hs⟩)⟩).2⟩

/-- The projection from the old skeleton and the disjoint union of new disks. -/
def attachmentProjection
    (hb : ∀ n (c : Cell X n), MapsTo (boundaryMap X n c) univ (skeletonLT X n))
    (n : ℕ) : (skeletonLT X n ⊕ (Σ _ : Cell X n, Disk n)) → skeletonLT X (n + 1) :=
  Sum.elim (oldSkeletonInclusion X n) (fun p => diskToSkeleton X hb n p.1 p.2)

/-- The source's Hausdorff CW structure. The final field expresses the
attachment topology using the actual skeleton subspaces. Together with the
disjoint interior embeddings and the boundary condition, its projection is
the attaching pushout projection. No injectivity on boundaries is imposed. -/
class CWStructure (X : Type u) [TopologicalSpace X] extends CellStructure X where
  hausdorff : T2Space X
  interior_embedding : ∀ n (c : P202.Cellular.Cell X n), IsEmbedding (interiorMap X n c)
  disjoint_interiors : (univ : Set (Σ n, P202.Cellular.Cell X n)).PairwiseDisjoint
    (fun c => openCell X c.1 c.2)
  cover : ⋃ (n : ℕ) (c : P202.Cellular.Cell X n), openCell X n c = univ
  boundary_lands : ∀ n (c : P202.Cellular.Cell X n), MapsTo (boundaryMap X n c) univ (skeletonLT X n)
  closure_finite : ∀ n (c : P202.Cellular.Cell X n), ∃ F : Finset (Σ m, P202.Cellular.Cell X m),
    closedCell X n c ⊆ ⋃ d ∈ F, openCell X d.1 d.2
  weak_topology : ∀ A : Set X, IsClosed A ↔
    ∀ n (c : P202.Cellular.Cell X n), IsClosed (P202.Cellular.characteristic X n c ⁻¹' A)
  attachment_quotient : ∀ n, IsQuotientMap (attachmentProjection X boundary_lands n)

attribute [instance] CWStructure.hausdorff

def attachingMap {X : Type u} [TopologicalSpace X] [CWStructure X]
    (n : ℕ) (c : Cell X n) : C(Sphere n, skeletonLT X n) where
  toFun x := ⟨boundaryMap X n c x, CWStructure.boundary_lands n c (mem_univ x)⟩
  continuous_toFun := ((characteristic X n c).continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _

def cellHomeomorph {X : Type u} [TopologicalSpace X] [CWStructure X]
    (n : ℕ) (c : Cell X n) : OpenDisk n ≃ₜ openCell X n c :=
  (CWStructure.interior_embedding n c).toHomeomorph

/-- A cell selection containing the closures of all its selected cells.
Closedness is deliberately not an assumption. -/
structure Subcomplex (X : Type u) [TopologicalSpace X] [CWStructure X] where
  cells : ∀ n, Set (Cell X n)
  contains_closures : ∀ n (c : Cell X n), c ∈ cells n →
    closure (openCell X n c) ⊆ ⋃ (m : ℕ) (d : cells m), openCell X m d.1

def Subcomplex.carrier {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) : Set X :=
  ⋃ (n : ℕ) (c : A.cells n), openCell X n c.1

instance {X : Type u} [TopologicalSpace X] [CWStructure X] :
    CoeSort (Subcomplex X) (Type u) := ⟨fun A => A.carrier⟩

/-- No requirement that all vertices of the ambient type occur in a simplex. -/
structure AbstractSimplicialComplex (V : Type u) where
  simplices : Set (Finset V)
  nonempty : ∀ s ∈ simplices, s.Nonempty
  face : ∀ {s t}, s ∈ simplices → t ⊆ s → t.Nonempty → t ∈ simplices

namespace AbstractSimplicialComplex

variable {V : Type u} (K : AbstractSimplicialComplex V)

abbrev Simplex := {s : Finset V // s ∈ K.simplices}

/-- Finite nonnegative barycentric coordinates, with total weight one. -/
def Realization := {p : Convexity.StdSimplex ℝ V // p.weights.support ∈ K.simplices}

/-- The closed simplex with a given finite vertex set. On a finite vertex set,
the library topology is induced by all barycentric coordinate functions. -/
abbrev GeometricSimplex (s : Simplex K) := Convexity.StdSimplex ℝ s.1

def simplexChart (s : Simplex K) : GeometricSimplex K s → Realization K := by
  classical
  exact fun t => ⟨t.map (Subtype.val : s.1 → V), by
    apply K.face s.2 _ (Convexity.StdSimplex.support_weights_nonempty _)
    intro v hv
    have hv' := Finsupp.mapDomain_support hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv'
    exact a.2⟩

/-- The weak realization topology; it is not defined as an infinite product
subspace topology. -/
instance realizationTopology : TopologicalSpace (Realization K) :=
  ⨆ s : Simplex K, TopologicalSpace.coinduced (simplexChart K s) inferInstance

def simplexInterior (s : Simplex K) : Set (GeometricSimplex K s) :=
  {t | ∀ v, 0 < t.weights v}

end AbstractSimplicialComplex

/-- Ordered geometric simplices. The chosen topology is the usual finite
barycentric coordinate topology (see `finiteSimplexTopology` below). -/
abbrev StandardSimplex (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n + 1))

def standardSimplexInterior (n : ℕ) : Set (StandardSimplex n) :=
  {t | ∀ v, 0 < t.weights v}

/-- An order-preserving affine face map extends barycentric weights by zero. -/
def orderedAffineFace {m n : ℕ} (a : Fin (m + 1) ↪o Fin (n + 1)) :
    StandardSimplex m → StandardSimplex n := Convexity.StdSimplex.map a

/-- A Delta-complex has separate simplex labels and coherent ordered face
operators. Neither the face operators nor their induced vertex maps need be
injective on the labels. Thus two faces of one simplex can have the same image. -/
structure DeltaComplex where
  Simplex : ℕ → Type u
  face : ∀ {m n}, (Fin (m + 1) ↪o Fin (n + 1)) → Simplex n → Simplex m
  face_id : ∀ n (c : Simplex n), face (OrderEmbedding.id _) c = c
  face_comp : ∀ {k m n} (a : Fin (k + 1) ↪o Fin (m + 1))
    (b : Fin (m + 1) ↪o Fin (n + 1)) (c : Simplex n),
    face a (face b c) = face (a.comp b) c

namespace DeltaComplex

variable (D : DeltaComplex.{u})

abbrev SimplexSum := Σ n, Σ _ : D.Simplex n, StandardSimplex n

inductive FaceRelation : SimplexSum D → SimplexSum D → Prop where
  | face {m n} (a : Fin (m + 1) ↪o Fin (n + 1)) (c : D.Simplex n)
      (t : StandardSimplex m) :
      FaceRelation ⟨m, D.face a c, t⟩ ⟨n, c, orderedAffineFace a t⟩

def faceSetoid : Setoid (SimplexSum D) := Relation.EqvGen.setoid (FaceRelation D)

/-- Gluing all ordered faces, with the quotient (weak) topology. -/
def Realization := Quotient (faceSetoid D)

instance realizationTopology : TopologicalSpace (Realization D) :=
  inferInstanceAs (TopologicalSpace (Quotient (faceSetoid D)))

def simplexChart (n : ℕ) (c : D.Simplex n) : StandardSimplex n → Realization D :=
  fun t => Quotient.mk (faceSetoid D) ⟨n, c, t⟩

end DeltaComplex

end P202.Cellular

namespace P202Specs.Topology.CellStructures
open P202.Cellular

def quotientAdapter : Prop :=
  ∀ {P : Type u} {Q : Type v} [TopologicalSpace P] [TopologicalSpace Q] (q : P → Q),
    D10Topology.Ch03.QuotientMap q ↔ IsQuotientMap q

def quotientProductInterval : Prop :=
  ∀ {P : Type u} {Q : Type v} [TopologicalSpace P] [TopologicalSpace Q] (q : P → Q),
    IsQuotientMap q → IsQuotientMap (Prod.map q (id : Interval → Interval))

def characteristicProjectionQuotient : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X], IsQuotientMap (diskProjection X)

def continuityTest : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [CWStructure X]
    (f : X → Y), Continuous f ↔ ∀ n (c : Cell X n), Continuous (f ∘ characteristic X n c)

def homotopyContinuityTest : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [CWStructure X]
    (H : X × Interval → Y), Continuous H ↔
    ∀ n (c : Cell X n), Continuous (H ∘ Prod.map (characteristic X n c) id)

def characteristicDescent : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [CWStructure X]
    (f : DiskSum X → Y), Continuous f →
    (∀ p p', diskProjection X p = diskProjection X p' → f p = f p') →
    ∃! g : X → Y, Continuous g ∧ g ∘ diskProjection X = f

def negativeSkeleton : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CellStructure X], skeleton X (-1) = ∅

def skeletonIndexing : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CellStructure X] (n : ℕ),
    skeleton X (n : ℤ) = skeletonLT X (n + 1)

def closureOpenCell : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X] (n : ℕ) (c : Cell X n),
    closure (openCell X n c) = closedCell X n c

def attachmentPushout : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [CWStructure X]
    (n : ℕ) (f : C(skeletonLT X n, Y)) (g : ∀ _c : Cell X n, C(Disk n, Y)),
    (∀ c z, g c (boundaryInclusion n z) = f (attachingMap n c z)) →
    ∃! h : C(skeletonLT X (n + 1), Y),
      (∀ x, h (oldSkeletonInclusion X n x) = f x) ∧
      (∀ c x, h (diskToSkeleton X CWStructure.boundary_lands n c x) = g c x)

/-- Whitehead's diskwise conditions imply the successive-attachment CW
structure, retaining the given characteristic maps and cell labels. -/
def weakCWConstructor : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [S : CellStructure X],
    (∀ n (c : Cell X n), IsEmbedding (interiorMap X n c)) →
    (univ : Set (Σ n, Cell X n)).PairwiseDisjoint (fun c => openCell X c.1 c.2) →
    (⋃ (n : ℕ) (c : Cell X n), openCell X n c = univ) →
    (∀ n (c : Cell X n), MapsTo (boundaryMap X n c) univ (skeletonLT X n)) →
    (∀ n (c : Cell X n), ∃ F : Finset (Σ m, Cell X m),
      closedCell X n c ⊆ ⋃ d ∈ F, openCell X d.1 d.2) →
    (∀ A : Set X, IsClosed A ↔
      ∀ n (c : Cell X n), IsClosed (characteristic X n c ⁻¹' A)) →
    ∃ C : CWStructure X, C.toCellStructure = S

/-- On finite types this is precisely the usual barycentric coordinate topology. -/
def finiteSimplexTopology : Prop :=
  ∀ (V : Type u) [Finite V], IsEmbedding
    (fun t : Convexity.StdSimplex ℝ V => (t.weights : V → ℝ))

/-- Euclidean disks parametrize the ordered closed simplices, with the open
ball corresponding exactly to the positive barycentric stratum. -/
def diskSimplexParametrization : Prop :=
  ∀ n : ℕ, ∃ e : Disk n ≃ₜ StandardSimplex n,
    ∀ x : Disk n, e x ∈ standardSimplexInterior n ↔ ‖x.1‖ < 1

def simplicialWeakTopology : Prop :=
  ∀ {V : Type u} (K : AbstractSimplicialComplex V) (A : Set K.Realization),
    IsOpen A ↔ ∀ s : K.Simplex, IsOpen (K.simplexChart s ⁻¹' A)

def simplicialHausdorff : Prop :=
  ∀ {V : Type u} (K : AbstractSimplicialComplex V), T2Space K.Realization

def simplicialChartEmbedding : Prop :=
  ∀ {V : Type u} (K : AbstractSimplicialComplex V) (s : K.Simplex),
    IsEmbedding (K.simplexChart s)

def deltaFaceCompatibility : Prop :=
  ∀ (D : DeltaComplex.{u}) {m n} (a : Fin (m + 1) ↪o Fin (n + 1))
    (c : D.Simplex n) (t : StandardSimplex m),
    D.simplexChart m (D.face a c) t = D.simplexChart n c (orderedAffineFace a t)

def deltaProjectionQuotient : Prop :=
  ∀ D : DeltaComplex.{u}, IsQuotientMap (Quotient.mk (D.faceSetoid))

/-- Ordered face gluing preserves each labelled simplex interior exactly. -/
def deltaInteriorPartition : Prop :=
  ∀ (D : DeltaComplex.{u}) (x : D.Realization), ∃! r : D.SimplexSum,
    r.2.2 ∈ standardSimplexInterior r.1 ∧ D.simplexChart r.1 r.2.1 r.2.2 = x

def deltaHausdorff : Prop :=
  ∀ D : DeltaComplex.{u}, T2Space D.Realization

/-- All simplex labels, including repeated face images, remain distinct cell
indices. The characteristic disks are parametrizations of the closed simplices. -/
def deltaRealizationCW : Prop :=
  ∀ D : DeltaComplex.{u}, ∃ (C : CWStructure D.Realization)
    (indices : ∀ n, C.toCellStructure.Cell n ≃ D.Simplex n),
    letI : CWStructure D.Realization := C
    ∀ n (c : Cell D.Realization n),
      openCell D.Realization n c =
        D.simplexChart n (indices n c) '' standardSimplexInterior n ∧
      ∃ e : Disk n ≃ₜ StandardSimplex n,
        (characteristic D.Realization n c : Disk n → D.Realization) =
          D.simplexChart n (indices n c) ∘ e

def simplicialRealizationCW : Prop :=
  ∀ {V : Type u} (K : AbstractSimplicialComplex V),
    ∃ (C : CWStructure K.Realization)
      (indices : ∀ n, C.toCellStructure.Cell n ≃ {s : K.Simplex // s.1.card = n + 1}),
      letI : CWStructure K.Realization := C
      ∀ n (c : Cell K.Realization n),
        let s := (indices n c).1
        openCell K.Realization n c = K.simplexChart s '' K.simplexInterior s ∧
        ∃ e : Disk n ≃ₜ K.GeometricSimplex s,
          (characteristic K.Realization n c : Disk n → K.Realization) =
            K.simplexChart s ∘ e

end P202Specs.Topology.CellStructures
