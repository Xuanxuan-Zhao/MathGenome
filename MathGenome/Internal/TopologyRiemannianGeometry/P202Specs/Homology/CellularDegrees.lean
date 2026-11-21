import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.CellularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SpheresDisks
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.Degree
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.GoodPairQuotient

/-! Interfaces for the attaching-coefficient conclusion of
`thm:p202-cellular-comparison`, paper.tex 1543–1557.

These statements use the genuine skeletal relative homology and its
connecting-map differential. Source and target orientations are specified
independently by geometric sphere charts; the chart compatibility conditions
use only the disk connecting and quotient maps, never the differential formula.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory HomologicalComplex Topology
open scoped Simplicial
universe u v w

namespace P202Specs.CellularDegrees
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains

variable (X : Type w) [TopologicalSpace X] [CWStructure X]
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- The disk class in the actual cellular chain group. -/
def cellClass (n : ℕ) (c : Cell X n)
    (a : relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)) :
    chainGroup X R M n :=
  (relativeHomologyFunctor R M (n : ℤ)).map (characteristicPairMap n c) a

/-- The attaching map, with the boundary universe lift retained. -/
def attachingBoundary (n : ℕ) (c : Cell X (n+1)) :
    (referenceDiskPair.{w} (n+1)).sub ⟶ skeletalSpace X (n+1) :=
  (characteristicPairMap (n+1) c).restrict ≫ lowerMap X (n+1)

/-- Compatibility identifies the cell summands through characteristic maps;
it is stronger than asking for an abstract module isomorphism. -/
def CharacteristicCoordinates (n : ℕ)
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M)) : Prop :=
  ∀ c m, e (cellClass X R M n c (g m)) = Finsupp.single c m

/-- Column of the actual differential, in any specified cell coordinates. -/
def boundaryColumn (n : ℕ)
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} (n+1))
      ((n+1 : ℕ) : ℤ))
    (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))
    (c : Cell X (n+1)) : M →ₗ[R] (Cell X n →₀ M) :=
  e.toLinearMap.comp ((differential X R M n).hom.comp
    (((relativeHomologyFunctor R M ((n+1 : ℕ) : ℤ)).map
      (characteristicPairMap (n+1) c)).hom.comp g.toLinearMap))

/-- A singular simplex with coefficient m, in the integer-indexed complex. -/
def simplexChainZ (Y : TopCat.{w}) (n : ℕ) (s : Simplex Y n) (m : M) :
    (ordinaryComplex R M Y).X (n : ℤ) :=
  (ordinaryNonnegativeIso R M Y n).inv (Finsupp.single s m)

/-- The singular vertex with value p. -/
def pointSimplex (Y : TopCat.{w}) (p : Y) : Simplex Y 0 :=
  (simplexEquiv Y 0).symm (ContinuousMap.const _ p)

/-- Projection of a simplex chain to the actual relative complex. -/
def relativeSimplexChain (P : Pair.{w}) (n : ℕ) (s : Simplex P.space n) (m : M) :
    (ordinary R M P).X (n : ℤ) :=
  (projection (ordinaryFunctor R M) P).f (n : ℤ) (simplexChainZ R M P.space n s m)

/-- Ordinary degree zero has no outgoing boundary. This supplies the cycle
proof in the canonical point class without adding a certificate hypothesis. -/
lemma ordinaryZeroBoundary (Y : TopCat.{w}) : (ordinaryComplex R M Y).d 0 (-1) = 0 := by
  apply HomologicalComplex.extend_d_from_eq_zero
    (complex R M Y) (degreeEmbedding 0) 0 (-1) 0 (by rfl)
  simp [ComplexShape.down_Rel]

/-- The positively weighted point class in a genuine relative group H₀(P). -/
def relativePointClass (P : Pair.{w}) (p : P.space) (m : M) :
    relativeHomology R M P 0 :=
  homologyMap (projection (ordinaryFunctor R M) P) 0
    (P202Specs.SpheresDisks.classOf R (ordinaryComplex R M P.space) 0
      (simplexChainZ R M P.space 0 (pointSimplex P.space p) m)
      (by change (ordinaryComplex R M P.space).d 0 (-1) _ = 0
          rw [ordinaryZeroBoundary]; rfl))

/-- An oriented closed interval is a boundary-preserving disk parametrized by
the simplex with ordered vertices 0,1. Reversing this parametrization reverses
the interval orientation. -/
structure IntervalParametrization where
  homeomorph : StandardSimplex 1 ≃ₜ Disk 1
  boundary : ∀ x, (∃ i, x.weights i = 0) ↔ ‖(homeomorph x).val‖ = 1

namespace IntervalParametrization

def referenceHomeomorph (h : IntervalParametrization) :
    P202Specs.SpheresDisks.simplex 1 ≃ₜ (referenceDiskPair.{w} 1).space :=
  h.homeomorph.trans (referenceDiskHomeomorph 1).symm

def boundaryHomeomorph (h : IntervalParametrization) :
    (P202Specs.SpheresDisks.simplexPair 1).sub ≃ₜ (referenceDiskPair.{w} 1).sub where
  toFun x := ⟨h.referenceHomeomorph.{w} x.val, (h.boundary x.val).mp x.property⟩
  invFun x := ⟨h.referenceHomeomorph.{w}.symm x.val,
    (h.boundary (h.homeomorph.symm x.val.down)).mpr (by
      have hx : ‖x.val.down.val‖ = 1 := x.property
      simpa only [Homeomorph.apply_symm_apply] using hx)⟩
  left_inv x := Subtype.ext (h.referenceHomeomorph.{w}.symm_apply_apply x.val)
  right_inv x := Subtype.ext (h.referenceHomeomorph.{w}.apply_symm_apply x.val)
  continuous_toFun := (h.referenceHomeomorph.{w}.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (h.referenceHomeomorph.{w}.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- The singular interval in the actual universe-lifted reference disk. -/
def simplex (h : IntervalParametrization) : Simplex (referenceDiskPair.{w} 1).space 1 :=
  (simplexEquiv _ 1).symm ⟨h.referenceHomeomorph, h.referenceHomeomorph.continuous⟩

/-- Face zero is the final endpoint; face one is the initial endpoint. -/
def endpoint (h : IntervalParametrization) (i : Fin 2) : (referenceDiskPair.{w} 1).sub :=
  h.boundaryHomeomorph (P202Specs.SpheresDisks.boundaryFace i (Convexity.StdSimplex.single 0))

end IntervalParametrization

namespace Expected

open Classical in
/-- The selected-cell collapse is an actual quotient map into D^n/∂D^n.
Its restrictions to every characteristic disk specify which cell survives.
An explicit boundary point is only used to name the collapsed basepoint;
such a point exists for every positive n. -/
def cellCollapse : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (n : ℕ) (c : Cell X n) (b : Sphere n),
    let P := P202Specs.SpheresDisks.diskPair n
    let Q := P202Specs.GoodPairQuotient.quotientSpace P
    let π := P202Specs.GoodPairQuotient.quotientProjection P
    ∃ q : C(skeletalSpace X (n+1), Q),
      IsQuotientMap q ∧
      (∀ x, q (oldSkeletonInclusion X n x) = π (boundaryInclusion n b)) ∧
      (∀ (d : Cell X n) (x : Disk n),
        q (diskToSkeleton X CWStructure.boundary_lands n d x) =
          if d = c then π x else π (boundaryInclusion n b)) ∧
      ∀ x : skeletalSpace X (n+1), x.val ∉ openCell X n c →
        q x = π (boundaryInclusion n b)

/-- Naturality sends the relative disk boundary to the attaching sphere
class before projecting to the next relative group. No generator is assumed. -/
def attachingNaturality : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (c : Cell X (n+1))
    (a : relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ)),
    differential X R M n (cellClass X R M (n+1) c a) =
      homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ)
        ((homologyFunctor R M (n : ℤ)).map (attachingBoundary X n c)
          (pairConnecting R M (referenceDiskPair.{w} (n+1)) n a))

/-- Cell coordinates, with this compatibility, are unique. -/
def coordinatesUnique : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ)
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e f : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M)),
    CharacteristicCoordinates X R M n g e →
    CharacteristicCoordinates X R M n g f → e = f

/-- Every cellular boundary has finite cell support, even when the CW
complex has infinitely many cells and unbounded dimension. -/
def boundaryFiniteSupport : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ)
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)),
    ∃ e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M),
      CharacteristicCoordinates X R M n g e ∧
      ∀ z : chainGroup X R M (n+1),
        ∃ F : Finset (Cell X n), ∀ c, c ∉ F → e (differential X R M n z) c = 0

/-- Signed endpoint incidence in the actual skeletal relative homology.
Coordinates send each positive point class to its vertex basis vector. Every
singular interval in X¹ with endpoints in X⁰ has the displayed boundary;
coincident endpoints are allowed. -/
def intervalBoundary : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    ∃ e : chainGroup X R M 0 ≃ₗ[R] (Cell X 0 →₀ M),
      (∀ (c : Cell X 0) (m : M),
        e (relativePointClass R M (skeletalPair X 0)
          (diskToSkeleton X CWStructure.boundary_lands 0 c ⟨0, by simp⟩) m) =
            Finsupp.single c m) ∧
      ∀ (s : Simplex (skeletalPair X 1).space 1) (a b : (skeletalPair X 1).sub),
        face 0 s = (TopCat.toSSet.map (skeletalPair X 1).inclusion).app
          (Opposite.op ⦋0⦌) (pointSimplex (skeletalPair X 1).sub a) →
        face 1 s = (TopCat.toSSet.map (skeletalPair X 1).inclusion).app
          (Opposite.op ⦋0⦌) (pointSimplex (skeletalPair X 1).sub b) →
        ∃ (vfinal vinitial : Cell X 0),
          lowerHomeomorph X 1 a =
            diskToSkeleton X CWStructure.boundary_lands 0 vfinal ⟨0, by simp⟩ ∧
          lowerHomeomorph X 1 b =
            diskToSkeleton X CWStructure.boundary_lands 0 vinitial ⟨0, by simp⟩ ∧
          ∃ hz : ∀ m : M, (ordinary R M (skeletalPair X 1)).d 1 0
              (relativeSimplexChain R M (skeletalPair X 1) 1 s m) = 0,
            ∀ m : M,
              e (differential X R M 0
                (P202Specs.SpheresDisks.classOf R (ordinary R M (skeletalPair X 1)) 1
                  (relativeSimplexChain R M (skeletalPair X 1) 1 s m) (hz m))) =
                Finsupp.single vfinal m - Finsupp.single vinitial m

/-- Oriented characteristic intervals are genuine relative generators, and their
cellular boundaries have the signed incidences of their two endpoints. -/
def intervalCellBoundary : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (h : IntervalParametrization),
    ∃ (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} 1) 1)
      (e : chainGroup X R M 0 ≃ₗ[R] (Cell X 0 →₀ M))
      (hz : ∀ m : M, (ordinary R M (referenceDiskPair.{w} 1)).d 1 0
        (relativeSimplexChain R M (referenceDiskPair.{w} 1) 1 h.simplex m) = 0),
      (∀ (c : Cell X 0) (m : M),
        e (relativePointClass R M (skeletalPair X 0)
          (diskToSkeleton X CWStructure.boundary_lands 0 c ⟨0, by simp⟩) m) =
            Finsupp.single c m) ∧
      (∀ m : M, g m = P202Specs.SpheresDisks.classOf R
        (ordinary R M (referenceDiskPair.{w} 1)) 1
        (relativeSimplexChain R M (referenceDiskPair.{w} 1) 1 h.simplex m) (hz m)) ∧
      ∀ c : Cell X 1, ∃ vfinal vinitial : Cell X 0,
        attachingBoundary X 0 c (h.endpoint 0) =
          diskToSkeleton X CWStructure.boundary_lands 0 vfinal ⟨0, by simp⟩ ∧
        attachingBoundary X 0 c (h.endpoint 1) =
          diskToSkeleton X CWStructure.boundary_lands 0 vinitial ⟨0, by simp⟩ ∧
        ∀ m : M, e (differential X R M 0 (cellClass X R M 1 c (g m))) =
          Finsupp.single vfinal m - Finsupp.single vinitial m

-- Add import P202Specs.Homology.Degree, upstream Specs only.
-- Place in namespace P202Specs.CellularDegrees.Expected.
def sphereCoefficientAction : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (f : P202Specs.SpheresDisks.sphere n ⟶ P202Specs.SpheresDisks.sphere n)
    (x : P202Specs.SingularChains.reducedHomology R M
      (P202Specs.SpheresDisks.sphere n) (n : ℤ)),
    (P202Specs.SingularChains.reducedHomologyFunctor R M (n : ℤ)).map f x =
      P202Specs.Degree.degree n f • x

/-- The cell quotient is the actual geometric sphere. -/
def diskQuotientSphere : Prop :=
  ∀ (n : ℕ) (b : Sphere n),
    Nonempty (P202Specs.GoodPairQuotient.quotientSpace
      (P202Specs.SpheresDisks.diskPair n) ≃ₜ P202Specs.SpheresDisks.sphere n)

end Expected
end P202Specs.CellularDegrees

namespace P202Specs.CellularDegrees
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202Specs.SpheresDisks P202Specs.GoodPairQuotient

abbrev liftedSphere (n : ℕ) : TopCat.{w} := TopCat.of (ULift.{w} (sphere n))

def chartAttachingMap (X : Type w) [TopologicalSpace X] [CWStructure X] (n : ℕ)
    (hS : (referenceDiskPair.{w} (n+1)).sub ≃ₜ liftedSphere.{w} n)
    (hT : quotientSpace (referenceDiskPair.{w} n) ≃ₜ liftedSphere.{w} n)
    (q : skeletalPair X n ⟶ quotientPair (referenceDiskPair.{w} n))
    (c : Cell X (n+1)) : sphere n ⟶ sphere n :=
  TopCat.ofHom ⟨fun x => (hT (q.map (attachingBoundary X n c (hS.symm (ULift.up x))))).down,
    continuous_uliftDown.comp (hT.continuous.comp (q.map.hom.continuous.comp
      ((attachingBoundary X n c).hom.continuous.comp
        (hS.symm.continuous.comp continuous_uliftUp))))⟩

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- The source disk orientation induces the specified sphere orientation
through the actual connecting map and the chosen boundary chart. -/
def SourceChartCoordinate (n : ℕ)
    (hS : (referenceDiskPair.{w} (n+1)).sub ≃ₜ liftedSphere.{w} n)
    (s : M ≃ₗ[R] homology R M (liftedSphere.{w} n) (n : ℤ))
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ)) : Prop :=
  ∀ m, (homologyFunctor R M (n : ℤ)).map (TopCat.isoOfHomeo hS).hom
    (pairConnecting R M (referenceDiskPair.{w} (n+1)) n (g m)) = s m

/-- The target disk orientation induces the same model sphere orientation
through the actual disk quotient and the independently chosen quotient chart. -/
def TargetChartCoordinate (n : ℕ)
    (hT : quotientSpace (referenceDiskPair.{w} n) ≃ₜ liftedSphere.{w} n)
    (s : M ≃ₗ[R] homology R M (liftedSphere.{w} n) (n : ℤ))
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)) : Prop :=
  ∀ m, (relativeHomologyFunctor R M (n : ℤ)).map (quotientPairMap (referenceDiskPair.{w} n)) (g m) =
    homologyMap (projection (ordinaryFunctor R M) (quotientPair (referenceDiskPair.{w} n))) (n : ℤ)
      ((homologyFunctor R M (n : ℤ)).map (TopCat.isoOfHomeo hT).inv (s m))

variable (X : Type w) [TopologicalSpace X] [CWStructure X]

def CellwiseCharacteristicCoordinates (n : ℕ)
    (g : ∀ c : Cell X n, M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M)) : Prop :=
  ∀ c m, e (cellClass X R M n c (g c m)) = Finsupp.single c m

open Classical in
def SelectedCellCollapse (n : ℕ) (d : Cell X n) (b : (referenceDiskPair.{w} n).sub)
    (q : skeletalPair X n ⟶ quotientPair (referenceDiskPair.{w} n)) : Prop :=
  IsQuotientMap q.map ∧
  (∀ (k : Cell X n) (x : (referenceDiskPair.{w} n).space),
    q.map ((characteristicPairMap n k).map x) =
      if k = d then quotientProjection (referenceDiskPair.{w} n) x
      else quotientProjection (referenceDiskPair.{w} n) b.val) ∧
  ∀ x : skeletalSpace X (n+1), x.val ∉ openCell X n d →
    q.map x = quotientProjection (referenceDiskPair.{w} n) b.val

namespace Expected

/-- The cellular coefficient formula for arbitrary independent source and
target orientation charts, including separate orientations on every cell.
The coefficient is the integral degree of the actual attaching-collapse map.
The finite support set works for every relative class of a source cell. -/
def geometricBoundaryFormula : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (hn : 0 < n) (b : (referenceDiskPair.{w} n).sub)
    (hS : ∀ c : Cell X (n+1), (referenceDiskPair.{w} (n+1)).sub ≃ₜ liftedSphere.{w} n)
    (hT : ∀ d : Cell X n, quotientSpace (referenceDiskPair.{w} n) ≃ₜ liftedSphere.{w} n)
    (s : M ≃ₗ[R] homology R M (liftedSphere.{w} n) (n : ℤ)),
    ∃ (gS : ∀ c : Cell X (n+1), M ≃ₗ[R]
        relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ))
      (gT : ∀ d : Cell X n, M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
      (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M)),
      (∀ c, SourceChartCoordinate R M n (hS c) s (gS c)) ∧
      (∀ d, TargetChartCoordinate R M n (hT d) s (gT d)) ∧
      CellwiseCharacteristicCoordinates R M X n gT e ∧
      (∀ d : Cell X n, ∃ q : skeletalPair X n ⟶ quotientPair (referenceDiskPair.{w} n),
        SelectedCellCollapse X n d b q ∧
        ∀ (c : Cell X (n+1)) (m : M),
          e (differential X R M n (cellClass X R M (n+1) c (gS c m))) d =
            P202Specs.Degree.degree n (chartAttachingMap X n (hS c) (hT d) q c) • m) ∧
      ∀ c : Cell X (n+1), ∃ F : Finset (Cell X n),
        ∀ (a : relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ))
          d, d ∉ F → e (differential X R M n (cellClass X R M (n+1) c a)) d = 0

/-- All orientation-chart inputs of the degree formula exist for every
positive target dimension and every coefficient module. -/
def chartDataExist : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (hn : 0 < n),
    Nonempty (referenceDiskPair.{w} n).sub ∧
    Nonempty ((referenceDiskPair.{w} (n+1)).sub ≃ₜ liftedSphere.{w} n) ∧
    Nonempty (quotientSpace (referenceDiskPair.{w} n) ≃ₜ liftedSphere.{w} n) ∧
    Nonempty (M ≃ₗ[R] homology R M (liftedSphere.{w} n) (n : ℤ))

end Expected
end P202Specs.CellularDegrees
