import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellStructures
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.RelativeSingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularDegreeZero
import Mathlib.Topology.Homotopy.Contractible

/-!
Independent statements for paper.tex 1471–1495 and 1588–1593.
The geometric sphere of dimension n is the unit sphere in R^(n+1).
The boundary of the zero-dimensional disk is empty. Coefficients are arbitrary
modules, and reduced homology is the shared integer-indexed augmented theory.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v w
namespace P202Specs.SpheresDisks
open P202Specs.SingularChains P202Specs.RelativeSingularChains

abbrev sphere (n : ℕ) : TopCat := TopCat.of (P202.Cellular.Sphere (n+1))
abbrev disk (n : ℕ) : TopCat := TopCat.of (P202.Cellular.Disk n)

/-- This includes the pair (point, empty) at n = 0. -/
def diskPair (n : ℕ) : Pair :=
  ⟨disk n, {x | ‖x.val‖ = 1}⟩

abbrev simplex (n : ℕ) : TopCat := TopCat.of (P202.Cellular.StandardSimplex n)

def simplexPair (n : ℕ) : Pair :=
  ⟨simplex n, {x | ∃ i, x.weights i = 0}⟩

/-- Identity parametrization with the vertex order 0,...,n. -/
def affineSimplex (n : ℕ) : Simplex (simplex n) n :=
  (simplexEquiv (simplex n) n).symm (ContinuousMap.id _)

/-- The face opposite the i-th vertex, with its inherited increasing order. -/
def boundaryFace {n : ℕ} (i : Fin (n+2)) :
    C(P202.Cellular.StandardSimplex n, (simplexPair (n+1)).sub) where
  toFun x := ⟨faceInclusion i x, i, by
    change (x.weights.mapDomain i.succAbove) i = 0
    exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)⟩
  continuous_toFun := (faceInclusion i).continuous.subtype_mk _

def boundarySimplex {n : ℕ} (i : Fin (n+2)) :
    Simplex (simplexPair (n+1)).sub n :=
  (simplexEquiv _ n).symm (boundaryFace i)

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- The affine oriented chain with an arbitrary coefficient. -/
def affineChain (n : ℕ) (m : M) : Chains M (simplex n) n :=
  Finsupp.single (affineSimplex n) m

/-- The signed boundary cycle, in the boundary space itself. -/
def orientedBoundary (n : ℕ) (m : M) : Chains M (simplexPair (n+1)).sub n :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.single (boundarySimplex i) m

/-- Transport to the actual shared integer-indexed ordinary complexes. -/
def affineChainZ (n : ℕ) (m : M) : (ordinaryComplex R M (simplex n)).X (n : ℤ) :=
  (ordinaryNonnegativeIso R M (simplex n) n).inv (affineChain M n m)

def orientedBoundaryZ (n : ℕ) (m : M) :
    (ordinaryComplex R M (simplexPair (n+1)).sub).X (n : ℤ) :=
  (ordinaryNonnegativeIso R M _ n).inv (orientedBoundary M n m)

def relativeAffineChain (n : ℕ) (m : M) : (ordinary R M (simplexPair n)).X (n : ℤ) :=
  (projection (ordinaryFunctor R M) (simplexPair n)).f (n : ℤ) (affineChainZ R M n m)

/-- Class in the actual categorical homology object, rather than a replacement quotient. -/
def classOf (K : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) (z : K.X n)
    (hz : K.d n (n-1) z = 0) : K.homology n :=
  P202Specs.ChainLES.cycleClass K (n-1) ((ComplexShape.down ℤ).next_eq' (by simp)) z hz

/-- The nonnegative reduced homology of every sphere. -/
def sphereHomology_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n j : ℕ),
    (j = n → Nonempty (reducedHomology R M (sphere n) (j : ℤ) ≃ₗ[R] M)) ∧
    (j ≠ n → IsZero (reducedHomology R M (sphere n) (j : ℤ)))

/-- Relative disk computation, including the zero-dimensional disk. -/
def diskHomology_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n j : ℕ),
    (j = n → Nonempty (relativeHomology R M (diskPair n) (j : ℤ) ≃ₗ[R] M)) ∧
    (j ≠ n → IsZero (relativeHomology R M (diskPair n) (j : ℤ)))

/-- The oriented relative simplex is exactly the indicated copy of the coefficient
module: coefficient m is the class of m times the affine simplex. In particular,
R=M=Z and m=1 gives the specified integral generator and fixes its sign. -/
def simplexGenerator_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ),
    ∃ hz : ∀ m : M, (ordinary R M (simplexPair n)).d (n : ℤ) ((n : ℤ)-1)
        (relativeAffineChain R M n m) = 0,
      ∃ e : relativeHomology R M (simplexPair n) (n : ℤ) ≃ₗ[R] M,
        ∀ m, e (classOf R (ordinary R M (simplexPair n)) (n : ℤ)
          (relativeAffineChain R M n m) (hz m)) = m

/-- The remaining degrees of the simplex pair vanish. -/
def simplexVanishing_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n j : ℕ), j ≠ n → IsZero (relativeHomology R M (simplexPair n) (j : ℤ))

/-- The connecting map sends the relative oriented simplex to its signed
boundary cycle. Short exactness, and both cycle conditions, are conclusions. -/
def simplexConnecting_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ),
    ∃ h : P202Specs.ChainLES.DegreewiseShortExact
        (sequence (ordinaryFunctor R M) (simplexPair (n+1))),
      ∀ m : M,
        ∃ (hz : (ordinary R M (simplexPair (n+1))).d ((n+1 : ℕ) : ℤ) (n : ℤ)
            (relativeAffineChain R M (n+1) m) = 0)
          (hb : (ordinaryComplex R M (simplexPair (n+1)).sub).d (n : ℤ) ((n : ℤ)-1)
            (orientedBoundaryZ R M n m) = 0),
          P202Specs.ChainLES.connecting h ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp)
            (classOf R _ ((n+1 : ℕ) : ℤ) (relativeAffineChain R M (n+1) m)
              (by have hh : (((n+1 : ℕ) : ℤ)-1) = (n : ℤ) := by omega
                  rw [hh]; exact hz)) =
            classOf R _ (n : ℤ) (orientedBoundaryZ R M n m) hb

/-- In dimension one the signed boundary is final endpoint minus initial endpoint:
face 0 omits v0, and face 1 omits v1. -/
def endpointDifference_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (m : M),
    orientedBoundary M 0 m = Finsupp.single (boundarySimplex (n := 0) 0) m -
      Finsupp.single (boundarySimplex (n := 0) 1) m

/-- A point and all nonempty contractible spaces have zero reduced homology,
in every integer degree with the shared augmentation convention. -/
def contractible_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    (∀ j : ℤ, IsZero (reducedHomology R M P202Specs.SingularDegreeZero.point.{w} j)) ∧
    ∀ (X : TopCat.{w}) [Nonempty X] [ContractibleSpace X] (j : ℤ),
      IsZero (reducedHomology R M X j)

end P202Specs.SpheresDisks
