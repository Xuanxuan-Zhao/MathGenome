import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.RealProjectiveHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.CupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.UniversalCoefficients
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.ThomClass
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.CompactOrientation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.RelativeCupProduct
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Basis.Basic

/-!
Independent interface for the real-projective part of
`prop:p202-cohomology-rings`, paper.tex 2594–2597 and 2621–2643.
The ordinary cohomology groups and product are the existing singular ones.

The complete target includes the hyperplane Thom image and its local and
global fundamental-class evaluations. The generic algebra lemmas are assembly
helpers: their basis and nilpotence hypotheses are not assumptions of the
projective-space theorem.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped DirectSum

universe w
namespace P202Specs.RealProjectiveRing
open P202Specs.RealProjectiveHomology P202Specs.CupProduct P202Specs.SpheresDisks

/-- Actual homogeneous cup powers; the zeroth power is the singular cup unit. -/
def cupPower {X : TopCat.{w}} (C : CohomologyRing (ZMod 2) X)
    (u : H (ZMod 2) X 1) : ∀ n : ℕ, H (ZMod 2) X n
  | 0 => letI := C.gradedRing; GradedMonoid.GOne.one
  | n+1 => C.product n 1 (cupPower C u n) u

/-- The actual Kronecker pairing, obtained by evaluation on singular cycles. -/
def kronecker (X : TopCat.{w}) (n : ℕ) :
    H (ZMod 2) X n →ₗ[ZMod 2]
      P202Specs.SingularChains.homology (ZMod 2) (ZMod 2) X (n : ℤ) →ₗ[ZMod 2] ZMod 2 :=
  P202Specs.UniversalCoefficients.evaluation (ZMod 2) (ZMod 2)
    (P202Specs.SingularChains.ordinaryComplex (ZMod 2) (ZMod 2) X) (n : ℤ)

/-- Extension by zero in the first n+1 homogeneous coordinates. -/
abbrev standardCoordinateInclusion (n m : ℕ) (h : n ≤ m) :
    EuclideanSpace ℝ (Fin (n+1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m+1)) :=
  LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (Nat.succ_le_succ h))

/-- Extend the first n+1 coordinates by zero before taking the antipodal quotient. -/
def standardSphereInclusion (n m : ℕ) (h : n ≤ m) : C(sphere n, sphere m) :=
  ⟨fun x => ⟨standardCoordinateInclusion n m h x.val, by
      simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometry.norm_map] using x.property⟩,
    ((standardCoordinateInclusion n m h).continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The standard projective n-plane in projective m-space. -/
def standardInclusion (n m : ℕ) (h : n ≤ m) : projective n ⟶ projective m :=
  TopCat.ofHom {
    toFun := Quotient.map (standardSphereInclusion n m h) (by
      intro x y hxy
      rcases hxy with hxy | hxy
      · exact Or.inl (congrArg (LinearIsometry.piLpExtendByZero 2 ℝ ℝ
          (Fin.castLEEmb (Nat.succ_le_succ h))) hxy)
      · exact Or.inr (by
          change (LinearIsometry.piLpExtendByZero 2 ℝ ℝ
            (Fin.castLEEmb (Nat.succ_le_succ h))) x.val =
            -(LinearIsometry.piLpExtendByZero 2 ℝ ℝ
            (Fin.castLEEmb (Nat.succ_le_succ h))) y.val
          rw [hxy, map_neg]) )
    continuous_toFun := by
      apply continuous_quot_lift
      exact continuous_quot_mk.comp (standardSphereInclusion n m h).continuous }

lemma standardInclusion_quotient (n m : ℕ) (h : n ≤ m) (x : sphere n) :
    standardInclusion n m h (quotientMap n x) =
      quotientMap m (standardSphereInclusion n m h x) := rfl

/-- The first coordinate line, the common intersection point used for the
coordinate hyperplanes on the standard projective subspaces. -/
def coordinatePoint (n : ℕ) : Space n :=
  quotientMap n ⟨EuclideanSpace.single (0 : Fin (n+1)) (1 : ℝ), by simp⟩

/-- Literally R[X]/(X^(m+1)); `AdjoinRoot` is defined by this ideal quotient. -/
abbrev TruncatedPolynomial (R : Type*) [CommRing R] (m : ℕ) :=
  AdjoinRoot ((Polynomial.X : Polynomial R) ^ (m+1))

def variableClass (R : Type*) [CommRing R] (m : ℕ) : TruncatedPolynomial R m :=
  AdjoinRoot.root _

/-- The full graded algebraic answer on the actual projective quotient.
There is deliberately no chosen cohomology replacement in this structure. -/
structure Presentation (m : ℕ) (C : CohomologyRing (ZMod 2) (projective m)) where
  powers : ∀ n : ℕ, H (ZMod 2) (projective m) n
  equiv : letI := C.gradedRing
    letI := C.algebra
    TruncatedPolynomial (ZMod 2) m ≃ₐ[ZMod 2] HStar (ZMod 2) (projective m)
  homogeneous : letI := C.gradedRing
    letI := C.algebra
    ∀ n, equiv (variableClass (ZMod 2) m ^ n) =
      DirectSum.of (H (ZMod 2) (projective m)) n (powers n)
  generators : ∀ n, n ≤ m → Function.Bijective (fun r : ZMod 2 => r • powers n)
  above : ∀ n, m < n → ∀ a : H (ZMod 2) (projective m) n, a = 0

open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData

/-- Geometric data to be constructed on the fixed quotient and its actual
standard hyperplane. None of these fields is an assumption of `completeRing`.
The normal orientation is mod two; its fiber generator has no sign ambiguity. -/
structure HyperplaneGeometry (m : ℕ) where
  source : SmoothManifold m .euclidean (Space m)
  ambient : SmoothManifold (m+1) .euclidean (Space (m+1))
  embedding : IsSmoothEmbedding source ambient (standardInclusion m (m+1) (by omega))
  normal : NormalBundle source ambient (standardInclusion m (m+1) (by omega))
  orientation : P202Specs.ThomClass.Orientation (ZMod 2) normal 1
  tube : ∃ K : TubularNeighborhood normal, P202Specs.ThomClass.NormalCompatible normal K
  thom : P202Specs.CohomologyPairs.relativeCohomology (ZMod 2) (ZMod 2)
    (P202Specs.ThomClass.ambientPair (standardInclusion m (m+1) (by omega))) 1
  fiber_values : P202Specs.ThomClass.HasFiberValues (ZMod 2) orientation thom

def HyperplaneGeometry.ordinaryClass {m : ℕ} (G : HyperplaneGeometry m) :
    H (ZMod 2) (projective (m+1)) 1 :=
  P202Specs.RelativeCupProduct.forget (ZMod 2)
    (P202Specs.ThomClass.ambientPair (standardInclusion m (m+1) (by omega))) 1 G.thom

/-- An ordinary fundamental class normalized by the actual local orientation
groups. The mod-two orientation is canonical by the upstream uniqueness theorem. -/
structure FundamentalData (n : ℕ) where
  manifold : P202Specs.LocalOrientation.Manifold n (Space n)
  orientation : P202Specs.LocalOrientation.Orientation (ZMod 2) manifold
  fundamental : P202Specs.SingularChains.homology (ZMod 2) (ZMod 2) (projective n) (n : ℤ)
  local_values : P202Specs.CompactOrientation.HasLocalValues (ZMod 2) orientation.val
    Set.univ (P202Specs.CompactOrientation.absoluteToSupported (ZMod 2) (Space n) n fundamental)

/-- The power restricts to the ordinary image of the normalized local top class
on the standard projective n-plane; both local and global evaluations are 1. -/
structure PowerEvaluation (μ : NaturalCohomologyRing (ZMod 2)) (m n : ℕ) (hn : n ≤ m)
    (u : H (ZMod 2) (projective m) 1) where
  fundamental : FundamentalData n
  localClass : P202Specs.CohomologyPairs.relativeCohomology (ZMod 2) (ZMod 2)
    (P202Specs.LocalOrientation.localPair (Space n) (coordinatePoint n)) (n : ℤ)
  local_generator : Function.Bijective (fun r : ZMod 2 => r • localClass)
  local_evaluation : P202Specs.UniversalCoefficients.evaluation (ZMod 2) (ZMod 2)
    (P202Specs.RelativeSingularChains.ordinary (ZMod 2) (ZMod 2)
      (P202Specs.LocalOrientation.localPair (Space n) (coordinatePoint n))) (n : ℤ)
      localClass (fundamental.orientation.val (coordinatePoint n)) = 1
  ordinary_image : P202Specs.RelativeCupProduct.forget (ZMod 2) _ n localClass =
    hPullback (ZMod 2) (standardInclusion n m hn) n (cupPower (μ.ring (projective m)) u n)
  global_evaluation : kronecker (projective n) n
    (hPullback (ZMod 2) (standardInclusion n m hn) n (cupPower (μ.ring (projective m)) u n))
      fundamental.fundamental = 1

/-- The full positive-dimensional conclusion, with the generator tied to the
hyperplane Thom class and all powers tied to the actual singular cup product. -/
structure GeometricPresentation (μ : NaturalCohomologyRing (ZMod 2)) (m : ℕ) where
  geometry : HyperplaneGeometry m
  presentation : Presentation (m+1) (μ.ring (projective (m+1)))
  powers_eq : ∀ n, presentation.powers n =
    cupPower (μ.ring (projective (m+1))) geometry.ordinaryClass n
  evaluations : ∀ n (hn : n ≤ m+1), PowerEvaluation μ (m+1) n hn geometry.ordinaryClass

namespace Expected

/-- Complete source obligation. The point case and every positive dimension
are conclusions; no projective geometry, power basis or evaluation is assumed. -/
def completeRing : Prop :=
  ∀ μ : NaturalCohomologyRing (ZMod 2),
    Nonempty (Presentation 0 (μ.ring (projective 0))) ∧
      ∀ m : ℕ, Nonempty (GeometricPresentation μ m)

/-- Canonical mod-two fundamental classes on the actual projective quotients. -/
def fundamentalClasses : Prop := ∀ n : ℕ, Nonempty (FundamentalData n)

/-- Full hyperplane input, including the normalized relative Thom class. -/
def hyperplaneGeometry : Prop := ∀ n : ℕ, Nonempty (HyperplaneGeometry n)

/-- The local generator dual to the canonical mod-two local orientation. -/
def normalizedLocalClasses : Prop :=
  ∀ (n : ℕ) (F : FundamentalData n),
    ∃ a : P202Specs.CohomologyPairs.relativeCohomology (ZMod 2) (ZMod 2)
        (P202Specs.LocalOrientation.localPair (Space n) (coordinatePoint n)) (n : ℤ),
      Function.Bijective (fun r : ZMod 2 => r • a) ∧
      P202Specs.UniversalCoefficients.evaluation (ZMod 2) (ZMod 2)
        (P202Specs.RelativeSingularChains.ordinary (ZMod 2) (ZMod 2)
          (P202Specs.LocalOrientation.localPair (Space n) (coordinatePoint n))) (n : ℤ)
        a (F.orientation.val (coordinatePoint n)) = 1 ∧
      kronecker (projective n) n
        (P202Specs.RelativeCupProduct.forget (ZMod 2)
          (P202Specs.LocalOrientation.localPair (Space n) (coordinatePoint n)) n a)
        F.fundamental = 1

/-- The constructed hyperplane Thom class has a genuinely nonzero fiber value. -/
def hyperplaneThomNonzero : Prop := ∀ (n : ℕ) (G : HyperplaneGeometry n), G.thom ≠ 0

/-- The ordinary image of the normalized hyperplane Thom class is the
specified degree-one generator, on the actual projective quotient. -/
def hyperplaneGenerator : Prop :=
  ∀ (n : ℕ) (G : HyperplaneGeometry n),
    Function.Bijective (fun r : ZMod 2 => r • G.ordinaryClass)

/-- The actual singular cup unit generates degree zero. -/
def degreeZeroUnitGenerator : Prop :=
  ∀ (m : ℕ) (C : CohomologyRing (ZMod 2) (projective m)),
    letI := C.gradedRing
    Function.Bijective (fun r : ZMod 2 =>
      r • (GradedMonoid.GOne.one : H (ZMod 2) (projective m) 0))

/-- Every degree-one singular class satisfies the top truncation relation. -/
def cohomologyTruncation : Prop :=
  ∀ (m : ℕ) (C : CohomologyRing (ZMod 2) (projective m))
    (u : H (ZMod 2) (projective m) 1),
    letI := C.gradedRing
    ∀ n : ℕ, m < n → (DirectSum.of _ 1 u) ^ n = 0

/-- Assembly helper only: the geometry and local restrictions are the
remaining conclusions of `completeRing`, not assumptions in that target. -/
def geometricAssembly : Prop :=
  ∀ (μ : NaturalCohomologyRing (ZMod 2)) (m : ℕ) (G : HyperplaneGeometry m),
    (∀ n (hn : n ≤ m+1), PowerEvaluation μ (m+1) n hn G.ordinaryClass) →
      Nonempty (GeometricPresentation μ m)

/-- The top relation and all higher relations in the presented algebra.
These do not assert corresponding relations in cohomology before assembly. -/
def quotientTruncation : Prop :=
  ∀ (R : Type*) [CommRing R] (m : ℕ),
    variableClass R m ^ (m+1) = 0 ∧
      ∀ n : ℕ, m < n → variableClass R m ^ n = 0

/-- The dimension-zero polynomial quotient is the coefficient ring. -/
def quotientPoint : Prop :=
  ∀ (R : Type*) [CommRing R], Nonempty (TruncatedPolynomial R 0 ≃ₐ[R] R)

/-- Over F₂ the actual graded-commutative singular cup ring is commutative
as an ordinary ring on its direct sum. -/
def modTwoCommutative : Prop :=
  ∀ (X : TopCat.{w}) (C : CohomologyRing (ZMod 2) X),
    letI := C.gradedRing
    ∀ a b : HStar (ZMod 2) X, a * b = b * a

/-- Generators of a rank-one F₂-module have no sign ambiguity. -/
def modTwoGeneratorUnique : Prop :=
  ∀ (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] (a b : V),
    Function.Bijective (fun r : ZMod 2 => r • a) →
    Function.Bijective (fun r : ZMod 2 => r • b) → a = b

/-- Generic final algebra assembly. In the intended application, neither
`hx` nor the basis is available until the geometric and additive work is proved. -/
def presentationFromBasis : Prop :=
  ∀ (R : Type*) [CommRing R] [Nontrivial R]
    (A : Type*) [CommRing A] [Algebra R A]
    (m : ℕ) (x : A), x ^ (m+1) = 0 →
    ∀ b : Module.Basis (Fin (m+1)) R A,
      (∀ i, b i = x ^ (i : ℕ)) →
      ∃ e : TruncatedPolynomial R m ≃ₐ[R] A,
        e (variableClass R m) = x

/-- Degree zero of each actual projective quotient is the coefficient field. -/
def cohomologyDegreeZero : Prop :=
  ∀ m : ℕ, Nonempty (H (ZMod 2) (projective m) 0 ≃ₗ[ZMod 2] ZMod 2)

/-- All the nonzero graded groups, on the fixed singular cohomology objects. -/
def cohomologyGroups : Prop :=
  ∀ m n : ℕ, n ≤ m → Nonempty (H (ZMod 2) (projective m) n ≃ₗ[ZMod 2] ZMod 2)

/-- Vanishing above the dimension, in the actual singular cohomology. -/
def cohomologyAboveDimension : Prop :=
  ∀ m n : ℕ, m < n → ∀ a : H (ZMod 2) (projective m) n, a = 0

/-- Powers are homogeneous in the ring with the existing singular product. -/
def cupPowerHomogeneous : Prop :=
  ∀ (X : TopCat.{w}) (C : CohomologyRing (ZMod 2) X) (u : H (ZMod 2) X 1),
    letI := C.gradedRing
    ∀ n, (DirectSum.of _ 1 u) ^ n = DirectSum.of _ n (cupPower C u n)

/-- Restriction of powers uses the actual cohomology pullback. -/
def cupPowerNatural : Prop :=
  ∀ (μ : NaturalCohomologyRing.{0,w} (ZMod 2)) {X Y : TopCat.{w}} (f : X ⟶ Y)
    (u : H (ZMod 2) Y 1) (n : ℕ),
    hPullback (ZMod 2) f n (cupPower (μ.ring Y) u n) =
      cupPower (μ.ring X) (hPullback (ZMod 2) f 1 u) n

/-- Graded assembly from powers already proved to be homogeneous generators.
The hypotheses here are intermediate obligations, not new assumptions in the
original projective-space theorem. -/
def presentationFromPowers : Prop :=
  ∀ (m : ℕ) (C : CohomologyRing (ZMod 2) (projective m))
    (p : ∀ n, H (ZMod 2) (projective m) n),
    letI := C.gradedRing
    letI := C.algebra
    (∀ n, (DirectSum.of _ 1 (p 1)) ^ n = DirectSum.of _ n (p n)) →
    (∀ n, n ≤ m → Function.Bijective (fun r : ZMod 2 => r • p n)) →
    (∀ n, m < n → ∀ a : H (ZMod 2) (projective m) n, a = 0) →
    Nonempty (Presentation m C)

/-- The singular cohomology groups of the actual dimension-zero quotient. -/
def pointCohomology : Prop :=
  Nonempty (H (ZMod 2) (projective 0) 0 ≃ₗ[ZMod 2] ZMod 2) ∧
    ∀ n : ℕ, 0 < n → ∀ a : H (ZMod 2) (projective 0) n, a = 0

/-- The complete graded algebraic presentation in dimension zero. -/
def pointPresentation : Prop :=
  ∀ C : CohomologyRing (ZMod 2) (projective 0), Nonempty (Presentation 0 C)

/-- The graded algebraic presentation, also obtained by forgetting the
geometric and evaluation fields of the complete conclusion. -/
def ringPresentation : Prop :=
  ∀ μ : NaturalCohomologyRing (ZMod 2), ∀ m : ℕ,
    Nonempty (Presentation m (μ.ring (projective m)))

end Expected
end P202Specs.RealProjectiveRing
