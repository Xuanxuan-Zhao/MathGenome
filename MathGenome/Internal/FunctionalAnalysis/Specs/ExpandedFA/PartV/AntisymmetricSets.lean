import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ExtremeScalarMeasures
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Measure.Support

/-! Independent statements for the antisymmetric sets and extreme annihilating
measure argument at `fa2:p5:bishop`, paper.tex 23416–23440. Algebras are complex
linear and multiplicatively closed, without a unit or involution requirement.
Constancy is pairwise equality, so the empty set is included. -/

noncomputable section
namespace ExpandedFA.PartV.AntisymmetricSetsSpec
open Set MeasureTheory
open scoped ZeroAtInfty
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
universe u

/-- Every algebra function which is real on `S` is constant on `S`. -/
def IsAntisymmetric {K : Type u} [TopologicalSpace K]
    (A : NonUnitalSubalgebra ℂ C(K, ℂ)) (S : Set K) : Prop :=
  ∀ f ∈ A, (∀ x ∈ S, (f x).im = 0) →
    ∀ x ∈ S, ∀ y ∈ S, f x = f y

/-- Maximality among closed antisymmetric sets. Closure preservation implies
that these sets are also maximal among all antisymmetric sets. -/
def IsMaximalClosedAntisymmetric {K : Type u} [TopologicalSpace K]
    (A : NonUnitalSubalgebra ℂ C(K, ℂ)) (S : Set K) : Prop :=
  IsClosed S ∧ IsAntisymmetric A S ∧
    ∀ T, IsClosed T → IsAntisymmetric A T → S ⊆ T → T ⊆ S

/-- The actual total-variation unit ball in the annihilator. -/
def annihilatorBall {K : Type u} [TopologicalSpace K] [MeasurableSpace K]
    (A : NonUnitalSubalgebra ℂ C(K, ℂ)) : Set (VectorMeasure K ℂ) :=
  {ν | ν ∈ ExtremeScalarMeasuresSpec.measureBall K ℂ ∧
    ∀ f ∈ A, scalarIntegral ν f = 0}

/-- Weak-star topology of measures: the initial topology of integration
against all C₀ functions. On compact K these are exactly all continuous
functions, via `ContinuousMap.liftZeroAtInfty`. -/
@[instance_reducible]
def measureWeakStarTopology (K : Type u) [TopologicalSpace K] [MeasurableSpace K] :
    TopologicalSpace (VectorMeasure K ℂ) :=
  TopologicalSpace.induced
    (fun ν : VectorMeasure K ℂ => fun f : C₀(K, ℂ) => scalarIntegral ν f) inferInstance

def AnnihilatorBallCompactness : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K]
    (A : NonUnitalSubalgebra ℂ C(K, ℂ)),
    @IsCompact (VectorMeasure K ℂ) (measureWeakStarTopology K) (annihilatorBall A)

def AntisymmetricType : Type (u + 1) :=
  {K : Type u} → [TopologicalSpace K] →
    NonUnitalSubalgebra ℂ C(K, ℂ) → Set K → Prop

def AntisymmetricValue : AntisymmetricType.{u} := @IsAntisymmetric

def ClosureProperty : Prop :=
  ∀ (K : Type u) [TopologicalSpace K]
    (A : NonUnitalSubalgebra ℂ C(K, ℂ)) (S : Set K),
    IsAntisymmetric A S → IsAntisymmetric A (closure S)

def ChainUnionProperty : Prop :=
  ∀ (K : Type u) [TopologicalSpace K]
    (A : NonUnitalSubalgebra ℂ C(K, ℂ)) (c : Set (Set K)),
    IsChain (· ⊆ ·) c → (∀ S ∈ c, IsAntisymmetric A S) →
    IsAntisymmetric A (⋃₀ c)

def MaximalExtension : Prop :=
  ∀ (K : Type u) [TopologicalSpace K]
    (A : NonUnitalSubalgebra ℂ C(K, ℂ)) (S : Set K),
    IsAntisymmetric A S →
    ∃ T, S ⊆ T ∧ IsMaximalClosedAntisymmetric A T

def MaximalAmongAll : Prop :=
  ∀ (K : Type u) [TopologicalSpace K]
    (A : NonUnitalSubalgebra ℂ C(K, ℂ)) (S : Set K),
    IsMaximalClosedAntisymmetric A S →
    ∀ T, IsAntisymmetric A T → S ⊆ T → T ⊆ S

/-- The norm-one extreme-point support conclusion, in the original measure
model, for arbitrary closed complex algebras. Extremality is real convexity.
No nonemptiness, separability, unitality or self-adjointness is assumed. -/
def ExtremeAnnihilatorSupport : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K]
    (A : NonUnitalSubalgebra ℂ C(K, ℂ)), IsClosed (A : Set C(K, ℂ)) →
    ∀ ν : VectorMeasure K ℂ,
    ν ∈ (annihilatorBall A).extremePoints ℝ → ν.variation univ = 1 →
    IsAntisymmetric A ν.variation.support

end ExpandedFA.PartV.AntisymmetricSetsSpec
