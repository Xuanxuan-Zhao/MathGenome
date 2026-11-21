import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.LogisticTent
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ChaosDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ShiftSpaces

/-! Full independent statements for Proposition `d13:17:tent-chaos` and its
following remark. Exactness is stated for every nonempty relatively open set,
which in particular includes every nonempty relatively open interval.
The metric is the inherited Euclidean metric on the entire closed interval. -/
noncomputable section
namespace Specs.D13Unified.Ch17.TentChaos
open Set Topology
open Specs.D13Unified.Ch15.LogisticTent
open _root_.D13Unified.Ch15.LogisticTent (Interval)
open Specs.D13Unified.Ch17.ChaosDefinitions
open Specs.D13Unified.Ch17.ShiftSpaces (OneSided)

def exactness : Prop :=
  ∀ U : Set Interval, IsOpen U → U.Nonempty →
    ∃ n : ℕ, tentMap^[n] '' U = univ

def transitivity : Prop := TopologicallyTransitive tentMap

def periodicDensity : Prop := DensePeriodicPoints tentMap

def sensitivityConstants : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ x : Interval, ∀ U ∈ 𝓝 x,
    ∃ y ∈ U, ∃ n : ℕ, δ < dist (tentMap^[n] x) (tentMap^[n] y)

def tentChaos : Prop := Chaotic tentMap

/-- Uniform continuity of the inverse on a compact metric space transports
sensitivity, including the strict separation required by the definition. -/
def compactSensitivityTransport : Prop :=
  ∀ {X Y : Type} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y),
    Function.Semiconj h F G → SensitiveDependence F → SensitiveDependence G

def logisticChaos : Prop := Chaotic logisticFour

/-- The topology obstruction to identifying the interval with the full shift. -/
def noSymbolicHomeomorph : Prop := ¬ Nonempty (Interval ≃ₜ OneSided)

/-- Any continuous surjective coding of the full interval fails injectivity. -/
def codingNotInjective : Prop :=
  ∀ π : OneSided → Interval, Continuous π → Function.Surjective π →
    ¬ Function.Injective π

/-- Explicit standard tent inverse branches; both images include 1/2. -/
def leftBranch (y : Interval) : Interval :=
  ⟨(y : ℝ) / 2, by constructor <;> linarith [y.property.1, y.property.2]⟩

def rightBranch (y : Interval) : Interval :=
  ⟨1 - (y : ℝ) / 2, by constructor <;> linarith [y.property.1, y.property.2]⟩

def leftBranchType := Interval → Interval
def rightBranchType := Interval → Interval

def branchProperties : Prop :=
  Function.Injective leftBranch ∧ Function.Injective rightBranch ∧
  (∀ y, tentMap (leftBranch y) = y) ∧ (∀ y, tentMap (rightBranch y) = y) ∧
  ¬ Disjoint (range leftBranch) (range rightBranch)
end Specs.D13Unified.Ch17.TentChaos
