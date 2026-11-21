import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions

/-!
Independent specification of `paper.tex`, Definition `d13:17:chaos-definition`.

The paper applies these predicates to continuous self-maps of metric spaces.
As with the Chapter 15 orbit predicates, the individual conditions make sense
for arbitrary self-maps, so continuity is a standing hypothesis when applying
them, rather than an extra conjunct hidden in any of the three conditions.
The two purely topological predicates need only a topology. No nonemptiness,
compactness, absence of isolated points, or invertibility is assumed.
-/

namespace Specs.D13Unified.Ch17.ChaosDefinitions

universe u
open Set
open scoped Topology
open Specs.D13Unified.Ch15.DiscreteDefinitions (iterate)

def TopologicallyTransitiveType :=
  {X : Type u} → [TopologicalSpace X] → (X → X) → Prop

/-- Some nonnegative iterate of each nonempty open set meets each other one. -/
def TopologicallyTransitive : TopologicallyTransitiveType :=
  fun F => ∀ U V : Set _, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
    ∃ n : ℕ, ((iterate F n '' U) ∩ V).Nonempty

def periodicPointsType := {X : Type u} → (X → X) → Set X

/-- All positive-period points, without requiring a prescribed least period. -/
def periodicPoints : periodicPointsType :=
  fun F => Function.periodicPts F

def DensePeriodicPointsType :=
  {X : Type u} → [TopologicalSpace X] → (X → X) → Prop

/-- The set of all points fixed by some positive iterate is dense. -/
def DensePeriodicPoints : DensePeriodicPointsType :=
  fun F => Dense (periodicPoints F)

def SensitiveDependenceType := {X : Type u} → [MetricSpace X] → (X → X) → Prop

/-- One positive separation constant works for every point and neighborhood.
The separation is strictly greater than that constant. -/
def SensitiveDependence : SensitiveDependenceType :=
  fun F => ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ U ∈ 𝓝 x,
    ∃ y ∈ U, ∃ n : ℕ, δ < dist (iterate F n x) (iterate F n y)

def ChaoticType := {X : Type u} → [MetricSpace X] → (X → X) → Prop

/-- The three-part convention for chaos used in this manuscript. -/
def Chaotic : ChaoticType :=
  fun F => TopologicallyTransitive F ∧ DensePeriodicPoints F ∧ SensitiveDependence F

def topologicallyTransitive_iffStatement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (F : X → X),
    TopologicallyTransitive F ↔
      ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
        ∃ n : ℕ, ((F^[n] '' U) ∩ V).Nonempty

def topologicallyTransitive_iff_exists_memStatement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (F : X → X),
    TopologicallyTransitive F ↔
      ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
        ∃ x ∈ U, ∃ n : ℕ, F^[n] x ∈ V

def mem_periodicPointsStatement : Prop :=
  ∀ {X : Type u} (F : X → X) (x : X),
    x ∈ periodicPoints F ↔ ∃ n : ℕ, 0 < n ∧ F^[n] x = x

def densePeriodicPoints_iffStatement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (F : X → X),
    DensePeriodicPoints F ↔ Dense {x : X | ∃ n : ℕ, 0 < n ∧ F^[n] x = x}

def densePeriodicPoints_iff_openStatement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (F : X → X),
    DensePeriodicPoints F ↔ ∀ U : Set X, IsOpen U → U.Nonempty →
      ∃ x ∈ U, ∃ n : ℕ, 0 < n ∧ F^[n] x = x

def sensitiveDependence_iff_neighborhoodsStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X),
    SensitiveDependence F ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ U ∈ 𝓝 x,
      ∃ y ∈ U, ∃ n : ℕ, δ < dist (F^[n] x) (F^[n] y)

def sensitiveDependence_iff_ballsStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X),
    SensitiveDependence F ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ ε : ℝ, 0 < ε →
      ∃ y, dist y x < ε ∧ ∃ n : ℕ, δ < dist (F^[n] x) (F^[n] y)

def chaotic_iffStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X),
    Chaotic F ↔ TopologicallyTransitive F ∧ DensePeriodicPoints F ∧ SensitiveDependence F

end Specs.D13Unified.Ch17.ChaosDefinitions
