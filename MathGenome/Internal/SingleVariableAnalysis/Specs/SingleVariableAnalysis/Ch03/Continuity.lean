import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.RelativeLimit
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Compactness.Compact

/-!
Independent specification for K03.03.continuity, paper.tex:489–506.
The domain carries its usual metric and a subset its induced metric/topology.
The metric target formulation includes both canonical scalar targets ℝ and ℂ.
Only values on E are tested; at the base point a ∈ E the test is unpunctured.
Natural index n denotes manuscript index n+1. Test sequences may equal a.
The last three bridges fix the relative topology and finite-subcover convention;
they assert no compactness theorem about particular sets.
-/
namespace Specs.SingleVariableAnalysis.Ch03.Continuity

open scoped Topology
open Specs.SingleVariableAnalysis.Ch02.RelativeLimit
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
universe u v

def relativeContinuousAtType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → [MetricSpace X] → [MetricSpace Y] →
    (X → Y) → Set X → X → Prop

def relativeContinuousAtValue : relativeContinuousAtType.{u,v} :=
  fun f E a => ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ E, dist x a < δ → dist (f x) (f a) < ε

def relativeContinuousType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → [MetricSpace X] → [MetricSpace Y] →
    (X → Y) → Set X → Prop

def relativeContinuousValue : relativeContinuousType.{u,v} :=
  fun f E => ∀ a ∈ E, relativeContinuousAtValue f E a

def relativeContinuousAtWithinIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X),
    relativeContinuousAtValue f E a ↔ ContinuousWithinAt f E a

def relativeContinuousAtSubtypeIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : E),
    relativeContinuousAtValue f E a ↔ ContinuousAt (fun x : E => f x) a

def relativeContinuousSubtypeIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X),
    relativeContinuousValue f E ↔ Continuous (fun x : E => f x)

def relativeContinuousAtPuncturedIffOfMem : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : E),
    relativeContinuousAtValue f E a ↔ relativePuncturedLimitValue f E a (f a)

def relativeContinuousAtPuncturedIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : E),
    domainAccumulationValue E a →
      (relativeContinuousAtValue f E a ↔ relativePuncturedLimitValue f E a (f a))

def relativeContinuousAtOfIsolated : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : E),
    ¬ domainAccumulationValue E a → relativeContinuousAtValue f E a

def relativeContinuousAtOfIsolatingBall : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : E),
    (∃ r : ℝ, 0 < r ∧ ∀ x ∈ E, dist x a < r → x = a) →
      relativeContinuousAtValue f E a

def relativeContinuousAtSequentialIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : E),
    relativeContinuousAtValue f E a ↔
      ∀ x : ℕ → X, (∀ n, x n ∈ E) →
        Filter.Tendsto x Filter.atTop (𝓝 (a : X)) →
        Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 (f a))

/-- Also covers an intrinsic metric domain and every function on it. -/
def continuousAtSequentialIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (a : X), ContinuousAt f a ↔
      ∀ x : ℕ → X, Filter.Tendsto x Filter.atTop (𝓝 a) →
        Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 (f a))

def realRelativeContinuousAtIff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : E),
    relativeContinuousAtValue f E a ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, dist x a < δ → |f x - f a| < ε

def complexRelativeContinuousAtIff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (a : E),
    relativeContinuousAtValue f E a ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, dist x a < δ → ‖f x - f a‖ < ε

def realRelativeContinuousAtSequentialIff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : E),
    relativeContinuousAtValue f E a ↔
      ∀ x : ℕ → X, (∀ n, x n ∈ E) →
        Filter.Tendsto x Filter.atTop (𝓝 (a : X)) →
        realSequenceConvergesValue (fun n => f (x n)) (f a)

def complexRelativeContinuousAtSequentialIff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (a : E),
    relativeContinuousAtValue f E a ↔
      ∀ x : ℕ → X, (∀ n, x n ∈ E) →
        Filter.Tendsto x Filter.atTop (𝓝 (a : X)) →
        complexSequenceConvergesValue (fun n => f (x n)) (f a)

def relativeOpenIff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X) (U : Set E),
    IsOpen U ↔ ∃ V : Set X, IsOpen V ∧ (Subtype.val ⁻¹' V : Set E) = U

def relativeClosedIff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X) (F : Set E),
    IsClosed F ↔ ∃ G : Set X, IsClosed G ∧ (Subtype.val ⁻¹' G : Set E) = F

def compactRelativeCoverIff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X),
    IsCompact E ↔ ∀ {ι : Type u} (U : ι → Set E),
      (∀ i, IsOpen (U i)) → (Set.univ ⊆ ⋃ i, U i) →
        ∃ t : Finset ι, Set.univ ⊆ ⋃ i ∈ t, U i

end Specs.SingleVariableAnalysis.Ch03.Continuity
