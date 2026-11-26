import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Geometry.CAT0Comparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Statements for nearest-point projection and its application to displacement minsets. -/

open Filter Set unitInterval
open scoped Topology

namespace LinearAlgebraicGroups.Geometry.ProjectionSpec

open CAT0SpacesSpec

variable {X : Type*} [MetricSpace X]

def isNearestPointType := ∀ {X : Type*} [MetricSpace X], Set X → X → X → Prop

def isNearestPointValue (C : Set X) (x p : X) : Prop :=
  p ∈ C ∧ ∀ q ∈ C, dist x p ≤ dist x q

def nearestPointType := ∀ {X : Type*} [MetricSpace X], Set X → X → X

noncomputable def nearestPointValue (C : Set X) (x : X) : X := by
  classical
  exact if h : ∃ p, isNearestPointValue C x p then Classical.choose h else x

def existsUniqueNearestPointType :=
  ∀ {X : Type*} [MetricSpace X] {C : Set X}, cat0Value X → ∀ [CompleteSpace C],
    C.Nonempty → geodesicConvexValue C → ∀ x : X, ∃! p, isNearestPointValue C x p

def isNearestPointUniqueType :=
  ∀ {X : Type*} [MetricSpace X] {C : Set X}, cat0Value X → geodesicConvexValue C →
    ∀ {x p q : X}, isNearestPointValue C x p → isNearestPointValue C x q → p = q

def nearestPointCharacterizationType :=
  ∀ {X : Type*} [MetricSpace X] {C : Set X}, cat0Value X → ∀ [CompleteSpace C],
    C.Nonempty → geodesicConvexValue C → ∀ x : X, isNearestPointValue C x (nearestPointValue C x)

def pythagoreanOfIsNearestPointType :=
  ∀ {X : Type*} [MetricSpace X] {C : Set X}, cat0Value X → geodesicConvexValue C →
    ∀ {x p q : X}, isNearestPointValue C x p → q ∈ C →
      dist x p ^ 2 + dist p q ^ 2 ≤ dist x q ^ 2

def pythagoreanType :=
  ∀ {X : Type*} [MetricSpace X] {C : Set X}, cat0Value X → ∀ [CompleteSpace C],
    C.Nonempty → geodesicConvexValue C → ∀ (x : X) {q : X}, q ∈ C →
      dist x (nearestPointValue C x) ^ 2 + dist (nearestPointValue C x) q ^ 2 ≤ dist x q ^ 2

def lipschitzNearestPointType :=
  ∀ {X : Type*} [MetricSpace X] {C : Set X}, cat0Value X → ∀ [CompleteSpace C],
    C.Nonempty → geodesicConvexValue C → LipschitzWith 1 (nearestPointValue C)

def nearestPointIsometryType :=
  ∀ {X : Type*} [MetricSpace X] {C : Set X}, cat0Value X → ∀ [CompleteSpace C],
    C.Nonempty → geodesicConvexValue C → ∀ g : X ≃ᵢ X, g '' C = C → ∀ x : X,
      nearestPointValue C (g x) = g (nearestPointValue C x)

def closedConvexMinsetType :=
  ∀ {X : Type*} [MetricSpace X] [CompleteSpace X], cat0Value X → ∀ g : X ≃ᵢ X,
    IsClosed (minsetValue g) ∧ geodesicConvexValue (minsetValue g) ∧ CompleteSpace (minsetValue g)

def closedConvexCommonMinsetType :=
  ∀ {X : Type*} [MetricSpace X] [CompleteSpace X], cat0Value X →
    ∀ {ι : Type*} (f : ι → X ≃ᵢ X),
      IsClosed (commonMinsetValue f) ∧ geodesicConvexValue (commonMinsetValue f) ∧
        CompleteSpace (commonMinsetValue f)

def nearestPointAlongSegmentType :=
  ∀ {X : Type*} [MetricSpace X] {C : Set X} {p x : X}, isNearestPointValue C x p →
    ∀ (a : geodesicSegmentValue p x) (s : I), isNearestPointValue C (a.val s) p

def comparisonAngleType := ∀ {X : Type*} [MetricSpace X], X → X → X → ℝ

noncomputable def comparisonAngleValue (p x y : X) : ℝ :=
  Real.arccos ((dist p x ^ 2 + dist p y ^ 2 - dist x y ^ 2) /
    (2 * dist p x * dist p y))

def segmentComparisonAngleType :=
  ∀ {X : Type*} [MetricSpace X] {p x y : X},
    geodesicSegmentValue p x → geodesicSegmentValue p y → Ioc (0 : ℝ) 1 × Ioc (0 : ℝ) 1 → ℝ

noncomputable def segmentComparisonAngleValue {p x y : X}
    (a : geodesicSegmentValue p x) (b : geodesicSegmentValue p y)
    (st : Ioc (0 : ℝ) 1 × Ioc (0 : ℝ) 1) : ℝ :=
  comparisonAngleValue p (a.val ⟨st.1, st.1.prop.1.le, st.1.prop.2⟩)
    (b.val ⟨st.2, st.2.prop.1.le, st.2.prop.2⟩)

def alexandrovAngleType :=
  ∀ {X : Type*} [MetricSpace X] {p x y : X},
    geodesicSegmentValue p x → geodesicSegmentValue p y → ℝ

noncomputable def alexandrovAngleValue {p x y : X}
    (a : geodesicSegmentValue p x) (b : geodesicSegmentValue p y) : ℝ :=
  ⨅ st, segmentComparisonAngleValue a b st

def alexandrovAngleLimitType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ {p x y : X}, p ≠ x → p ≠ y →
    ∀ (a : geodesicSegmentValue p x) (b : geodesicSegmentValue p y),
      Tendsto (segmentComparisonAngleValue a b) atBot (𝓝 (alexandrovAngleValue a b))

def nearestPointAngleType :=
  ∀ {X : Type*} [MetricSpace X] {C : Set X}, cat0Value X → geodesicConvexValue C →
    ∀ {p x q : X}, isNearestPointValue C x p → q ∈ C → p ≠ x → p ≠ q →
      ∀ (a : geodesicSegmentValue p x) (b : geodesicSegmentValue p q),
        Real.pi / 2 ≤ alexandrovAngleValue a b

def nearestPointMinsetType :=
  ∀ {X : Type*} [MetricSpace X] [CompleteSpace X], cat0Value X →
    ∀ (a b : X ≃ᵢ X), isSemisimpleValue a → Function.Commute a b →
      ∀ {x : X}, x ∈ minsetValue b → nearestPointValue (minsetValue a) x ∈ minsetValue a ∩ minsetValue b

end LinearAlgebraicGroups.Geometry.ProjectionSpec
