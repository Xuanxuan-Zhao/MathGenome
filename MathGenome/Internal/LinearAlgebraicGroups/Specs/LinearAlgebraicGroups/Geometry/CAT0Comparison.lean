import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Geometry.CAT0Spaces
import Mathlib.Tactic.NormNum

/-! Statements for squared distance comparison and its metric consequences. -/

open Set unitInterval

namespace LinearAlgebraicGroups.Geometry.CAT0ComparisonSpec

open CAT0SpacesSpec

variable {X : Type*} [MetricSpace X]

def squaredDistanceComparisonType := ∀ (X : Type*) [MetricSpace X], Prop

def squaredDistanceComparisonValue (X : Type*) [MetricSpace X] : Prop :=
  ∀ (z : X) {a b : X} (p : geodesicSegmentValue a b) (t : I),
    dist z (p.val t) ^ 2 ≤
      (1 - (t : ℝ)) * dist z a ^ 2 + (t : ℝ) * dist z b ^ 2 -
        (t : ℝ) * (1 - (t : ℝ)) * dist a b ^ 2

def midpointComparisonType := ∀ (X : Type*) [MetricSpace X], Prop

def midpointComparisonValue (X : Type*) [MetricSpace X] : Prop :=
  ∀ (z : X) {a b : X} (p : geodesicSegmentValue a b),
    dist z (p.val (⟨1 / 2, by norm_num⟩ : I)) ^ 2 ≤
      (dist z a ^ 2 + dist z b ^ 2) / 2 - dist a b ^ 2 / 4

def cat0IffSquaredDistanceComparisonType :=
  ∀ {X : Type*} [MetricSpace X], isGeodesicSpaceValue X →
    (cat0Value X ↔ squaredDistanceComparisonValue X)

def cat0IffMidpointComparisonType :=
  ∀ {X : Type*} [MetricSpace X], isGeodesicSpaceValue X →
    (cat0Value X ↔ midpointComparisonValue X)

def uniquelyGeodesicType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → isUniquelyGeodesicValue X

def distAlongSegmentsType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X →
    ∀ {a b c d : X} (p : geodesicSegmentValue a b) (q : geodesicSegmentValue c d) (t : I),
      dist (p.val t) (q.val t) ≤ (1 - (t : ℝ)) * dist a c + (t : ℝ) * dist b d

def quadrilateralType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ a b c d : X,
    dist a c ^ 2 + dist b d ^ 2 ≤ dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2

def euclideanType :=
  ∀ (n : ℕ), cat0Value (EuclideanSpace ℝ (Fin n))

/-- The zero-slim triangle characterization of metric trees. -/
def metricTreeType := ∀ (X : Type*) [MetricSpace X], Prop

def metricTreeValue (X : Type*) [MetricSpace X] : Prop :=
  isGeodesicSpaceValue X ∧
    ∀ {a b c : X} (p : geodesicSegmentValue a b) (q : geodesicSegmentValue a c)
      (r : geodesicSegmentValue b c) (t : I),
      p.val t ∈ range q.val ∪ range r.val

def metricTreeCat0Type :=
  ∀ {X : Type*} [MetricSpace X], metricTreeValue X → cat0Value X

def minsetClosedType :=
  ∀ {X : Type*} [MetricSpace X] (g : X ≃ᵢ X), IsClosed (minsetValue g)

def minsetConvexType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ g : X ≃ᵢ X,
    geodesicConvexValue (minsetValue g)

def commonMinsetClosedType :=
  ∀ {X : Type*} [MetricSpace X] {ι : Type*} (f : ι → X ≃ᵢ X),
    IsClosed (commonMinsetValue f)

def commonMinsetConvexType :=
  ∀ {X : Type*} [MetricSpace X] {ι : Type*}, cat0Value X → ∀ f : ι → X ≃ᵢ X,
    geodesicConvexValue (commonMinsetValue f)

def convexSubtypeCat0Type :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ {C : Set X},
    C.Nonempty → geodesicConvexValue C → cat0Value C

def closedConvexSubtypeType :=
  ∀ {X : Type*} [MetricSpace X] [CompleteSpace X], cat0Value X → ∀ {C : Set X},
    C.Nonempty → IsClosed C → geodesicConvexValue C → cat0Value C ∧ CompleteSpace C

end LinearAlgebraicGroups.Geometry.CAT0ComparisonSpec
