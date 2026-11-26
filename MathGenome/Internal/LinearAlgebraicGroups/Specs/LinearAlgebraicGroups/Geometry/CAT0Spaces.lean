import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.Path

/-! Shared metric and action definitions for Euclidean triangle comparison. -/

open Set unitInterval

universe u v

namespace LinearAlgebraicGroups.Geometry.CAT0SpacesSpec

-- Expected types are themselves types, so their universes are collected in a max.
set_option linter.checkUnivs false

variable {X : Type*} [MetricSpace X]

def isGeodesicSegmentType := ∀ {X : Type*} [MetricSpace X] {x y : X}, Path x y → Prop

def isGeodesicSegmentValue {x y : X} (p : Path x y) : Prop :=
  ∀ s t : I, dist (p s) (p t) = dist s t * dist x y

def geodesicSegmentType := ∀ {X : Type u} [MetricSpace X], X → X → Type u

abbrev geodesicSegmentValue (x y : X) :=
  {p : Path x y // isGeodesicSegmentValue p}

def isGeodesicSpaceType := ∀ (X : Type*) [MetricSpace X], Prop

def isGeodesicSpaceValue (X : Type*) [MetricSpace X] : Prop :=
  Nonempty X ∧ ∀ x y : X, Nonempty (geodesicSegmentValue x y)

def isUniquelyGeodesicType := ∀ (X : Type*) [MetricSpace X], Prop

def isUniquelyGeodesicValue (X : Type*) [MetricSpace X] : Prop :=
  isGeodesicSpaceValue X ∧ ∀ x y : X, Subsingleton (geodesicSegmentValue x y)

def geodesicConvexType := ∀ {X : Type*} [MetricSpace X], Set X → Prop

def geodesicConvexValue (C : Set X) : Prop :=
  ∀ ⦃x y : X⦄, x ∈ C → y ∈ C → ∀ (p : geodesicSegmentValue x y) (t : I), p.val t ∈ C

def euclideanPlaneType := Type

abbrev euclideanPlaneValue := EuclideanSpace ℝ (Fin 2)

def euclideanProductType := Type u → Type v → Type (max u v)

abbrev euclideanProductValue (X : Type u) (Y : Type v) := WithLp 2 (X × Y)

def euclideanProductDistType := ∀ {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y]
    (x y : euclideanProductValue X Y),
  dist x y = Real.sqrt (dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2)

def comparisonTriangleType := ∀ {X : Type*} [MetricSpace X],
    (Fin 3 → X) → (Fin 3 → euclideanPlaneValue) → Prop

def comparisonTriangleValue (v : Fin 3 → X) (w : Fin 3 → euclideanPlaneValue) : Prop :=
  ∀ i j, dist (w i) (w j) = dist (v i) (v j)

def existsComparisonTriangleType := ∀ {X : Type*} [MetricSpace X] (v : Fin 3 → X),
  ∃ w : Fin 3 → euclideanPlaneValue, comparisonTriangleValue v w

def comparisonTriangleCongruentType := ∀ {X : Type*} [MetricSpace X] {v : Fin 3 → X}
    {w w' : Fin 3 → euclideanPlaneValue},
  comparisonTriangleValue v w → comparisonTriangleValue v w' →
    ∃ e : euclideanPlaneValue ≃ᵢ euclideanPlaneValue, ∀ i, e (w i) = w' i

def cat0Type := ∀ (X : Type*) [MetricSpace X], Prop

def cat0Value (X : Type*) [MetricSpace X] : Prop :=
  isGeodesicSpaceValue X ∧
    ∀ (v : Fin 3 → X) (side : ∀ i : Fin 3, geodesicSegmentValue (v i) (v (i + 1)))
      (w : Fin 3 → euclideanPlaneValue), comparisonTriangleValue v w →
        ∀ (i j : Fin 3) (s t : I), dist ((side i).val s) ((side j).val t) ≤
          dist ((1 - (s : ℝ)) • w i + (s : ℝ) • w (i + 1))
               ((1 - (t : ℝ)) • w j + (t : ℝ) • w (j + 1))

section Actions

variable (G X : Type*) [Group G] [MetricSpace X] [MulAction G X]

def isProperActionType := ∀ (G X : Type*) [Group G] [MetricSpace X] [MulAction G X], Prop

def isProperActionValue : Prop :=
  ∀ K : Set X, IsCompact K → {g : G | ∃ x ∈ K, g • x ∈ K}.Finite

def isCocompactActionType := ∀ (G X : Type*) [Group G] [MetricSpace X] [MulAction G X], Prop

def isCocompactActionValue : Prop :=
  ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ (g : G) (k : X), k ∈ K ∧ g • k = x

def isGeometricActionType := ∀ (G X : Type*) [Group G] [MetricSpace X] [MulAction G X], Prop

def isGeometricActionValue : Prop :=
  IsIsometricSMul G X ∧ isProperActionValue G X ∧ isCocompactActionValue G X

end Actions

def translationLengthType := ∀ {X : Type*} [MetricSpace X], (X ≃ᵢ X) → ℝ

noncomputable def translationLengthValue (g : X ≃ᵢ X) : ℝ :=
  ⨅ x : X, dist x (g x)

def minsetType := ∀ {X : Type*} [MetricSpace X], (X ≃ᵢ X) → Set X

def minsetValue (g : X ≃ᵢ X) : Set X :=
  {x | dist x (g x) = translationLengthValue g}

def isSemisimpleType := ∀ {X : Type*} [MetricSpace X], (X ≃ᵢ X) → Prop

def isSemisimpleValue (g : X ≃ᵢ X) : Prop :=
  (minsetValue g).Nonempty

def commonMinsetType := ∀ {X : Type*} [MetricSpace X] {ι : Type*}, (ι → X ≃ᵢ X) → Set X

def commonMinsetValue {ι : Type*} (f : ι → X ≃ᵢ X) : Set X :=
  ⋂ i, minsetValue (f i)

def actionMinsetType := ∀ (G X : Type*) [Group G] [MetricSpace X]
  [MulAction G X] [IsIsometricSMul G X], Set X

def actionMinsetValue (G X : Type*) [Group G] [MetricSpace X]
    [MulAction G X] [IsIsometricSMul G X] : Set X :=
  commonMinsetValue (fun g : G => (IsometryEquiv.constSMul g : X ≃ᵢ X))

end LinearAlgebraicGroups.Geometry.CAT0SpacesSpec
