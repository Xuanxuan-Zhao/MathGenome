import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Geometry.Projection
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! Statements for centers of bounded sets and bounded-orbit fixed points. -/

open Bornology Set

namespace LinearAlgebraicGroups.Geometry.CircumcenterSpec

open CAT0SpacesSpec ProjectionSpec

variable {X : Type*} [MetricSpace X]

def enclosingRadiusType := ∀ {X : Type*} [MetricSpace X], Set X → X → ℝ

noncomputable def enclosingRadiusValue (A : Set X) (x : X) : ℝ :=
  ⨆ a : A, dist x (a : X)

def isCircumcenterType := ∀ {X : Type*} [MetricSpace X], Set X → X → Prop

def isCircumcenterValue (A : Set X) (c : X) : Prop :=
  ∀ x : X, enclosingRadiusValue A c ≤ enclosingRadiusValue A x

def circumcenterType :=
  ∀ {X : Type*} [MetricSpace X] (A : Set X), A.Nonempty → X

noncomputable def circumcenterValue (A : Set X) (hA : A.Nonempty) : X := by
  classical
  exact if h : ∃ c, isCircumcenterValue A c then Classical.choose h else Classical.choose hA

def enclosingRadiusSqType :=
  ∀ {X : Type*} [MetricSpace X] {A : Set X}, A.Nonempty → IsBounded A → ∀ x : X,
    enclosingRadiusValue A x ^ 2 = ⨆ a : A, dist x (a : X) ^ 2

def existsUniqueCircumcenterType :=
  ∀ {X : Type*} [MetricSpace X] {A : Set X} [CompleteSpace X], cat0Value X →
    A.Nonempty → IsBounded A → ∃! c, isCircumcenterValue A c

def isCircumcenterCircumcenterType :=
  ∀ {X : Type*} [MetricSpace X] {A : Set X} [CompleteSpace X], cat0Value X →
    ∀ (hA : A.Nonempty), IsBounded A →
      isCircumcenterValue A (circumcenterValue A hA)

def circumcenterFixedType :=
  ∀ {X : Type*} [MetricSpace X] {A : Set X} [CompleteSpace X], cat0Value X →
    ∀ (hA : A.Nonempty), IsBounded A →
      ∀ {g : X → X}, Isometry g → g '' A = A →
        g (circumcenterValue A hA) = circumcenterValue A hA

def projectionSqSupType :=
  ∀ {X : Type*} [MetricSpace X] {A C : Set X} [CompleteSpace X], cat0Value X →
    A.Nonempty → IsBounded A → A ⊆ C → IsClosed C →
      geodesicConvexValue C → ∀ x : X,
        (⨆ a : A, dist (nearestPointValue C x) (a : X) ^ 2) ≤
          (⨆ a : A, dist x (a : X) ^ 2) - dist x (nearestPointValue C x) ^ 2

def circumcenterMemType :=
  ∀ {X : Type*} [MetricSpace X] {A C : Set X} [CompleteSpace X], cat0Value X →
    ∀ (hA : A.Nonempty), IsBounded A → A ⊆ C →
      IsClosed C → geodesicConvexValue C → circumcenterValue A hA ∈ C

def circumcenterMemCommonMinsetType :=
  ∀ {X : Type*} [MetricSpace X] {A : Set X} [CompleteSpace X], cat0Value X →
    ∀ (hA : A.Nonempty), IsBounded A →
      ∀ {ι : Type*} (f : ι → X ≃ᵢ X), A ⊆ commonMinsetValue f →
        circumcenterValue A hA ∈ commonMinsetValue f

def orbitCircumcenterFixedType :=
  ∀ {X : Type*} [MetricSpace X] {G : Type*} [Group G]
    [MulAction G X] [IsIsometricSMul G X] [CompleteSpace X], cat0Value X →
      ∀ {x : X}, IsBounded (MulAction.orbit G x) →
        circumcenterValue (MulAction.orbit G x) (MulAction.nonempty_orbit x) ∈
          MulAction.fixedPoints G X

def fixedPointsNonemptyOfBoundedOrbitType :=
  ∀ {X : Type*} [MetricSpace X] {G : Type*} [Group G]
    [MulAction G X] [IsIsometricSMul G X] [CompleteSpace X], cat0Value X →
      (∃ x : X, IsBounded (MulAction.orbit G x)) → (MulAction.fixedPoints G X).Nonempty

def fixedPointsNonemptyOfFiniteGroupType :=
  ∀ {X : Type*} [MetricSpace X] {G : Type*} [Group G]
    [MulAction G X] [IsIsometricSMul G X] [CompleteSpace X] [Finite G],
      cat0Value X → (MulAction.fixedPoints G X).Nonempty

def closedConvexFixedPointsType :=
  ∀ {X : Type*} [MetricSpace X] {G : Type*} [Group G]
    [MulAction G X] [IsIsometricSMul G X] [CompleteSpace X], cat0Value X →
      (MulAction.fixedPoints G X).Nonempty →
        IsClosed (MulAction.fixedPoints G X) ∧ geodesicConvexValue (MulAction.fixedPoints G X) ∧
          cat0Value (MulAction.fixedPoints G X) ∧ CompleteSpace (MulAction.fixedPoints G X)

def finiteOrbitCircumcenterMemType :=
  ∀ {X : Type*} [MetricSpace X] {G : Type*} [Group G]
    [MulAction G X] [IsIsometricSMul G X] [CompleteSpace X], cat0Value X →
      ∀ {x : X}, (MulAction.orbit G x).Finite →
        ∀ {ι : Type*} (f : ι → X ≃ᵢ X), MulAction.orbit G x ⊆ commonMinsetValue f →
          circumcenterValue (MulAction.orbit G x) (MulAction.nonempty_orbit x) ∈
            MulAction.fixedPoints G X ∩ commonMinsetValue f

end LinearAlgebraicGroups.Geometry.CircumcenterSpec
