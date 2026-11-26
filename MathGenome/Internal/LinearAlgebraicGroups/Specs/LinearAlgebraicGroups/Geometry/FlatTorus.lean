import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Geometry.CAT0Spaces
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Group.Quotient

namespace LinearAlgebraicGroups.Geometry.FlatTorusSpec

open CAT0SpacesSpec
open Set

universe u v

/-- The local ball formulation of properness from the flats section gives the
compact-set condition used for the action. -/
def properActionOfLocalType :=
  ∀ {A : Type v} {X : Type u} [Group A] [MetricSpace X] [MulAction A X]
    [IsIsometricSMul A X],
    (∀ x : X, ∃ δ : ℝ, 0 < δ ∧
      {a : A | ∃ z ∈ Metric.ball x δ, a • z ∈ Metric.ball x δ}.Finite) →
    isProperActionValue A X

/-- The flat torus theorem, including the orbit relation and the quotient distance on each
Euclidean slice. The integral span of a real basis is the full translation lattice. -/
def flatTorusType :=
  ∀ {A : Type v} {X : Type u} [Group A] [MetricSpace X] [CompleteSpace X]
    [MulAction A X] [IsIsometricSMul A X] (r : ℕ),
    Nonempty (A ≃* Multiplicative (Fin r → ℤ)) →
    cat0Value X → isProperActionValue A X →
    (∀ a : A, isSemisimpleValue (IsometryEquiv.constSMul a : X ≃ᵢ X)) →
    (actionMinsetValue A X).Nonempty ∧
    ∃ (Y : Type u) (_ : MetricSpace Y),
      cat0Value Y ∧ CompleteSpace Y ∧
      ∃ (e : euclideanProductValue Y (EuclideanSpace ℝ (Fin r)) ≃ᵢ actionMinsetValue A X)
        (τ : A →* Multiplicative (EuclideanSpace ℝ (Fin r)))
        (b : Module.Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))),
        Function.Injective τ ∧
        (∀ (a : A) (y : Y) (x : EuclideanSpace ℝ (Fin r)),
          a • (e (WithLp.toLp 2 (y, x)) : X) =
            (e (WithLp.toLp 2 (y, x + (τ a).toAdd)) : X)) ∧
        let L := (Submodule.span ℤ (range b)).toAddSubgroup
        range (fun a => (τ a).toAdd) = (L : Set (EuclideanSpace ℝ (Fin r))) ∧
        DiscreteTopology L ∧
        letI : IsClosed (L : Set (EuclideanSpace ℝ (Fin r))) :=
          AddSubgroup.isClosed_of_discreteTopology
        let q := QuotientAddGroup.mk' L
        CompactSpace (EuclideanSpace ℝ (Fin r) ⧸ L) ∧
        ∀ (y : Y) (x x' : EuclideanSpace ℝ (Fin r)),
          (q x = q x' ↔ ∃ a : A, a • (e (WithLp.toLp 2 (y, x')) : X) =
            (e (WithLp.toLp 2 (y, x)) : X)) ∧
          dist (q x) (q x') =
            ⨅ a : A, dist (e (WithLp.toLp 2 (y, x)) : X)
              (a • (e (WithLp.toLp 2 (y, x')) : X))

/-- A geometric action of a group containing a copy of the rank-two integer lattice
gives an isometric Euclidean plane. -/
def geometricActionPlaneType :=
  ∀ {G : Type v} {X : Type u} [Group G] [MetricSpace X] [MulAction G X],
    isGeometricActionValue G X → cat0Value X →
    ∀ i : Multiplicative (Fin 2 → ℤ) →* G, Function.Injective i →
      ∃ f : euclideanPlaneValue → X, Isometry f

end LinearAlgebraicGroups.Geometry.FlatTorusSpec
