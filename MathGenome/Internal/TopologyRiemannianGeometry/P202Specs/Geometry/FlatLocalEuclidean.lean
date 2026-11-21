import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurvatureAlgebra

/-! Independent statement of Theorem 7.3 (`thm:p202-flat`, paper.tex
3668–3715), under the conventions at paper.tex 84–98.

A Euclidean chart is an actual open partial homeomorphism in the given maximal
smooth atlas, whose *intrinsic coordinate differential* pulls back the standard
Euclidean dot product to g on its entire source. In particular its source and
target are open and its inverse is smooth. This is a local diffeomorphism and
metric preservation, rather than merely a tangent-space isometry. The coordinate
maps below are fixed by `FiberCoordinates.isCoordinates`, hence are evaluations
on the actual coordinate germs. No auxiliary frame is part of the conclusion.
All statements allow n = 0 and empty open sets. -/
set_option autoImplicit false

namespace P202.FlatData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurvatureData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Pointwise vanishing of the actual trilinear curvature tensor. -/
def FlatOn (R : CurvatureTensor S) (U : Set M) : Prop :=
  ∀ p ∈ U, ∀ v w z : TangentSpace S p, R.val p v w z = 0

/-- A smooth chart which is an isometry to its Euclidean open target, with
standard metric ∑ᵢ dxᵢ². Smoothness in both directions is atlas membership. -/
def IsEuclideanChart (g : RiemannianMetric S)
    (c : ModelChart n .euclidean M) : Prop :=
  ∃ hc : c ∈ S.smoothStructure.val,
    ∀ (p : M) (hp : p ∈ c.source) (v w : TangentSpace S p),
      pairing g p v w = ∑ i : Fin n,
        ((tangentStructure S).fiberCoordinates.equiv c hc p hp v) i *
          ((tangentStructure S).fiberCoordinates.equiv c hc p hp w) i

/-- Every point has an isometric chart with its whole source inside U. -/
def LocallyEuclideanOn (g : RiemannianMetric S) (U : Set M) : Prop :=
  ∀ p ∈ U, ∃ c : ModelChart n .euclidean M,
    p ∈ c.source ∧ c.source ⊆ U ∧ IsEuclideanChart g c

end P202.FlatData

namespace P202Specs.Geometry.FlatLocalEuclidean
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.CurvatureData
  P202.FlatData P202.TorsionMetricData
universe u

/-- Full original equivalence, with every representing curvature tensor and
every Levi–Civita connection; no extra existence assumptions on the manifold. -/
def flat_iff_locallyEuclideanType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ U : Set M, IsOpen U → (FlatOn R U ↔ LocallyEuclideanOn g U)

/-- The Euclidean direction is valid on any union of isometric chart sources. -/
def flat_of_locallyEuclideanType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ U : Set M, LocallyEuclideanOn g U → FlatOn R U

/-- Integrating commuting orthonormal fields gives an actual isometric chart.
The fields are global representatives; only their behavior on U is used. -/
def chart_of_commuting_orthonormalType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (U : Set M) (hU : IsOpen U) (p : M), p ∈ U →
    ∀ e : Fin n → Field S,
      (∀ q ∈ U, ∀ i j : Fin n,
        pairing g q ((e i).val q) ((e j).val q) = if i = j then 1 else 0) →
      (∀ i j q, q ∈ U → (bracket (e i) (e j)).val q = 0) →
      ∃ c : ModelChart n .euclidean M,
        p ∈ c.source ∧ c.source ⊆ U ∧ IsEuclideanChart g c

/-- In dimension zero every metric is flat and has isometric charts. -/
def zero_dimensionalType : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 .euclidean M} (g : RiemannianMetric S)
    (R : CurvatureTensor S) (U : Set M), IsOpen U →
      FlatOn R U ∧ LocallyEuclideanOn g U

end P202Specs.Geometry.FlatLocalEuclidean
