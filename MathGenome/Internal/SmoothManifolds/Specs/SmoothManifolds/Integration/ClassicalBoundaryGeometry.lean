import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.RegularDomains
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.EmbeddedComparison
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Boundary
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.MetricVolume
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Complex.Basic
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.SmoothJordan
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.IndexProperties

/-! Geometric prerequisites for the classical examples at paper.tex 1927–1940.

This independent interface covers genuine differentials, induced Euclidean
metrics and smooth normals, normal-first intrinsic boundary volume and density
including signed endpoints, oriented surface area and boundary comparisons,
and compact planar components with actual positive circle parametrizations,
Jordan-side classification and genuine winding signs.
No normal, sign or parametrization certificate is assumed for the existence results.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology

namespace SmoothManifolds.ClassicalBoundaryData
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData

/-- The standard oriented determinant functional in ambient Euclidean space. -/
def standardAmbientDet (n : ℕ) : (⋀[ℝ]^n (Euclidean n)) →ₗ[ℝ] ℝ :=
  exteriorPower.alternatingMapLinearEquiv (Pi.basisFun ℝ (Fin n)).det

/-- The genuine intrinsic differential expressed in the standard ambient chart.
This condition determines a linear map, rather than an arbitrary identification
of two vector spaces of the same dimension. -/
def IsEuclideanDifferential {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (T : SmoothManifold N .euclidean (Euclidean N)) (j : M → Euclidean N)
    (p : M) (J : TangentSpace S p →ₗ[ℝ] Euclidean N) : Prop :=
  ∃ (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (F : TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N),
    IsDifferential S T j p L ∧ IsChartCoordinates T (j p) (euclideanChart N) F ∧
      J = F.toLinearMap.comp L

/-- Pullback of the Euclidean dot product on the actual intrinsic fibers.
The Pi Banach norm on `Euclidean N` is not used as a Euclidean metric. -/
def euclideanPullback {V : Type*} [AddCommGroup V] [Module ℝ V] {N : ℕ}
    (J : V →ₗ[ℝ] Euclidean N) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun v w => dotProduct (J v) (J w))
    (by intro v w z; simp [add_dotProduct])
    (by intro t v w; simp [smul_dotProduct])
    (by intro v w z; simp [dotProduct_add])
    (by intro t v w; simp [dotProduct_smul])

def dotFunctional {N : ℕ} (v : Euclidean N) : Euclidean N →ₗ[ℝ] ℝ where
  toFun z := dotProduct v z
  map_add' x y := dotProduct_add v x y
  map_smul' t x := dotProduct_smul t v x

/-- Quarter-turn to the geometric left in the standard oriented plane. -/
def rotateLeft (v : Euclidean 2) : Euclidean 2 := ![-v 1, v 0]

/-- The standard real-linear coordinate identification of the actual plane
with the complex plane used for logarithmic-lift winding numbers. -/
def planeComplexEquiv : Euclidean 2 ≃L[ℝ] ℂ :=
  (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv.trans
    Complex.equivRealProdCLM.symm

/-- Area of a pair of intrinsic tangent vectors for the Euclidean pullback
metric, expressed by its Gram determinant. -/
def gramArea {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] Euclidean 3) (u v : V) : ℝ :=
  Real.sqrt (dotProduct (J u) (J u) * dotProduct (J v) (J v) -
    dotProduct (J u) (J v) * dotProduct (J u) (J v))

end SmoothManifolds.ClassicalBoundaryData

namespace Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.EmbeddedData
  _root_.SmoothManifolds.MapClassData _root_.SmoothManifolds.RegularDomainData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.BoundaryConeData
  _root_.SmoothManifolds.BoundaryOrientationData
  _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.MetricVolumeData
  _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.ClassicalBoundaryData

/-- Smooth maps have a unique ambient-coordinate differential. -/
def euclidean_differential_exists_uniqueType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M)
    (T : SmoothManifold N .euclidean (Euclidean N)) (j : M → Euclidean N),
    euclideanChart N ∈ T.smoothStructure.val → IsSmoothMap S T j → ∀ p,
      ∃! J, IsEuclideanDifferential S T j p J

/-- Every embedding, in any codimension and with either boundary model, induces
a positive definite symmetric form on the original intrinsic tangent fiber. -/
def embedded_metric_positiveType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M)
    (T : SmoothManifold N .euclidean (Euclidean N)) (j : M → Euclidean N),
    IsSmoothEmbedding S T j → ∀ p (J : TangentSpace S p →ₗ[ℝ] Euclidean N),
    IsEuclideanDifferential S T j p J →
      Function.Injective J ∧
      (∀ v w, euclideanPullback J v w = euclideanPullback J w v) ∧
      ∀ v, v ≠ 0 → 0 < euclideanPullback J v v

/-- The pointwise pullback is a smooth metric on every canonical realization
of the intrinsic tangent bundle, not just an unrelated existing fiber metric.
Existence of the genuine differential family is established separately. -/
def embedded_metric_existsType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M)
    (T : SmoothManifold N .euclidean (Euclidean N)) (j : M → Euclidean N),
    euclideanChart N ∈ T.smoothStructure.val → IsSmoothEmbedding S T j →
    ∀ (C : CotangentBundle S) (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N),
      (∀ p, IsEuclideanDifferential S T j p (J p)) →
      ∃ g : Metric C, ∀ p, metricForm g p = euclideanPullback (J p)

/-- Full dimensionality identifies the genuine differential with the entire
ambient vector space, including at boundary points and in dimension zero. -/
def regular_domain_tangentType : Prop :=
  ∀ {m : ℕ} {a : ModelKind}
    (T : SmoothManifold m .euclidean (Euclidean m)),
    euclideanChart m ∈ T.smoothStructure.val →
    ∀ (D : Set (Euclidean m)) (S : SmoothManifold m a D),
      IsRegularDomain T D S → ∀ p,
      ∃ J : TangentSpace S p ≃ₗ[ℝ] Euclidean m,
        IsEuclideanDifferential S T Subtype.val p J.toLinearMap

/-- At every actual boundary point, the Euclidean hyperplane is the image of
the differential of the actual boundary inclusion. The unique normal has dot
square one, is perpendicular to precisely that hyperplane, and is the image
of an intrinsic outward vector. Existence is concluded for every regular
domain; none of these conditions is a premise. Bulk dimension one is `n = 0`.
-/
def outward_unit_normal_pointwiseType : Prop :=
  ∀ {n : ℕ} (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1))),
    euclideanChart (n+1) ∈ T.smoothStructure.val →
    ∀ (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) .halfSpace D),
    IsRegularDomain T D S →
    ∃ B : SmoothManifold n .euclidean (intrinsicBoundary S), IsNaturalBoundary S B ∧
      ∀ (p : intrinsicBoundary S)
      (J : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1))
      (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
      IsEuclideanDifferential S T Subtype.val p.val J.toLinearMap →
      IsDifferential B S Subtype.val p K →
      Function.Injective K ∧
      ∃! ν : Euclidean (n+1),
        dotProduct ν ν = 1 ∧ IsOutward S p (J.symm ν) ∧
        LinearMap.range (J.toLinearMap.comp K) =
          LinearMap.ker (dotFunctional ν)

/-- Global pointwise construction, with the differentials and the normal field
all concluded from the original regular-domain hypotheses. Smoothness is supplied by
`regular_domain_normal_field_smooth` and `regular_domain_normals` below. -/
def regular_domain_normal_fieldType : Prop :=
  ∀ {n : ℕ} (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1))),
    euclideanChart (n+1) ∈ T.smoothStructure.val →
    ∀ (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) .halfSpace D),
    IsRegularDomain T D S →
    ∃ (B : SmoothManifold n .euclidean (intrinsicBoundary S))
      (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean (n+1))
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (ν : intrinsicBoundary S → Euclidean (n+1)),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      ∀ p, IsDifferential B S Subtype.val p (K p) ∧
        dotProduct (ν p) (ν p) = 1 ∧ IsOutward S p ((J p.val).symm (ν p)) ∧
        LinearMap.range ((J p.val).toLinearMap.comp (K p)) =
          LinearMap.ker (dotFunctional (ν p))

/-- For every oriented embedded surface, at every point, a compatible unit
normal works simultaneously for every positive ordered tangent frame. The
Gram area is the norm of the actual intrinsic exterior determinant for the
Euclidean pullback bilinear form. No compactness or interior-point hypothesis
is imposed, so this includes noncompact surfaces and their boundary points.
The global smooth metric-volume and normal construction is stated below.
-/
def surface_normal_pointwiseType : Prop :=
  ∀ {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold 2 a M)
    (T : SmoothManifold 3 .euclidean (Euclidean 3)) (j : M → Euclidean 3),
    IsSmoothEmbedding S T j → ∀ (o : Orientation S) (p : M)
    (J : TangentSpace S p →ₗ[ℝ] Euclidean 3),
    IsEuclideanDifferential S T j p J →
    ∃ ν : Euclidean 3, dotProduct ν ν = 1 ∧
      (∀ w, dotProduct ν (J w) = 0) ∧
      ∀ u v, IsPositive (o.val p) (exteriorPower.ιMulti ℝ 2 ![u, v]) →
        crossProduct (J u) (J v) = gramArea J u v • ν ∧
        0 < gramArea J u v ∧
        gramArea J u v = Real.sqrt ((euclideanPullback J).exteriorPower 2
          (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![u, v]))

/-- The induced metric and its actual smooth intrinsic volume form exist, and
their positive-frame evaluations are precisely the Euclidean Gram areas in
the normal/cross-product formula. The normal field is constructed globally
pointwise in this staging result; the subsequent targets include its smoothness
and the actual surface boundary direction.
-/
def surface_metric_volumeType : Prop :=
  ∀ {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold 2 a M)
    (T : SmoothManifold 3 .euclidean (Euclidean 3)) (j : M → Euclidean 3),
    euclideanChart 3 ∈ T.smoothStructure.val → IsSmoothEmbedding S T j →
    ∀ (o : Orientation S) (C : CotangentBundle S) (A : FormBundle C 2),
    ∃ (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 3)
      (g : Metric C) (ω : Form A) (ν : M → Euclidean 3),
      (∀ p, IsEuclideanDifferential S T j p (J p)) ∧
      (∀ p, metricForm g p = euclideanPullback (J p)) ∧ IsMetricVolume g o ω ∧
      ∀ p, dotProduct (ν p) (ν p) = 1 ∧ (∀ w, dotProduct (ν p) (J p w) = 0) ∧
        ∀ u v, IsPositive (o.val p) (exteriorPower.ιMulti ℝ 2 ![u, v]) →
          pairing p (ω.field p) (exteriorPower.ιMulti ℝ 2 ![u, v]) = gramArea (J p) u v ∧
          crossProduct (J p u) (J p v) =
            pairing p (ω.field p) (exteriorPower.ιMulti ℝ 2 ![u, v]) • ν p

/-- Every regular domain has a smooth Euclidean outward unit normal along its
actual natural boundary, with genuine ambient and boundary differentials. -/
def regular_domain_normal_field_smoothType : Prop :=
  ∀ {n : ℕ} (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1))),
    euclideanChart (n+1) ∈ T.smoothStructure.val →
    ∀ (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) .halfSpace D),
    IsRegularDomain T D S →
    ∃ (B : SmoothManifold n .euclidean (intrinsicBoundary S))
      (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean (n+1))
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (ν : intrinsicBoundary S → Euclidean (n+1)),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      FrameData.VectorSmooth B.smoothStructure.val ν ∧
      ∀ p, IsDifferential B S Subtype.val p (K p) ∧
        dotProduct (ν p) (ν p) = 1 ∧ IsOutward S p ((J p.val).symm (ν p)) ∧
        LinearMap.range ((J p.val).toLinearMap.comp (K p)) =
          LinearMap.ker (dotFunctional (ν p))

/-- Full smooth compatible Euclidean surface normal and induced metric volume.
The alternating cross/volume identity holds on every ordered pair; positivity
identifies its coefficient with the positive Gram area. -/
def surface_geometryType : Prop :=
  ∀ {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold 2 a M)
    (T : SmoothManifold 3 .euclidean (Euclidean 3)) (j : M → Euclidean 3),
    euclideanChart 3 ∈ T.smoothStructure.val → IsSmoothEmbedding S T j →
    ∀ (o : Orientation S) (C : CotangentBundle S) (A : FormBundle C 2),
    ∃ (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 3)
      (g : Metric C) (ω : Form A) (ν : M → Euclidean 3),
      (∀ p, IsEuclideanDifferential S T j p (J p)) ∧
      (∀ p, metricForm g p = euclideanPullback (J p)) ∧ IsMetricVolume g o ω ∧
      FrameData.VectorSmooth S.smoothStructure.val ν ∧
      (∀ p, dotProduct (ν p) (ν p) = 1 ∧ ∀ w, dotProduct (ν p) (J p w) = 0) ∧
      (∀ p u v, crossProduct (J p u) (J p v) =
        pairing p (ω.field p) (exteriorPower.ιMulti ℝ 2 ![u, v]) • ν p) ∧
      ∀ p u v, IsPositive (o.val p) (exteriorPower.ιMulti ℝ 2 ![u, v]) →
        pairing p (ω.field p) (exteriorPower.ιMulti ℝ 2 ![u, v]) = gramArea (J p) u v

def surface_boundary_directionType : Prop :=
  ∀ {a : ModelKind} {M : Type} [TopologicalSpace M] (S : SmoothManifold 2 a M)
    (T : SmoothManifold 3 .euclidean (Euclidean 3)) (j : M → Euclidean 3),
    euclideanChart 3 ∈ T.smoothStructure.val → IsSmoothEmbedding S T j →
    ∀ (o : Orientation S) (C : CotangentBundle S) (A : FormBundle C 2),
    ∃ (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) (b : Orientation B)
      (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 3)
      (g : Metric C) (ω : Form A) (ν : M → Euclidean 3),
      IsNaturalBoundary S B ∧ IsInducedOrientation o b ∧
      (∀ p, IsEuclideanDifferential S T j p (J p)) ∧
      (∀ p, metricForm g p = euclideanPullback (J p)) ∧ IsMetricVolume g o ω ∧
      _root_.SmoothManifolds.FrameData.VectorSmooth S.smoothStructure.val ν ∧
      (∀ p, dotProduct (ν p) (ν p) = 1 ∧ ∀ v, dotProduct (ν p) (J p v) = 0) ∧
      ∀ (p : intrinsicBoundary S)
        (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
        IsDifferential B S Subtype.val p K →
        ∀ u, IsOutward S p u → ∀ w,
          (IsPositive (b.val p) (exteriorPower.ιMulti ℝ 1 ![w]) ↔
            0 < dotProduct (ν p.val) (crossProduct (J p.val u) (J p.val (K w))))

/-- An ambient Euclidean unit conormal exists inside the actual surface tangent
plane. Its preimage is intrinsically outward, and it is perpendicular to the
actual differential image of the boundary. -/
def surface_unit_conormalType : Prop :=
  ∀ {M : Type} [TopologicalSpace M] (S : SmoothManifold 2 .halfSpace M)
    (T : SmoothManifold 3 .euclidean (Euclidean 3)) (j : M → Euclidean 3),
    IsSmoothEmbedding S T j →
    ∀ (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)), IsNaturalBoundary S B →
    ∀ (p : intrinsicBoundary S)
      (J : TangentSpace S p.val →ₗ[ℝ] Euclidean 3)
      (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
      IsEuclideanDifferential S T j p.val J → IsDifferential B S Subtype.val p K →
      ∃ μ : TangentSpace S p.val, IsOutward S p μ ∧ dotProduct (J μ) (J μ) = 1 ∧
        ∀ v, dotProduct (J μ) (J (K v)) = 0

/-- Genuine full-dimensional embedding differentials construct the standard
ambient orientation, including at boundary points. -/
def regular_domain_standard_orientationType : Prop :=
  ∀ {m : ℕ} {a : ModelKind} (T : SmoothManifold m .euclidean (Euclidean m)),
    euclideanChart m ∈ T.smoothStructure.val →
    ∀ (D : Set (Euclidean m)) (S : SmoothManifold m a D),
    IsRegularDomain T D S →
    ∃ (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean m) (o : Orientation S),
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      ∀ p (η : DeterminantLine S p), IsPositive (o.val p) η ↔
        0 < standardAmbientDet m (exteriorPower.map m (J p).toLinearMap η)

/-- Smooth outward normals for either uniform model. Euclidean-model manifolds
have the actual empty intrinsic boundary, so the empty case is retained. -/
def regular_domain_normalsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1))),
    euclideanChart (n+1) ∈ T.smoothStructure.val →
    ∀ (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a D),
    IsRegularDomain T D S →
    ∃ (B : SmoothManifold n .euclidean (intrinsicBoundary S))
      (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean (n+1))
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (ν : intrinsicBoundary S → Euclidean (n+1)),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      FrameData.VectorSmooth B.smoothStructure.val ν ∧
      ∀ p, IsDifferential B S Subtype.val p (K p) ∧
        dotProduct (ν p) (ν p) = 1 ∧ IsOutward S p ((J p.val).symm (ν p)) ∧
        LinearMap.range ((J p.val).toLinearMap.comp (K p)) =
          LinearMap.ker (dotFunctional (ν p))

/- Signed endpoint evaluation for the actual positive standard interval,
with unsigned Euclidean boundary density one. -/
set_option maxHeartbeats 1600000 in
def interval_metric_signType : Prop :=
  ∀ a b : ℝ, a < b →
    ∃ S : SmoothManifold 1 .halfSpace (Set.Icc a b),
    ∃ l r : ModelChart 1 .halfSpace (Set.Icc a b),
      IsStandardInterval a b S l r ∧
      intrinsicBoundary S = {x | x.val = a ∨ x.val = b} ∧
      ∃ (o : Orientation S) (s : SignedCharts S),
        RepresentsSignedCharts o.val s ∧
        (∀ (hl : l ∈ S.smoothStructure.val) p, s.sign l hl p = true) ∧
        (∀ (hr : r ∈ S.smoothStructure.val) p, s.sign r hr p = false) ∧
        ∃ (B : SmoothManifold 0 .euclidean (intrinsicBoundary S)) (q : Orientation B),
          IsNaturalBoundary S B ∧ IsInducedOrientation o q ∧
          (∀ p : intrinsicBoundary S,
            (IsPositive (q.val p)
              ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1) ↔ p.val.val = b) ∧
            (IsPositive (q.val p)
              (-((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1)) ↔ p.val.val = a)) ∧
          ∀ (C : CotangentBundle B) (A : FormBundle C 0) (g : Metric C),
            ∃ (ω : Form A) (ρ : DensityField B),
              IsMetricVolume g q ω ∧ IsMetricDensity g ρ ∧ IsSmoothDensity ρ ∧
              ∀ p : intrinsicBoundary S,
                pairing p (ω.field p)
                  ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1) =
                    (if p.val.val = a then -1 else 1) ∧
                (ρ p).val ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1) = 1

/-- The boundary metric is the pullback of the actual ambient dot product.
Its intrinsic smooth metric density is the absolute determinant obtained by
inserting the actual outward unit normal first, in every dimension. -/
def regular_domain_boundary_densityType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1))),
    euclideanChart (n+1) ∈ T.smoothStructure.val →
    ∀ (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a D),
    IsRegularDomain T D S →
    ∃ (B : SmoothManifold n .euclidean (intrinsicBoundary S))
      (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean (n+1))
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (ν : intrinsicBoundary S → Euclidean (n+1)),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      FrameData.VectorSmooth B.smoothStructure.val ν ∧
      (∀ p, IsDifferential B S Subtype.val p (K p) ∧
        dotProduct (ν p) (ν p) = 1 ∧ IsOutward S p ((J p.val).symm (ν p)) ∧
        LinearMap.range ((J p.val).toLinearMap.comp (K p)) =
          LinearMap.ker (dotFunctional (ν p))) ∧
      ∀ C : CotangentBundle B, ∃ (g : Metric C) (ρ : DensityField B),
        (∀ p, metricForm g p = euclideanPullback ((J p.val).toLinearMap.comp (K p))) ∧
        IsMetricDensity g ρ ∧ IsSmoothDensity ρ ∧ IsPositiveDensity ρ ∧
        (∀ p, ρ p ≠ 0) ∧
        (∀ p (v : Fin n → TangentSpace B p),
          (ρ p).val (exteriorPower.ιMulti ℝ n v) =
            |(Matrix.of (Fin.cons (ν p) (fun i => J p.val (K p (v i))))).det|) ∧
        (∀ hn : n = 0, ∀ p, (ρ p).val
          (castExterior hn.symm ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1)) = 1)

/-- The complete Euclidean boundary metric/normal/volume comparison, including
empty boundaries and signed zero-dimensional endpoints. The standard bulk and
actual outward-first boundary orientations are constructed from the hypotheses. -/
def regular_domain_boundary_geometryType : Prop :=
  ∀ {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1))),
    euclideanChart (n+1) ∈ T.smoothStructure.val →
    ∀ (D : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a D),
    IsRegularDomain T D S →
    ∃ (B : SmoothManifold n .euclidean (intrinsicBoundary S))
      (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean (n+1))
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (ν : intrinsicBoundary S → Euclidean (n+1)) (o : Orientation S) (b : Orientation B),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      FrameData.VectorSmooth B.smoothStructure.val ν ∧
      (∀ p (η : DeterminantLine S p), IsPositive (o.val p) η ↔
        0 < standardAmbientDet (n+1) (exteriorPower.map (n+1) (J p).toLinearMap η)) ∧
      IsInducedOrientation o b ∧
      (∀ p, IsDifferential B S Subtype.val p (K p) ∧
        dotProduct (ν p) (ν p) = 1 ∧ IsOutward S p ((J p.val).symm (ν p)) ∧
        LinearMap.range ((J p.val).toLinearMap.comp (K p)) =
          LinearMap.ker (dotFunctional (ν p))) ∧
      ∀ (C : CotangentBundle B) (A : FormBundle C n),
        ∃ (g : Metric C) (ω : Form A) (ρ : DensityField B),
          (∀ p, metricForm g p = euclideanPullback ((J p.val).toLinearMap.comp (K p))) ∧
          IsMetricVolume g b ω ∧ IsMetricDensity g ρ ∧
          IsSmoothDensity ρ ∧ IsPositiveDensity ρ ∧ (∀ p, ρ p ≠ 0) ∧
          (∀ p (v : Fin n → TangentSpace B p),
            pairing p (ω.field p) (exteriorPower.ιMulti ℝ n v) =
              (Matrix.of (Fin.cons (ν p) (fun i => J p.val (K p (v i))))).det ∧
            (ρ p).val (exteriorPower.ιMulti ℝ n v) =
              |(Matrix.of (Fin.cons (ν p) (fun i => J p.val (K p (v i))))).det|) ∧
          (∀ hn : n = 0, ∀ p,
            let one := castExterior hn.symm
              ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1)
            pairing p (ω.field p) one = ν p 0 ∧ (ρ p).val one = 1)

/-- A positive actual induced boundary tangent has actual interior points on
its geometric left, and this property characterizes positivity. This is a
local geometric bridge, valid without compactness; the compact global
classification is stated in `compact_planar_boundary_componentsType` below. -/
def planar_boundary_leftType : Prop :=
  ∀ {a : ModelKind} (T : SmoothManifold 2 .euclidean (Euclidean 2)),
    euclideanChart 2 ∈ T.smoothStructure.val →
    ∀ (D : Set (Euclidean 2)) (S : SmoothManifold 2 a D),
    IsRegularDomain T D S →
    ∃ (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
      (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean 2)
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (o : Orientation S) (b : Orientation B),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      (∀ p (η : DeterminantLine S p), IsPositive (o.val p) η ↔
        0 < standardAmbientDet 2 (exteriorPower.map 2 (J p).toLinearMap η)) ∧
      IsInducedOrientation o b ∧
      ∀ p, IsDifferential B S Subtype.val p (K p) ∧ ∀ w,
        (IsPositive (b.val p) (exteriorPower.ιMulti ℝ 1 ![w]) ↔
          ∀ᶠ t in 𝓝[>] (0 : ℝ),
            p.val.val + t • rotateLeft (J p.val (K p w)) ∈ interior D)

open Specs.D13Unified.Ch21.Collar
open Specs.D13Unified.Ch21.SmoothJordan
open Specs.D13Unified.Ch21.IndexProperties (index circleLoop)

/-- Every actual component of a compact smooth planar boundary admits a
regular embedded circle parametrization following the intrinsic induced
orientation. Its individual curve separates the plane into actual bounded and
unbounded regions. "Outer" means the domain locally occupies the closure of
that bounded region; "inner" means it locally occupies the closure of the
unbounded region. The genuine logarithmic-lift winding index is respectively
+1 and -1 on the bounded region, and is zero on the unbounded region.
The neighborhood equalities retain disconnected domains and nested islands.
All representation data and parametrizations are concluded from the original
regular-domain hypotheses, including the empty-boundary case. -/
def compact_planar_boundary_componentsType : Prop :=
  ∀ {a : ModelKind} (T : SmoothManifold 2 .euclidean (Euclidean 2)),
    euclideanChart 2 ∈ T.smoothStructure.val →
    ∀ (D : Set (Euclidean 2)) (S : SmoothManifold 2 a D),
    IsRegularDomain T D S → IsCompact D →
    ∃ (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
      (J : (p : D) → TangentSpace S p ≃ₗ[ℝ] Euclidean 2)
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (o : Orientation S) (b : Orientation B),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      (∀ p (η : DeterminantLine S p), IsPositive (o.val p) η ↔
        0 < standardAmbientDet 2 (exteriorPower.map 2 (J p).toLinearMap η)) ∧
      IsInducedOrientation o b ∧
      (∀ p, IsDifferential B S Subtype.val p (K p)) ∧
      ∀ p : intrinsicBoundary S,
        ∃ (γ : Circle → ℂ) (hγ : RegularEmbeddedLoop γ),
          Set.range γ = planeComplexEquiv ''
            ((fun q : intrinsicBoundary S => q.val.val) '' connectedComponent p) ∧
          (∀ t : ℝ, ∃ (q : intrinsicBoundary S) (w : TangentSpace B q) (r : ℝ),
            q ∈ connectedComponent p ∧ realLift γ t = planeComplexEquiv q.val.val ∧
            0 < r ∧ HasDerivAt (realLift γ)
              (r • planeComplexEquiv (J q.val (K q w))) t ∧
            IsPositive (b.val q) (exteriorPower.ιMulti ℝ 1 ![w])) ∧
          ∃ Ω E N : Set ℂ,
            TwoComponents (Set.range γ)ᶜ Ω E ∧
            IsOpen Ω ∧ IsOpen E ∧ IsPathConnected Ω ∧ IsPathConnected E ∧
            Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded E ∧
            frontier Ω = Set.range γ ∧ frontier E = Set.range γ ∧
            IsOpen N ∧ Set.range γ ⊆ N ∧
            (∀ z ∈ E, index (circleLoop (regularLoopMap γ hγ)) z = 0) ∧
            (((planeComplexEquiv '' D) ∩ N = N ∩ closure Ω ∧
                ∀ z ∈ Ω, index (circleLoop (regularLoopMap γ hγ)) z = 1) ∨
             ((planeComplexEquiv '' D) ∩ N = N ∩ closure E ∧
                ∀ z ∈ Ω, index (circleLoop (regularLoopMap γ hγ)) z = -1))

end Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry
