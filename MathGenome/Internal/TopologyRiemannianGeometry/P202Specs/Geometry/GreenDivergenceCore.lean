import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GreenBoundaryFlux
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorDerivative
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.ClassicalFormulas
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.Stokes

/-! Independent obligations for the divergence core of paper.tex 3246–3294.
No orientation is imposed on the density theorem. The oriented realization uses
actual Cartan contraction and exterior differentiation on the fixed tangent fibers.
The full density and oriented identities are stated independently of their proofs. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology CompactlySupported
namespace P202Specs.Geometry.GreenDivergenceCore
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.BoundaryData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData P202.GreenData
universe u

/-- Stronger compact-support version: it also covers noncompact manifolds with
boundary. No orientability, connectedness or positive dimension is assumed. -/
def divergence_theoremType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ b : BoundaryGeometry g, DivergenceIdentity g C b

/-- The oriented realization uses the actual contraction, derivative,
outward-first boundary orientation, pullback by the inclusion differential,
and the existing coordinate-compatible integrals. The last equalities identify
them with the density integrals, with the flux sign fixed by the unit normal. -/
def oriented_stokesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (b : BoundaryGeometry g) (o : SmoothManifolds.OrientationData.Orientation S)
    (X : Field S), IsCompact (sectionSupport X.val) →
    ∃ q : SmoothManifolds.OrientationData.Orientation b.manifold,
      SmoothManifolds.BoundaryOrientationData.IsInducedOrientation o q ∧
    let ω := SmoothManifolds.CartanData.contraction (P202.VolumeData.cotangentBundle S)
      X.val (n+1) (P202.VolumeData.volumeForm g o).field
    SmoothManifolds.ExteriorDerivativeData.IsRegularField
      (P202.VolumeData.cotangentBundle S) 1 n ω ∧
    IsCompact (sectionSupport ω) ∧
    ∃ (η : SmoothManifolds.LocalIntegrationData.CompactTopForm S)
      (β : SmoothManifolds.LocalIntegrationData.CompactTopForm b.manifold)
      (F : C_c(M, ℝ)) (Q : C_c(intrinsicBoundary S, ℝ)),
      SmoothManifolds.ExteriorDerivativeData.HasExteriorDerivative
        (P202.VolumeData.cotangentBundle S) ω η.field ∧
      η.field = (fun p => divergence C X p • (P202.VolumeData.volumeForm g o).field p) ∧
      β.field = SmoothManifolds.FormPullbackData.pullbackField b.manifold S Subtype.val
        (SmoothManifolds.differential b.manifold S Subtype.val b.natural.1) ω ∧
      β.field = (fun p => flux g b X p • (P202.VolumeData.volumeForm b.metric q).field p) ∧
      (∀ p, F p = divergence C X p) ∧ (∀ p, Q p = flux g b X p) ∧
      ∀ (I : SmoothManifolds.LocalIntegrationData.CompactTopForm S → ℝ)
        (J : SmoothManifolds.LocalIntegrationData.CompactTopForm b.manifold → ℝ),
        SmoothManifolds.GlobalIntegrationData.IsIntegral o I →
        SmoothManifolds.GlobalIntegrationData.IsIntegral q J →
        I η = J β ∧ I η = P202.VolumeData.integral g F ∧
          J β = P202.VolumeData.integral b.metric Q

def divergence_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S)) (X : Field S) (p : M),
    SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val (divergence C X) p

def divergence_supportType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S)) (X : Field S),
    sectionSupport (divergence C X) ⊆ sectionSupport X.val

def flux_continuousType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (b : BoundaryGeometry g)
    (X : Field S), Continuous (flux g b X)

def flux_supportType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (b : BoundaryGeometry g)
    (X : Field S), sectionSupport (flux g b X) ⊆ Subtype.val ⁻¹' sectionSupport X.val


/-- The pointwise differential identity required before applying Stokes. -/
def contraction_derivativeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (o : SmoothManifolds.OrientationData.Orientation S) (X : Field S),
    SmoothManifolds.ExteriorDerivativeData.HasExteriorDerivative
      (P202.VolumeData.cotangentBundle S)
      (SmoothManifolds.CartanData.contraction (P202.VolumeData.cotangentBundle S)
        X.val (n+1) (P202.VolumeData.volumeForm g o).field)
      (fun p => divergence C X p • (P202.VolumeData.volumeForm g o).field p)

/-- Contraction has C¹ coefficient extensions and compact closed support. -/
def contraction_regular_compactType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) a M} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S) (X : Field S),
    IsCompact (sectionSupport X.val) →
    let ω := SmoothManifolds.CartanData.contraction (P202.VolumeData.cotangentBundle S)
      X.val (n+1) (P202.VolumeData.volumeForm g o).field
    SmoothManifolds.ExteriorDerivativeData.IsRegularField
      (P202.VolumeData.cotangentBundle S) 1 n ω ∧ IsCompact (sectionSupport ω)

/-- The zero-dimensional theorem, with no chosen unit vector. -/
def divergence_zero_dimensionType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (b : BoundaryGeometry g), DivergenceIdentity g C b

/-- Reduction from the pointwise differential identity to full oriented Stokes. -/
def oriented_stokes_from_derivativeType : Prop :=
  contraction_derivativeType.{u} → oriented_stokesType.{u}

/-- The chart-supported local density theorem: compact support may meet the true
boundary, but must avoid artificial chart edges. This is an independent obligation,
not a certificate on manifold data. -/
def chart_supported_divergenceType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (b : BoundaryGeometry g) (X : Field S), IsCompact (sectionSupport X.val) →
    ∀ (c : ModelChart n a M), c ∈ S.smoothStructure.val →
    sectionSupport X.val ⊆ c.source →
      IntegralIdentity g b.metric (divergence C X) (flux g b X)

/-- Localization assembles the density theorem from its chart-supported version. -/
def divergence_from_chart_supportedType : Prop :=
  chart_supported_divergenceType.{u} → divergence_theoremType.{u}


/-- Both integrands are constructed in the original compact-density domain,
independently of the equality of their integrals. -/
def divergence_flux_representativesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (b : BoundaryGeometry g) (X : Field S),
    IsCompact (sectionSupport X.val) →
    ∃ (F : C_c(M, ℝ)) (Q : C_c(intrinsicBoundary S, ℝ)),
      (∀ p, F p = divergence C X p) ∧ (∀ p, Q p = flux g b X p)

/-- Finite global decomposition; differentiating it cancels every localizer term. -/
def finite_field_partitionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S)) (X : Field S),
    IsCompact (sectionSupport X.val) →
    ∀ {ι : Type*} (ρ : ι → GlobalSmooth S),
    LocallyFinite (fun i => sectionSupport (ρ i).val) →
    (∀ p, ∑ᶠ i, (ρ i).val p = 1) →
    ∃ t : Finset ι,
      (∀ i ∉ t, mulSection (ρ i) X = 0) ∧
      X = ∑ i ∈ t, mulSection (ρ i) X ∧
      ∀ p, divergence C X p = ∑ i ∈ t, divergence C (mulSection (ρ i) X) p

/-- The Euclidean weighted flux calculation used by the chart proof. -/
def weighted_flux_derivativeType : Prop :=
  ∀ {n : ℕ} (r : Euclidean (n+1) → ℝ)
    (X : Euclidean (n+1) → Euclidean (n+1)) (x : Euclidean (n+1)),
    DifferentiableAt ℝ r x → DifferentiableAt ℝ X x →
    extDeriv (fun y => r y • SmoothManifolds.ClassicalData.fluxForm X y) x =
      (∑ i : Fin (n+1), fderiv ℝ (fun y => r y • X y) x
        (SmoothManifolds.ClassicalData.frame (n+1) i) i) •
        SmoothManifolds.ClassicalData.volume (n+1)


/- Fiberwise transport to the actual coordinate flux form, with determinant
normalization. This does not assume the metric differential identity. -/
section CoordinateFlux
open SmoothManifolds hiding SmoothManifold ModelChart TangentSpace Euclidean modelSet ModelSpace sectionSupport
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.CovectorData SmoothManifolds.ExteriorData
  SmoothManifolds.LocalIntegrationData SmoothManifolds.ClassicalData
  SmoothManifolds.BundleOperationsData SmoothManifolds.FormPullbackData
  SmoothManifolds.VectorFieldData

def contraction_coordinates_fluxType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (n+1) a M}
    (C : CotangentBundle S) (X : VectorFieldData.Section S)
    (σ : ExteriorData.Field S (n+1))
    (c : ModelChart (n+1) a M) (hc : c ∈ S.smoothStructure.val) (p : c.source),
    ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv (n+1) n
      (fun I => coefficients C n c hc (CartanData.contraction C X (n+1) σ) p I) =
    topCoefficient C.tangent.fiberCoordinates c hc p.val p.property σ •
      (volume (n+1)).curryLeft
        (C.tangent.fiberCoordinates.equiv c hc p.val p.property (X p.val))
end CoordinateFlux

end P202Specs.Geometry.GreenDivergenceCore
