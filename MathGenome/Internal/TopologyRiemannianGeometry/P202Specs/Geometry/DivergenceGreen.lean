import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GreenDivergenceCore

/-! Independent obligations for Theorem 6.7, paper.tex 3246–3294.
Integrals are the fixed intrinsic compact-density integral. An identity includes
compact continuous representatives of its integrands, rather than silently
assigning a value to an integral of an unverified integrand. No orientation is
required for the density statements. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology CompactlySupported

namespace P202Specs.Geometry.DivergenceGreen
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.BoundaryData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData P202.GreenData
universe u

/-- Retain the full already established differential part of Theorem 6.7. -/
def scalar_calculusType : Prop :=
  ScalarCalculus.gradient_characterizationType.{u} ∧
  ScalarCalculus.hessian_covariantType.{u} ∧
  ScalarCalculus.hessian_formulaType.{u} ∧
  ScalarCalculus.hessian_symmetryType.{u} ∧
  ScalarCalculus.laplacian_traceType.{u} ∧
  ScalarCalculus.gradient_coordinatesType.{u} ∧
  ScalarCalculus.divergence_coordinatesType.{u} ∧
  ScalarCalculus.laplacian_coordinatesType.{u} ∧
  ScalarCalculus.connection_independenceType.{u}

def boundary_geometry_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S), Nonempty (BoundaryGeometry g)

def divergence_productType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S))
    (f : GlobalSmooth S) (X : Field S) (p : M),
    divergence C (mulSection f X) p =
      scalarDerivative S f.val p (X.val p) + f.val p * divergence C X p

def first_integrand_divergenceType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (u v : GlobalSmooth S) (p : M),
    divergence C (mulSection v (gradient g u)) p = firstIntegrand g C u v p

/-- Stronger compact-support version: it also covers noncompact manifolds with
boundary. No orientability, connectedness or positive dimension is assumed. -/
def divergence_theoremType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ b : BoundaryGeometry g, DivergenceIdentity g C b

def divergence_compactType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (b : BoundaryGeometry g) (X : Field S),
      IntegralIdentity g b.metric (divergence C X) (flux g b X)

def green_firstType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (b : BoundaryGeometry g) (u v : GlobalSmooth S),
      IntegralIdentity g b.metric (firstIntegrand g C u v)
        (fun p => v.val p.val * flux g b (gradient g u) p)

def green_secondType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (b : BoundaryGeometry g) (u v : GlobalSmooth S),
      IntegralIdentity g b.metric (secondIntegrand g C u v)
        (fun p => v.val p.val * flux g b (gradient g u) p -
          u.val p.val * flux g b (gradient g v) p)

def divergence_boundarylessType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C → intrinsicBoundary S = ∅ →
    ∀ X : Field S, IsCompact (sectionSupport X.val) → IntegralZero g (divergence C X)

def green_first_boundarylessType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C → intrinsicBoundary S = ∅ →
    ∀ u v : GlobalSmooth S, IsCompact (sectionSupport (mulSection v (gradient g u)).val) →
      IntegralZero g (firstIntegrand g C u v)

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

/-! Supporting calculus and reduction interfaces. The unconditional divergence
and Green obligations are stated above. -/
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

def unit_normal_of_covectorType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (p : M)
    (φ : Module.Dual ℝ (TangentSpace S p)), φ ≠ 0 →
    ∃ ν : TangentSpace S p, pairing g p ν ν = 1 ∧ φ ν < 0 ∧
      ∀ z, φ z = 0 → pairing g p ν z = 0

def boundary_geometry_of_emptyType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S),
    intrinsicBoundary S = ∅ → Nonempty (BoundaryGeometry g)

def divergence_zero_dimensionType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (C : Connection (tangentBundle S)) (X : Field S) (p : M),
    divergence C X p = 0

def divergence_identity_zero_dimensionType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (b : BoundaryGeometry g), DivergenceIdentity g C b

def divergence_compact_reductionType : Prop := divergence_theoremType.{u} → divergence_compactType.{u}
def green_first_reductionType : Prop := divergence_theoremType.{u} → green_firstType.{u}
def green_second_reductionType : Prop := divergence_theoremType.{u} → green_secondType.{u}
def divergence_boundaryless_reductionType : Prop :=
  divergence_theoremType.{u} → divergence_boundarylessType.{u}
def green_first_boundaryless_reductionType : Prop :=
  divergence_theoremType.{u} → green_first_boundarylessType.{u}

end P202Specs.Geometry.DivergenceGreen
