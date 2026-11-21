import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GaussWeingarten
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.DivergenceGreen
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Independent data and obligations for Proposition 7.7, paper.tex 3830–3868.
Mean curvature is the metric trace, with no dimension normalization. All
geometric fibers and integrals are the fixed upstream ones. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Topology CompactlySupported Classical

namespace P202.VolumeVariationData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData P202.MetricData P202.ConnectionData P202.ScalarData
universe u v
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- A basis of the actual tangent fiber, selected only to write the contraction.
The implementation proves independence of this selection. -/
def fiberBasis (S : SmoothManifold n a M) (p : M) :
    Module.Basis (Fin n) ℝ (TangentSpace S p) :=
  let c := Classical.choose ((tangentBundle S).covers p)
  let hc := Classical.choose_spec ((tangentBundle S).covers p)
  (Pi.basisFun ℝ (Fin n)).map ((tangentBundle S).fiberCoordinates c p hc).symm

/-- The trace of a vector-valued covariant two-tensor. The second input is
contracted with the metric dual of the first input's dual basis. -/
def vectorMetricTrace {E : Type v} [AddCommGroup E] [Module ℝ E]
    (g : RiemannianMetric S) (p : M)
    (B : TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] E) : E :=
  ∑ j : Fin n, B (fiberBasis S p j)
    ((musical g p).symm ((fiberBasis S p).dualBasis j))

/-- For the normal-valued second fundamental form this is H = tr_g B. -/
def meanCurvature {E : M → Type v} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    (g : RiemannianMetric S)
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] E p)
    (p : M) : E p := vectorMetricTrace g p (B p)

end P202.VolumeVariationData

namespace P202.VolumeVariationData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.DensityIntegrationData
  SmoothManifolds.MetricVolumeData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData
  P202.GreenData
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

/-- Joint smoothness in parameter and source coordinates, using ambient
extensions at genuine boundary points. No extension into the target manifold
across a boundary is required. Values outside the open parameter domain are
irrelevant. This is the ordinary chart definition of a smooth variation. -/
structure SmoothVariation (S : SmoothManifold n a M) (T : SmoothManifold m b N) where
  domain : Set ℝ
  open_domain : IsOpen domain
  zero_mem : (0 : ℝ) ∈ domain
  map : ℝ → M → N
  continuous : ContinuousOn (fun z : ℝ × M => map z.1 z.2) (domain ×ˢ Set.univ)
  immersion : ∀ s ∈ domain, SmoothImmersion S T (map s)
  joint_smooth : ∀ s ∈ domain, ∀ p : M,
    ∃ (c : ModelChart n a M) (_hc : c ∈ S.smoothStructure.val)
      (d : ModelChart m b N) (_hd : d ∈ T.smoothStructure.val),
      p ∈ c.source ∧ map s p ∈ d.source ∧
      ∃ (U : Set (ℝ × Euclidean n)) (f : ℝ × Euclidean n → Euclidean m),
        IsOpen U ∧ (s, (c p).val) ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
        ∀ t ∈ domain, ∀ x : ModelSpace n a,
          (t, x.val) ∈ U → x ∈ c.target →
          map t (c.symm x) ∈ d.source ∧ f (t, x.val) = (d (map t (c.symm x))).val

def initialImmersion (Q : SmoothVariation S T) : SmoothImmersion S T (Q.map 0) :=
  Q.immersion 0 Q.zero_mem

def variationVelocity (Q : SmoothVariation S T) (p : M) : TangentSpace T (Q.map 0 p) :=
  P202.CurveData.velocity T (fun s => Q.map s p) 0

/-- The metric family is identified fiberwise with the actual pullback form.
Existence is a separate unconditional obligation, not extra metric data. -/
def InducedMetrics (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) : Prop :=
  ∀ s (hs : s ∈ Q.domain) p v w,
    pairing (g s) p v w = pairing h (Q.map s p)
      ((Q.immersion s hs).differential p v) ((Q.immersion s hs).differential p w)

/-- The actual ambient-valued second fundamental tensor, characterized by the
normal condition and the Gauss formula in the genuine pullback connection.
Its existence follows from the upstream Gauss–Weingarten theorem. -/
def IsSecondFundamentalForm (h : RiemannianMetric T)
    (F : M → N) (i : SmoothImmersion S T F)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (F p)) : Prop :=
  (∀ p v w z, pairing h (F p) (B p v w) (i.differential p z) = 0) ∧
  ∃ P : PullbackBundle (tangentBundle T) S F,
    letI := P.space.topology
    ∃ D : Connection P.space.bundle,
      P202.PullbackData.IsPullback (tangentBundle T) K F i.smooth P D ∧
      ∀ X Y : Field S, ∃ V : Section P.space.bundle,
        (∀ p, V.val p = i.differential p (Y.val p)) ∧
        ∀ p, (D.cov X V).val p =
          i.differential p ((C.cov X Y).val p) + B p (X.val p) (Y.val p)

def VariationDecomposition (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p)) : Prop :=
  (∀ p, P202.CurveData.HasVelocityAt T (fun s => Q.map s p) 0 (variationVelocity Q p)) ∧
  (∀ p, variationVelocity Q p = (initialImmersion Q).differential p (W.val p) + ξ p) ∧
  ∀ p z, pairing h (Q.map 0 p) (ξ p) ((initialImmersion Q).differential p z) = 0

def normalIntegrand (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : RiemannianMetric S)
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p))
    (ξ : (p : M) → TangentSpace T (Q.map 0 p)) (p : M) : ℝ :=
  pairing h (Q.map 0 p) (ξ p)
    (meanCurvature (E := fun p => TangentSpace T (Q.map 0 p)) g B p)

/-- Coefficient statement of the derivative of the intrinsic density in every
fixed source chart. It is equivalent to dot(dV)=(div W-<ξ,H>)dV. -/
def LocalDensityVariation (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (C : Connection (tangentBundle S))
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p))
    (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p)) : Prop :=
  ∀ (A : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source),
    HasDerivAt (fun s => densityCoefficient A c hc p (P202.VolumeData.density (g s) p.val))
      ((divergence C W p.val - normalIntegrand Q h (g 0) B ξ p.val) *
        densityCoefficient A c hc p (P202.VolumeData.density (g 0) p.val)) 0

/-- Volume of the whole compact source, integrated as a density. -/
def compactVolume [CompactSpace M] (g : RiemannianMetric S) : ℝ :=
  P202.VolumeData.integral g
    ⟨⟨fun _ => 1, continuous_const⟩, HasCompactSupport.of_compactSpace _⟩

/-- A common compact set works for all sufficiently small parameter values. -/
def CompactlySupportedVariation (Q : SmoothVariation S T) : Prop :=
  ∃ L : Set M, IsCompact L ∧ ∀ᶠ s in nhds (0 : ℝ),
    s ∈ Q.domain ∧ ∀ p ∉ L, Q.map s p = Q.map 0 p

/-- The signed density difference is integrated directly. This definition
never subtracts potentially infinite total volumes. The compact-support theorem
below proves that the first branch applies near zero. -/
def localVolumeChange (g : ℝ → RiemannianMetric S) (s : ℝ) : ℝ :=
  if h : ∃ ρ : CompactDensity S,
      ρ.field = fun p => P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p
  then P202.VolumeData.densityIntegral S h.choose else 0

end P202.VolumeVariationData

namespace P202Specs.Geometry.VolumeFirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.ScalarData P202.VolumeVariationData
universe u v

def meanCurvatureType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n a M} → {E : M → Type v} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  (g : RiemannianMetric S) →
  ((p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] E p) → (p : M) → E p

def meanCurvatureValue : meanCurvatureType := @meanCurvature

/-- Pairing a vector-valued metric trace with any covector commutes with
contraction. This characterizes the trace without a chosen frame. -/
def trace_pairingType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {E : Type v} [AddCommGroup E] [Module ℝ E]
    (g : RiemannianMetric S) (p : M)
    (B : TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] E) (φ : E →ₗ[ℝ] ℝ),
    φ (vectorMetricTrace g p B) = metricTrace g p (B.compr₂ φ)

def trace_basis_independentType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {E : Type v} [AddCommGroup E] [Module ℝ E]
    (g : RiemannianMetric S) (p : M)
    (B : TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] E)
    {ι : Type*} [Fintype ι] (e : Module.Basis ι ℝ (TangentSpace S p)),
    vectorMetricTrace g p B = ∑ j, B (e j) ((musical g p).symm (e.dualBasis j))

/-- Jacobi's formula followed by differentiation of the positive square root.
This is a calculus lemma, not an assumed derivative of the induced metric. -/
def sqrt_det_derivativeType : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ℝ → Matrix ι ι ℝ) (D : Matrix ι ι ℝ) (s : ℝ),
    (∀ i j, HasDerivAt (fun t => G t i j) (D i j) s) → 0 < (G s).det →
    HasDerivAt (fun t => Real.sqrt (G t).det)
      ((1 / 2 : ℝ) * Real.sqrt (G s).det * ((G s)⁻¹ * D).trace) s

open SmoothManifolds.ModelData SmoothManifolds.MapData
  SmoothManifolds.TangentBundleData SmoothManifolds.BundleOperationsData
  SmoothManifolds.DensityIntegrationData SmoothManifolds.BoundaryData
  P202.ConnectionData P202.LeviCivitaData P202.GreenData

def induced_metrics_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (Q : SmoothVariation S T) (h : RiemannianMetric T),
    ∃ g : ℝ → RiemannianMetric S, InducedMetrics Q h g

def second_form_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (F : M → N) (i : SmoothImmersion S T F),
    IsMetricPreserving g h F i.differential →
    ∀ (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T)),
      IsLeviCivita g C → IsLeviCivita h K →
      ∃ B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (F p),
        IsSecondFundamentalForm h F i C K B

/-- The actual intrinsic velocity exists from coordinate smoothness. -/
def variation_velocityType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (Q : SmoothVariation S T) (p : M),
    P202.CurveData.HasVelocityAt T (fun s => Q.map s p) 0 (variationVelocity Q p)

/-- A common compact support of the variation also supports its tangential
part; no purely normal hypothesis is used. -/
def decomposition_supportType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S), InducedMetrics Q h g → CompactlySupportedVariation Q →
    ∀ (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p)),
      VariationDecomposition Q h W ξ →
      IsCompact (SmoothManifolds.ModelData.sectionSupport W.val)

def variation_decompositionType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (Q : SmoothVariation S T) (h : RiemannianMetric T),
    ∃ (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p)),
      VariationDecomposition Q h W ξ

/-- Required pointwise density derivative, with the metric and normal
splitting determined by the actual immersion. None of the variation identities
to be proved are hypotheses. -/
def local_densityType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S), InducedMetrics Q h g →
    ∀ (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T)),
      IsLeviCivita (g 0) C → IsLeviCivita h K →
    ∀ (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p)),
      IsSecondFundamentalForm h (Q.map 0) (initialImmersion Q) C K B →
    ∀ (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p)),
      VariationDecomposition Q h W ξ → LocalDensityVariation Q h g C B W ξ

/-- Required compact-manifold formula. The two integrands are actual compact
continuous scalar representatives in the upstream density integral domain. -/
def compact_first_variationType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [CompactSpace M]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S), InducedMetrics Q h g →
    ∀ (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T)),
      IsLeviCivita (g 0) C → IsLeviCivita h K →
    ∀ (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p)),
      IsSecondFundamentalForm h (Q.map 0) (initialImmersion Q) C K B →
    ∀ (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p)),
      VariationDecomposition Q h W ξ →
    ∀ bnd : BoundaryGeometry (g 0),
      ∃ (f : C_c(M, ℝ)) (q : C_c(intrinsicBoundary S, ℝ)),
        (∀ p, f p = normalIntegrand Q h (g 0) B ξ p) ∧
        (∀ p, q p = flux (g 0) bnd W p) ∧
        HasDerivAt (fun s => compactVolume (g s))
          (-P202.VolumeData.integral (g 0) f + P202.VolumeData.integral bnd.metric q) 0

/-- Near zero the density difference has a genuine compact representative.
This is needed before its integral can represent a local volume change. -/
def density_difference_compactType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S), InducedMetrics Q h g → CompactlySupportedVariation Q →
    ∀ᶠ s in nhds (0 : ℝ), ∃ ρ : CompactDensity S,
      ρ.field = fun p => P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p

/-- Required noncompact formula for a common compact support. The boundary is
exactly the original intrinsic boundary, not the boundary of a truncation. -/
def supported_first_variationType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S), InducedMetrics Q h g → CompactlySupportedVariation Q →
    ∀ (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T)),
      IsLeviCivita (g 0) C → IsLeviCivita h K →
    ∀ (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p)),
      IsSecondFundamentalForm h (Q.map 0) (initialImmersion Q) C K B →
    ∀ (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p)),
      VariationDecomposition Q h W ξ →
    ∀ bnd : BoundaryGeometry (g 0),
      ∃ (f : C_c(M, ℝ)) (q : C_c(intrinsicBoundary S, ℝ)),
        (∀ p, f p = normalIntegrand Q h (g 0) B ξ p) ∧
        (∀ p, q p = flux (g 0) bnd W p) ∧
        HasDerivAt (localVolumeChange g)
          (-P202.VolumeData.integral (g 0) f + P202.VolumeData.integral bnd.metric q) 0

end P202Specs.Geometry.VolumeFirstVariation
