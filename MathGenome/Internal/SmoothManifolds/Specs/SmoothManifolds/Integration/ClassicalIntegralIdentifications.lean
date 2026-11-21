import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.Global
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.MetricVolume
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.ExteriorDerivative
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.EmbeddedComparison
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.RegularDomains

/-! Independent interfaces for classical integration, induced Euclidean metrics,
parametrization factors, endpoint sums and intrinsic C¹ regularity.
No final Green, divergence or Stokes identity is assumed here. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Topology BigOperators

namespace SmoothManifolds.ClassicalIntegralData
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData ExteriorData
  FormPullbackData OrientationData MetricVolumeData LocalIntegrationData Set
universe u

/-- A continuous scalar multiplying the original intrinsic volume section. -/
def scalarVolume {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (f : M → ℝ) (ω : Field S n) : Field S n :=
  fun p => f p • ω p

/-- Unsigned metric integrand in a chart, extended by zero in the ambient model.
The true model boundary is included. -/
def gramIntegrand {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} (g : Metric C)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (f : M → ℝ) : Euclidean n → ℝ :=
  extendModel (fun x => if hx : x ∈ c.target then
    f (c.symm x) * Real.sqrt (metricMatrix g K c hc ⟨c.symm x, c.map_target hx⟩).det
    else 0)

/-- The Euclidean one-form pulled back by the actual ambient realization J of
the inclusion differential. No smoothness or compactness certificate is stored. -/
def euclideanOneForm {n N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N) (A : M → Euclidean N) : Field S 1 :=
  fun p => (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
    (∑ i : Fin N, A p i • (LinearMap.proj i).comp (J p))

/-- The Gram matrix of the images of the intrinsic coordinate vectors. -/
def embeddedGram {n N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M}
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => ∑ l : Fin N,
    J p.val (CovectorData.coordinateVector K c hc p.val p.property i) l *
    J p.val (CovectorData.coordinateVector K c hc p.val p.property j) l)

/-- The classical oriented line integrand A(γ(t)) · γ'(t), with the actual
inclusion differential applied to the chart tangent and the chart sign. -/
def lineIntegrand {N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 1 a M} (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart 1 a M) (hc : c ∈ S.smoothStructure.val)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N) (A : M → Euclidean N) :
    Euclidean 1 → ℝ :=
  extendModel (fun x => if hx : x ∈ c.target then
    let p : c.source := ⟨c.symm x, c.map_target hx⟩
    signValue (s.sign c hc p) * ∑ i : Fin N,
      A p.val i * J p.val (CovectorData.coordinateVector K c hc p.val p.property 0) i
    else 0)

/-- The pullback of first-slot contraction of determinant volume by X.
The sign (-1)^i corresponds to omitting the i-th coordinate covector. -/
def euclideanFluxForm {m N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean (N+1))
    (X : M → Euclidean (N+1)) : Field S N :=
  fun p => ∑ i : Fin (N+1), ((-1 : ℝ)^i.val * X p i) •
    exteriorPower.ιMulti ℝ N (fun k => (LinearMap.proj (i.succAbove k)).comp (J p))

/-- Classical Euclidean surface density in any parametrization, including true
boundary charts. The Euclidean dot product is used in the Gram determinant. -/
def surfaceIntegrand {n N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M}
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (f : M → ℝ) : Euclidean n → ℝ :=
  extendModel (fun x => if hx : x ∈ c.target then
    f (c.symm x) * Real.sqrt (embeddedGram J K c hc ⟨c.symm x, c.map_target hx⟩).det
    else 0)

/-- Extend a scalar on a Euclidean subset by zero, retaining its values at the
true boundary. Its ambient integral is the ordinary Lebesgue integral over d. -/
def extendScalar {n : ℕ} (d : Set (Euclidean n)) (f : d → ℝ) (x : Euclidean n) : ℝ :=
  if hx : x ∈ d then f ⟨x, hx⟩ else 0

/-- Pullback of the ordinary ordered Euclidean coordinate volume. -/
def euclideanVolumeForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean n) : Field S n :=
  fun p => exteriorPower.ιMulti ℝ n (fun i => (LinearMap.proj i).comp (J p))

end SmoothManifolds.ClassicalIntegralData

namespace Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.FormPullbackData
  _root_.SmoothManifolds.OrientationData _root_.SmoothManifolds.MetricVolumeData
  _root_.SmoothManifolds.LocalIntegrationData _root_.SmoothManifolds.GlobalIntegrationData
  _root_.SmoothManifolds.ClassicalIntegralData Set MeasureTheory
universe u

def scalar_volume_compactType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (g : Metric C) (o : Orientation S) (ω : Form D), IsMetricVolume g o ω →
    ∀ f : M → ℝ, Continuous f → IsCompact (sectionSupport f) →
    ∃ η : CompactTopForm S, η.field = scalarVolume f ω.field ∧
      sectionSupport η.field ⊆ sectionSupport f

def compact_manifold_supportType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold n a M) (k : ℕ) (ω : Field S k),
    IsCompact (sectionSupport ω)

/-- Cancellation of the orientation sign with the sign of metric volume. -/
def scalar_volume_coefficientType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (g : Metric C) (o : Orientation S) (ω : Form D), IsMetricVolume g o ω →
    ∀ (s : SignedCharts S), RepresentsSignedCharts o.val s →
    ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (f : M → ℝ),
      signedCoordinateCoefficient s K c hc (scalarVolume f ω.field) =
        gramIntegrand g K c hc f

/-- Local classical metric integral, for every genuine coordinate-compatible
integral and every chart containing the scalar support. -/
def scalar_volume_local_integralType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (g : Metric C) (o : Orientation S) (ω : Form D), IsMetricVolume g o ω →
    ∀ (f : M → ℝ), Continuous f → IsCompact (sectionSupport f) →
    ∃ η : CompactTopForm S, η.field = scalarVolume f ω.field ∧
      ∀ (I : CompactTopForm S → ℝ), IsIntegral o I →
      ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
      sectionSupport f ⊆ c.source →
      Integrable (gramIntegrand g K c hc f) ∧ I η = ∫ x, gramIntegrand g K c hc f x

/-- Actual unsigned Gram factors transform by the absolute Jacobian. -/
def weighted_gram_overlapType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (g : Metric C)
    (K : FiberCoordinates S) (c d : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (f : M → ℝ) (p : ↥(c.source ∩ d.source)),
    f p.val * Real.sqrt (metricMatrix g K d hd ⟨p.val, p.property.2⟩).det =
      |transitionDeterminant K d c hd hc ⟨p.val, p.property.2, p.property.1⟩| *
        (f p.val * Real.sqrt (metricMatrix g K c hc ⟨p.val, p.property.1⟩).det)

/-- Global classical metric integral for any subordinate localization. This does
not ask for a single chart containing the entire manifold or its support. -/
def scalar_volume_localizationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (g : Metric C) (o : Orientation S) (ω : Form D), IsMetricVolume g o ω →
    ∀ (f : M → ℝ), Continuous f → IsCompact (sectionSupport f) →
    ∃ η : CompactTopForm S, η.field = scalarVolume f ω.field ∧
      ∀ (I : CompactTopForm S → ℝ), IsIntegral o I →
      ∀ (K : FiberCoordinates S) {ι : Type u} (c : ι → ModelChart n a M)
        (hc : ∀ i, c i ∈ S.smoothStructure.val) (ρ : ι → M → ℝ),
      IsLocalization c ρ η →
      I η = ∑ᶠ i, ∫ x, gramIntegrand g K (c i) (hc i) (fun p => ρ i p * f p) x

/-- Ordinary signed point evaluation for scalar zero-forms, constructed from
continuous scalars with compact support. -/
def zero_scalar_integralType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (o : Orientation S) (f : M → ℝ),
    Continuous f → IsCompact (sectionSupport f) →
    ∃ η : CompactTopForm S, η.field = scalarField S f ∧
      ∀ I : CompactTopForm S → ℝ, IsIntegral o I →
      ∃ h : (sectionSupport f).Finite,
        I η = ∑ p ∈ h.toFinset, zeroSign o p * f p

/-- Metric zero-volume has the point sign as coefficient; integration multiplies
by that sign again and gives unsigned counting density. -/
def zero_metric_integralType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (C : CotangentBundle S) (D : FormBundle C 0)
    (g : Metric C) (o : Orientation S) (ω : Form D), IsMetricVolume g o ω →
    ∀ (f : M → ℝ), Continuous f → IsCompact (sectionSupport f) →
    ∃ η : CompactTopForm S, η.field = scalarVolume f ω.field ∧
      ∀ I : CompactTopForm S → ℝ, IsIntegral o I →
      ∃ h : (sectionSupport η.field).Finite,
        I η = ∑ p ∈ h.toFinset, f p

/-- Local ambient coefficient extensions remain local C¹ extensions in every
intrinsic chart, without a globally C¹ ambient extension. -/
def embedded_coefficients_regularType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (j : M → Euclidean N),
    _root_.SmoothManifolds.EmbeddedData.HasFullRankParametrizations S j →
    ∀ A : M → Euclidean N, LocallyContDiffAlong 1 j A →
    ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
      LocallyContDiffAlong 1 (fun p : c.source => (c p.val).val) (fun p => A p.val)

/-- Multiplication of a C¹ intrinsic field by coefficients with local C¹ chart
extensions preserves C¹ regularity and the closed support inclusion. -/
def regular_scalar_multiplyType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (k : ℕ)
    (ω : Field S k), _root_.SmoothManifolds.ExteriorDerivativeData.IsRegularField C 1 k ω →
    ∀ f : M → ℝ,
      (∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
        LocallyContDiffAlong 1 (fun p : c.source => (c p.val).val) (fun p => f p.val)) →
      _root_.SmoothManifolds.ExteriorDerivativeData.IsRegularField C 1 k (fun p => f p • ω p) ∧
      sectionSupport (fun p => f p • ω p) ⊆ sectionSupport f ∩ sectionSupport ω

/-- C¹ vector coefficients give the intrinsic pulled-back Euclidean one-form.
Its covector evaluation uses the actual inclusion differential and the genuine
standard ambient tangent coordinates. Closed support is taken in the source. -/
def embedded_oneform_regularType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (j : M → Euclidean N),
    _root_.SmoothManifolds.EmbeddedData.HasFullRankParametrizations S j →
    ∀ (A : M → Euclidean N), LocallyContDiffAlong 1 j A →
    ∀ (T : SmoothManifold N .euclidean (Euclidean N)),
      _root_.SmoothManifolds.EmbeddedData.euclideanChart N ∈ T.smoothStructure.val →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p)),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsDifferential S T j p (L p)) →
    ∀ (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsChartCoordinates T (j p)
        (_root_.SmoothManifolds.EmbeddedData.euclideanChart N) (F p)) →
    ∃ ω : Field S 1,
      _root_.SmoothManifolds.ExteriorDerivativeData.IsRegularField C 1 1 ω ∧
      sectionSupport ω ⊆ sectionSupport A ∧
      ∀ p v, (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))) (ω p) v =
        ∑ i, A p i * F p (L p v) i

/-- The existential C¹ form above is the explicit Euclidean covector pullback. -/
def euclidean_oneform_regularType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (j : M → Euclidean N),
    _root_.SmoothManifolds.EmbeddedData.HasFullRankParametrizations S j →
    ∀ (A : M → Euclidean N), LocallyContDiffAlong 1 j A →
    ∀ (T : SmoothManifold N .euclidean (Euclidean N)),
      _root_.SmoothManifolds.EmbeddedData.euclideanChart N ∈ T.smoothStructure.val →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p)),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsDifferential S T j p (L p)) →
    ∀ (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsChartCoordinates T (j p)
        (_root_.SmoothManifolds.EmbeddedData.euclideanChart N) (F p)) →
    let ω := euclideanOneForm S (fun p => (F p).toLinearMap.comp (L p)) A
    _root_.SmoothManifolds.ExteriorDerivativeData.IsRegularField C 1 1 ω ∧
      sectionSupport ω ⊆ sectionSupport A ∧
      (IsCompact (sectionSupport A) → IsCompact (sectionSupport ω))

/-- Open-neighborhood C¹ is sufficient; values off U are irrelevant. -/
def ambient_coefficients_localType : Prop :=
  ∀ {N : ℕ} {M : Type u} (j : M → Euclidean N) (U : Set (Euclidean N)),
    IsOpen U → (∀ p, j p ∈ U) → ∀ A : Euclidean N → Euclidean N,
      ContDiffOn ℝ 1 A U → LocallyContDiffAlong 1 j (fun p => A (j p))

/-- Construct a compact top form from C¹ local coefficient extensions and
compact closed support, also when that support meets a true boundary. -/
def regular_top_formType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (ω : Field S n),
    _root_.SmoothManifolds.ExteriorDerivativeData.IsRegularField C 1 n ω →
    IsCompact (sectionSupport ω) → ∃ η : CompactTopForm S, η.field = ω

/-- Induced Euclidean metric coefficients are exactly the Gram matrix of the
actual ambient images of the coordinate vectors. -/
def induced_metric_gramType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (g : Metric C)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N),
    (∀ p v w, metricForm g p v w = ∑ i, J p v i * J p w i) →
    ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (p : c.source), metricMatrix g K c hc p = embeddedGram J K c hc p

/-- Arc length is the one-by-one Gram square root in the Euclidean dot metric,
not the sup norm of Fin N → ℝ. -/
def arc_length_factorType : Prop :=
  ∀ {N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 1 a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N)
    (K : FiberCoordinates S) (c : ModelChart 1 a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source),
    Real.sqrt (embeddedGram J K c hc p).det =
      Real.sqrt (∑ l : Fin N, (J p.val (CovectorData.coordinateVector K c hc p.val p.property 0) l)^2)

/-- The two-dimensional Gram factor is the usual Euclidean surface area. -/
def surface_area_factorType : Prop :=
  ∀ {N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N)
    (K : FiberCoordinates S) (c : ModelChart 2 a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source),
    let u := J p.val (CovectorData.coordinateVector K c hc p.val p.property 0)
    let v := J p.val (CovectorData.coordinateVector K c hc p.val p.property 1)
    Real.sqrt (embeddedGram J K c hc p).det =
      Real.sqrt ((∑ l, (u l)^2) * (∑ l, (v l)^2) - (∑ l, u l * v l)^2)

/-- Local line integration is literal evaluation on the actual chart tangent. -/
def line_coefficientType : Prop :=
  ∀ {N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 1 a M) (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart 1 a M) (hc : c ∈ S.smoothStructure.val)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N) (A : M → Euclidean N),
    signedCoordinateCoefficient s K c hc (euclideanOneForm S J A) = lineIntegrand s K c hc J A

/-- Global line integration for any continuous intrinsic Euclidean pullback. Compact
support is imposed on the actual one-form; properness of the inclusion is absent.
Its regularity follows from euclidean_oneform_regular under local C¹ hypotheses. -/
def line_integralType : Prop :=
  ∀ {N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 1 a M) (C : CotangentBundle S) (o : Orientation S)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N) (A : M → Euclidean N),
    _root_.SmoothManifolds.ExteriorDerivativeData.IsContinuousField C 1 (euclideanOneForm S J A) →
    IsCompact (sectionSupport (euclideanOneForm S J A)) →
    ∃ η : CompactTopForm S, η.field = euclideanOneForm S J A ∧
      ∀ (I : CompactTopForm S → ℝ), IsIntegral o I →
      ∀ (s : SignedCharts S), RepresentsSignedCharts o.val s →
      ∀ (K : FiberCoordinates S),
      (∀ (c : ModelChart 1 a M) (hc : c ∈ S.smoothStructure.val),
        sectionSupport η.field ⊆ c.source →
        Integrable (lineIntegrand s K c hc J A) ∧ I η = ∫ x, lineIntegrand s K c hc J A x) ∧
      (∀ {ι : Type u} (c : ι → ModelChart 1 a M) (hc : ∀ i, c i ∈ S.smoothStructure.val)
        (ρ : ι → M → ℝ), IsLocalization c ρ η →
        I η = ∑ᶠ i, ∫ x, lineIntegrand s K (c i) (hc i) J (fun p => ρ i p • A p) x)

/-- The ambient image of each intrinsic chart tangent is literally the derivative
of every permitted local parametrization extension, also at true boundaries. -/
def parametrization_differentialType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (j : M → Euclidean N),
    _root_.SmoothManifolds.EmbeddedData.HasFullRankParametrizations S j →
    ∀ (T : SmoothManifold N .euclidean (Euclidean N)),
      _root_.SmoothManifolds.EmbeddedData.euclideanChart N ∈ T.smoothStructure.val →
    ∀ (p : M) (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
      (F : TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N),
    _root_.SmoothManifolds.DifferentialData.IsDifferential S T j p L →
    _root_.SmoothManifolds.DifferentialData.IsChartCoordinates T (j p)
      (_root_.SmoothManifolds.EmbeddedData.euclideanChart N) F →
    ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (hp : p ∈ c.source) (V : Set (Euclidean n)) (H : Euclidean n → Euclidean N),
    _root_.SmoothManifolds.EmbeddedData.IsParametrizationAt j c p V H →
    ∀ i : Fin n, F (L (CovectorData.coordinateVector K c hc p hp i)) =
      fderiv ℝ H (c p).val (Pi.single i 1)

/-- Pointwise verification that the omitted-covector expression is contraction
of standard determinant volume, with X inserted in the first slot. -/
def flux_evaluationType : Prop :=
  ∀ {m N : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean (N+1))
    (X : M → Euclidean (N+1)) (p : M) (v : Fin N → TangentSpace S p),
    evaluate (TangentSpace S p) N (euclideanFluxForm S J X p) v =
      (Matrix.of (fun i j : Fin (N+1) => ((Fin.cons (X p) (fun k => J p (v k)) : Fin (N+1) → Euclidean (N+1)) j) i)).det

/-- The contracted Euclidean (N-1)-form is intrinsically C¹ under local C¹
coefficient extensions and the actual smooth inclusion differential. This
includes ambient dimension one, where the result is a zero-form. -/
def euclidean_flux_regularType : Prop :=
  ∀ {m N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold m a M) (C : CotangentBundle S) (j : M → Euclidean (N+1)),
    _root_.SmoothManifolds.EmbeddedData.HasFullRankParametrizations S j →
    ∀ (X : M → Euclidean (N+1)), LocallyContDiffAlong 1 j X →
    ∀ (T : SmoothManifold (N+1) .euclidean (Euclidean (N+1))),
      _root_.SmoothManifolds.EmbeddedData.euclideanChart (N+1) ∈ T.smoothStructure.val →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p)),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsDifferential S T j p (L p)) →
    ∀ (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean (N+1)),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsChartCoordinates T (j p)
        (_root_.SmoothManifolds.EmbeddedData.euclideanChart (N+1)) (F p)) →
    let ω := euclideanFluxForm S (fun p => (F p).toLinearMap.comp (L p)) X
    _root_.SmoothManifolds.ExteriorDerivativeData.IsRegularField C 1 N ω ∧
      sectionSupport ω ⊆ sectionSupport X ∧
      (IsCompact (sectionSupport X) → IsCompact (sectionSupport ω))

/-- Smooth immersions into standard Euclidean space satisfy the full-rank
parametrization interface; it is a conclusion, not an extra embedding hypothesis. -/
def immersion_parametrizationsType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (T : SmoothManifold N .euclidean (Euclidean N)),
    _root_.SmoothManifolds.EmbeddedData.euclideanChart N ∈ T.smoothStructure.val →
    ∀ j : M → Euclidean N, _root_.SmoothManifolds.MapData.IsSmoothMap S T j →
      _root_.SmoothManifolds.MapClassData.IsImmersion S T j →
      _root_.SmoothManifolds.EmbeddedData.HasFullRankParametrizations S j

/-- In particular the actual inclusion of every Euclidean regular domain has
full-rank parametrizations, with no boundarylessness or interior-support premise. -/
def regular_domain_parametrizationsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} (T : SmoothManifold n .euclidean (Euclidean n)),
    _root_.SmoothManifolds.EmbeddedData.euclideanChart n ∈ T.smoothStructure.val →
    ∀ (d : Set (Euclidean n)) (S : SmoothManifold n a d),
      _root_.SmoothManifolds.RegularDomainData.IsRegularDomain T d S →
      _root_.SmoothManifolds.EmbeddedData.HasFullRankParametrizations S Subtype.val

/-- The classical surface integrand is the Gram determinant of the derivatives
of the inclusion parametrization, for every allowed local ambient extension. -/
def parametrization_gramType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (j : M → Euclidean N),
    _root_.SmoothManifolds.EmbeddedData.HasFullRankParametrizations S j →
    ∀ (T : SmoothManifold N .euclidean (Euclidean N)),
      _root_.SmoothManifolds.EmbeddedData.euclideanChart N ∈ T.smoothStructure.val →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p)),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsDifferential S T j p (L p)) →
    ∀ (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsChartCoordinates T (j p)
        (_root_.SmoothManifolds.EmbeddedData.euclideanChart N) (F p)) →
    ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (p : c.source) (V : Set (Euclidean n)) (H : Euclidean n → Euclidean N),
      _root_.SmoothManifolds.EmbeddedData.IsParametrizationAt j c p.val V H →
      embeddedGram (fun q => (F q).toLinearMap.comp (L q)) K c hc p =
        Matrix.of (fun i k : Fin n => ∑ l : Fin N,
          fderiv ℝ H (c p.val).val (Pi.single i 1) l *
          fderiv ℝ H (c p.val).val (Pi.single k 1) l)

/-- Scalar surface integration on every oriented embedded manifold, including
curves, hypersurfaces, surfaces in R³, empty manifolds and genuine boundaries.
The induced Euclidean metric, its volume form and the compact top form are
constructed, not assumed. Parametrization factors are the actual Gram factors. -/
def embedded_surface_integralType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (o : Orientation S) (j : M → Euclidean N),
    _root_.SmoothManifolds.EmbeddedData.HasFullRankParametrizations S j →
    ∀ (T : SmoothManifold N .euclidean (Euclidean N)),
      _root_.SmoothManifolds.EmbeddedData.euclideanChart N ∈ T.smoothStructure.val →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p)),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsDifferential S T j p (L p)) →
    ∀ (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsChartCoordinates T (j p)
        (_root_.SmoothManifolds.EmbeddedData.euclideanChart N) (F p)) →
    ∀ f : M → ℝ, Continuous f → IsCompact (sectionSupport f) →
    ∃ g : Metric C,
      (∀ p v w, metricForm g p v w = ∑ i, F p (L p v) i * F p (L p w) i) ∧
      ∃ ω : Form D, IsMetricVolume g o ω ∧
      ∃ η : CompactTopForm S, η.field = scalarVolume f ω.field ∧
      ∀ (I : CompactTopForm S → ℝ), IsIntegral o I →
      ∀ K : FiberCoordinates S,
      (∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
        sectionSupport f ⊆ c.source →
        Integrable (surfaceIntegrand (fun p => (F p).toLinearMap.comp (L p)) K c hc f) ∧
          I η = ∫ x, surfaceIntegrand (fun p => (F p).toLinearMap.comp (L p)) K c hc f x) ∧
      (∀ {ι : Type} (c : ι → ModelChart n a M) (hc : ∀ i, c i ∈ S.smoothStructure.val)
        (ρ : ι → M → ℝ), IsLocalization c ρ η →
        I η = ∑ᶠ i, ∫ x, surfaceIntegrand (fun p => (F p).toLinearMap.comp (L p))
          K (c i) (hc i) (fun p => ρ i p * f p) x)

/-- In ambient dimension one, first-slot contraction is the scalar zero-form. -/
def zero_flux_fieldType : Prop :=
  ∀ {m : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 1) (X : M → Euclidean 1),
    euclideanFluxForm (N := 0) S J X = scalarField S (fun p => X p 0)

/-- Scalar flux against the oriented zero-volume, whose underlying metric
 density is one at each point. -/
def zero_flux_metricType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (C : CotangentBundle S) (D : FormBundle C 0)
    (g : Metric C) (o : Orientation S) (ω : Form D), IsMetricVolume g o ω →
    ∀ (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 1) (X : M → Euclidean 1),
    euclideanFluxForm (N := 0) S J X = scalarVolume (fun p => zeroSign o p * X p 0) ω.field

/-- The ambient one-dimensional flux integral is the signed endpoint sum.
The compact top-form is constructed from continuity and intrinsic compact support. -/
def zero_flux_integralType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (o : Orientation S)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 1)
    (X : M → Euclidean 1), Continuous X → IsCompact (sectionSupport X) →
    ∃ η : CompactTopForm S, η.field = euclideanFluxForm (N := 0) S J X ∧
      ∀ I : CompactTopForm S → ℝ, IsIntegral o I →
      ∃ h : (sectionSupport X).Finite,
        I η = ∑ p ∈ h.toFinset, zeroSign o p * X p 0



/-- The ordinary Lebesgue interpretation for a regular Euclidean domain. The
induced metric, normalized volume and compact top form are all constructed from
the inclusion differential and scalar continuity/support. No globally defined
chart, interior support or integrability hypothesis is imposed. -/
def regular_domain_integralType : Prop :=
  ∀ {n : ℕ} {a : ModelKind}
    (T : SmoothManifold n .euclidean (Euclidean n)),
    _root_.SmoothManifolds.EmbeddedData.euclideanChart n ∈ T.smoothStructure.val →
    ∀ (d : Set (Euclidean n)) (S : SmoothManifold n a d),
    _root_.SmoothManifolds.RegularDomainData.IsRegularDomain T d S →
    ∀ (C : CotangentBundle S) (D : FormBundle C n) (o : Orientation S)
      (f : d → ℝ), Continuous f → IsCompact (sectionSupport f) →
    ∃ (L : (p : d) → TangentSpace S p →ₗ[ℝ] TangentSpace T p.val)
      (F : (p : d) → TangentSpace T p.val ≃ₗ[ℝ] Euclidean n),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsDifferential S T Subtype.val p (L p)) ∧
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsChartCoordinates T p.val
        (_root_.SmoothManifolds.EmbeddedData.euclideanChart n) (F p)) ∧
      ∃ g : Metric C,
        (∀ p v w, metricForm g p v w = ∑ i, F p (L p v) i * F p (L p w) i) ∧
        ∃ ω : Form D, IsMetricVolume g o ω ∧
        ∃ η : CompactTopForm S, η.field = scalarVolume f ω.field ∧
          Integrable (extendScalar d f) ∧
          ∀ I : CompactTopForm S → ℝ, IsIntegral o I →
            I η = ∫ x in d, extendScalar d f x


def euclidean_standard_volumeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (j : M → Euclidean n) (hj : EmbeddedData.HasFullRankParametrizations S j)
    (T : SmoothManifold n .euclidean (Euclidean n))
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (hL : ∀ p, DifferentialData.IsDifferential S T j p (L p))
    (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean n)
    (hF : ∀ p, DifferentialData.IsChartCoordinates T (j p) (EmbeddedData.euclideanChart n) (F p))
    (g : Metric C)
    (hJ : ∀ p v w, metricForm g p v w = ∑ i, F p (L p v) i * F p (L p w) i),
    ∃ (o : Orientation S) (ω : Form D),
      ω.field = (fun p => exteriorPower.ιMulti ℝ n
        (fun i => (LinearMap.proj i).comp ((F p).toLinearMap.comp (L p)))) ∧
      IsMetricVolume g o ω ∧
      ∀ p v, IsPositive (o.val p) v ↔ 0 < pairing p (ω.field p) v



/-- Standard Euclidean orientation is characterized by positive determinant
volume. Its scalar top-form integral is ordinary integration over the domain,
without an assumed volume-form or integrability certificate. -/
def standard_domain_integralType : Prop :=
  ∀ {n : ℕ} {a : ModelKind}
    (T : SmoothManifold n .euclidean (Euclidean n)),
    _root_.SmoothManifolds.EmbeddedData.euclideanChart n ∈ T.smoothStructure.val →
    ∀ (d : Set (Euclidean n)) (S : SmoothManifold n a d),
    _root_.SmoothManifolds.RegularDomainData.IsRegularDomain T d S →
    ∀ (C : CotangentBundle S) (D : FormBundle C n) (f : d → ℝ),
      Continuous f → IsCompact (sectionSupport f) →
    ∃ (L : (p : d) → TangentSpace S p →ₗ[ℝ] TangentSpace T p.val)
      (F : (p : d) → TangentSpace T p.val ≃ₗ[ℝ] Euclidean n),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsDifferential S T Subtype.val p (L p)) ∧
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsChartCoordinates T p.val
        (_root_.SmoothManifolds.EmbeddedData.euclideanChart n) (F p)) ∧
      ∃ o : Orientation S,
        (∀ p v, IsPositive (o.val p) v ↔
          0 < pairing p (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p)) p) v) ∧
        ∃ η : CompactTopForm S,
          η.field = scalarVolume f (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p))) ∧
          Integrable (extendScalar d f) ∧
          ∀ I : CompactTopForm S → ℝ, IsIntegral o I →
            I η = ∫ x in d, extendScalar d f x

/-- On a compact base all coefficient and vector-field support conditions are
automatic, as are the form support conditions above. -/
def compact_coefficient_supportType : Prop :=
  ∀ {M F : Type u} [TopologicalSpace M] [CompactSpace M] [Zero F]
    (f : M → F), IsCompact (sectionSupport f)

/-- Separate local extensions of finitely many coefficients give one local
vector-valued extension; no common global extension is required. -/
def coefficientwise_local_extensionsType : Prop :=
  ∀ {n q : ℕ} {M : Type u} (r : ℕ∞) (j : M → Euclidean n) (A : M → Euclidean q),
    (∀ i, LocallyContDiffAlong r j (fun p => A p i)) → LocallyContDiffAlong r j A

/-- The C¹ ambient open-neighborhood hypothesis gives the actual intrinsic
one-form on an embedded surface. Support is closed in the source, and no
properness or ambient compact-support condition is assumed. -/
def ambient_oneform_regularType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (j : M → Euclidean N),
    _root_.SmoothManifolds.EmbeddedData.HasFullRankParametrizations S j →
    ∀ U : Set (Euclidean N), IsOpen U → (∀ p, j p ∈ U) →
    ∀ A : Euclidean N → Euclidean N, ContDiffOn ℝ 1 A U →
    ∀ (T : SmoothManifold N .euclidean (Euclidean N)),
      _root_.SmoothManifolds.EmbeddedData.euclideanChart N ∈ T.smoothStructure.val →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p)),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsDifferential S T j p (L p)) →
    ∀ (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsChartCoordinates T (j p)
        (_root_.SmoothManifolds.EmbeddedData.euclideanChart N) (F p)) →
    let ω := euclideanOneForm S (fun p => (F p).toLinearMap.comp (L p)) (fun p => A (j p))
    _root_.SmoothManifolds.ExteriorDerivativeData.IsRegularField C 1 1 ω ∧
      sectionSupport ω ⊆ sectionSupport (fun p => A (j p))

/-- For every given standard orientation, integration of a continuous compactly
supported scalar times dx₁∧⋯∧dxₙ is its ordinary Lebesgue integral over D. -/
def standard_oriented_domain_integralType : Prop :=
  ∀ {n : ℕ} {a : ModelKind}
    (T : SmoothManifold n .euclidean (Euclidean n)),
    _root_.SmoothManifolds.EmbeddedData.euclideanChart n ∈ T.smoothStructure.val →
    ∀ (d : Set (Euclidean n)) (S : SmoothManifold n a d),
    _root_.SmoothManifolds.RegularDomainData.IsRegularDomain T d S →
    ∀ (C : CotangentBundle S) (D : FormBundle C n) (o : Orientation S)
      (L : (p : d) → TangentSpace S p →ₗ[ℝ] TangentSpace T p.val),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsDifferential S T Subtype.val p (L p)) →
    ∀ (F : (p : d) → TangentSpace T p.val ≃ₗ[ℝ] Euclidean n),
      (∀ p, _root_.SmoothManifolds.DifferentialData.IsChartCoordinates T p.val
        (_root_.SmoothManifolds.EmbeddedData.euclideanChart n) (F p)) →
      (∀ p v, IsPositive (o.val p) v ↔
        0 < pairing p (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p)) p) v) →
    ∀ f : d → ℝ, Continuous f → IsCompact (sectionSupport f) →
    ∃ η : CompactTopForm S,
      η.field = scalarVolume f (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p))) ∧
      Integrable (extendScalar d f) ∧
      ∀ I : CompactTopForm S → ℝ, IsIntegral o I → I η = ∫ x in d, extendScalar d f x

def euclidean_oneform_continuousType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) (C : CotangentBundle S)
    (j : M → Euclidean N) (hj : EmbeddedData.HasFullRankParametrizations S j)
    (A : M → Euclidean N) (hA : Continuous A)
    (T : SmoothManifold N .euclidean (Euclidean N))
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (hL : ∀ p, DifferentialData.IsDifferential S T j p (L p))
    (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N)
    (hF : ∀ p, DifferentialData.IsChartCoordinates T (j p) (EmbeddedData.euclideanChart N) (F p)),
    let ω := euclideanOneForm S (fun p => (F p).toLinearMap.comp (L p)) A
    ExteriorDerivativeData.IsContinuousField C 1 ω ∧
      ModelData.sectionSupport ω ⊆ ModelData.sectionSupport A

def euclidean_curve_integralType : Prop :=
  ∀ {N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold 1 a M) (C : CotangentBundle S)
    (o : Orientation S) (j : M → Euclidean N)
    (hj : EmbeddedData.HasFullRankParametrizations S j)
    (A : M → Euclidean N) (hA : Continuous A)
    (T : SmoothManifold N .euclidean (Euclidean N))
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (hL : ∀ p, DifferentialData.IsDifferential S T j p (L p))
    (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N)
    (hF : ∀ p, DifferentialData.IsChartCoordinates T (j p) (EmbeddedData.euclideanChart N) (F p))
    (hsupp : IsCompact (ModelData.sectionSupport
      (euclideanOneForm S (fun p => (F p).toLinearMap.comp (L p)) A))),
    let J := fun p => (F p).toLinearMap.comp (L p)
    ∃ η : CompactTopForm S, η.field = euclideanOneForm S J A ∧
      ∀ (I : CompactTopForm S → ℝ), IsIntegral o I →
      ∀ (s : SignedCharts S), RepresentsSignedCharts o.val s →
      ∀ (K : FiberCoordinates S),
      (∀ (c : ModelChart 1 a M) (hc : c ∈ S.smoothStructure.val),
        ModelData.sectionSupport η.field ⊆ c.source →
        Integrable (lineIntegrand s K c hc J A) ∧ I η = ∫ x, lineIntegrand s K c hc J A x) ∧
      (∀ {ι : Type} (c : ι → ModelChart 1 a M) (hc : ∀ i, c i ∈ S.smoothStructure.val)
        (ρ : ι → M → ℝ), IsLocalization c ρ η →
        I η = ∑ᶠ i, ∫ x, lineIntegrand s K (c i) (hc i) J (fun p => ρ i p • A p) x)


end Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications
