import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.EmbeddedCalculus
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.EmbeddedBoundary
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.Stokes
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.DensityIntegral
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.Global
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.MetricVolume
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.OrientedManifoldAndDensityIntegrals
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.MeasureBridge

/-! Independent integration and Stokes comparisons for M10.08, paper.tex 2111–2179.
These use the actual D04 proper Darboux integral and its actual zero extension.
The final statements use the actual D04 value predicates in every dimension.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped ContDiff BigOperators

namespace SmoothManifolds.EmbeddedIntegrationData
open ModelData TangentData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
/-- Positive basis predicate for D04's actual dimension-dependent orientation. -/
def D04PositiveBasis {N : ℕ} (d : ℕ) (M : Set (E N))
    (o : Specs.D04.C14.OrientationsAndChartSigns.Model.ManifoldOrientation 2 d M) (p : M)
    (b : Module.Basis (Fin d) ℝ (tangentSpace 2 d M p.val)) : Prop :=
  match d, o, b with
  | 0, s, _ => (s p).val = 1
  | _+1, o, b => b.orientation = o.atPoint p.val p.property
end SmoothManifolds.EmbeddedIntegrationData


namespace Specs.SmoothManifolds.Integration.EmbeddedCompatibility
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.EmbeddedCalculusData
  _root_.SmoothManifolds.EmbeddedAtlasData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.LocalIntegrationData _root_.SmoothManifolds.GlobalIntegrationData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model

/-- No continuity across the true boundary is required: actual proper Darboux
integrability suffices. This also includes dimension zero and an empty source. -/
def proper_integral_bridgeType : Prop :=
  ∀ {n : ℕ} {U : Set (E n)} (f : U → ℝ), ProperIntegrable f →
    MeasureTheory.Integrable (zeroExtension f) ∧
    coefficientIntegral f = ∫ x, zeroExtension f x

/-- D04 uses the Euclidean L² norm and intrinsic integration uses Pi
coordinates. Their canonical coordinate identification preserves volume. -/
def proper_integral_pi_bridgeType : Prop :=
  ∀ {n : ℕ} {U : Set (E n)} (f : U → ℝ), ProperIntegrable f →
    coefficientIntegral f = ∫ x : Euclidean n,
      zeroExtension f ((piCoordinates n).symm x)

/-- Every D04 finite partition summand has the same Riemann and Lebesgue
value. Continuity is only the original relative chart continuity. -/
def localized_top_integralType : Prop :=
  ∀ {r : ℕ∞ω} {n N : ℕ} {M : Set (E N)}
    (η : Specs.D04.C14.MetricTopFormsAndDensities.Model.TangentTopField r n M),
    ContinuousTopField η → ∀ {K : Set M} (P : ChartPartition r n M K) (i : Fin P.count),
    MeasureTheory.Integrable
      (zeroExtension (localizedTopCoefficient η (P.chart i) (P.weight i))) ∧
    coefficientIntegral (localizedTopCoefficient η (P.chart i) (P.weight i)) =
      ∫ u, zeroExtension (localizedTopCoefficient η (P.chart i) (P.weight i)) u

/-- Equality before integration, including each restricted ambient partition
weight, for the full ordered top frame. -/
def matching_localized_coefficientType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M), IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val,
    IsInclusionIdentification S I →
  ∀ (C : CotangentBundle S) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart ∞ n N M), MatchesEmbeddedChart e c →
  ∀ (ξ : Field S n) (w : E N → ℝ) (u : c.source),
    let p : M := ⟨c.toFun u, (c.map_source u.property).1⟩
    ∀ hp : p ∈ e.source,
    localizedTopCoefficient (transportField S I n ξ)
      (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)) w u =
      w p.val * FormPullbackData.topCoefficient C.tangent.fiberCoordinates e he p hp ξ

/-- The actual abstract integral, under its defining coordinate normalization,
agrees with D04's signed point sum. No connectedness or finiteness of the base
is assumed; compact support makes the sums finite. -/
def zero_integral_comparisonType : Prop :=
  ∀ {N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold 0 a M) (o : Orientation S),
  ∃ O : Specs.D04.C14.OrientationsAndChartSigns.Model.ZeroManifoldOrientation M,
    (∀ p, (O p).val = zeroSign o p) ∧
    ∀ (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 0 M p.val)
      (J : CompactTopForm S → ℝ), IsIntegral o J → ∀ ξ : CompactTopForm S,
      J ξ = Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.zeroIntegral O
        (fun p => transportField S I 0 ξ.field p (fun j => Fin.elim0 j))

/-- Local scalar-density/metric bridge. The metric is specified by its actual
bilinear values under the inclusion identification. Its global construction
from the embedding is a separate obligation. -/
def matching_density_coefficientType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M), IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val,
    IsInclusionIdentification S I →
  ∀ (C : CotangentBundle S) (g : MetricVolumeData.Metric C),
    (∀ p v z, MetricVolumeData.metricForm g p v z =
      inner ℝ (I p v).val (I p z).val) →
  ∀ μ : MetricVolumeData.DensityField S, MetricVolumeData.IsMetricDensity g μ →
  ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart ∞ n N M), MatchesEmbeddedChart e c →
  ∀ (ρ : M → ℝ) (w : E N → ℝ) (u : c.source),
    let p : M := ⟨c.toFun u, (c.map_source u.property).1⟩
    ∀ hp : p ∈ e.source,
    MetricVolumeData.densityCoefficient C.tangent.fiberCoordinates e he ⟨p, hp⟩
        (ρ p • μ p) =
      densityCoefficient ρ (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)) u ∧
    w p.val * MetricVolumeData.densityCoefficient C.tangent.fiberCoordinates e he ⟨p, hp⟩
        (ρ p • μ p) =
      localizedDensityCoefficient ρ (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)) w u

/-- All original D04 density partition summands use the same Lebesgue value,
including unorientable manifolds and dimension zero. -/
def localized_density_integralType : Prop :=
  ∀ {r : ℕ∞ω} {n N : ℕ} {M : Set (E N)}, IsEmbeddedManifold r n M →
  ∀ ρ : M → ℝ, Continuous ρ →
  ∀ {K : Set M} (P : ChartPartition r n M K) (i : Fin P.count),
    MeasureTheory.Integrable
      (zeroExtension (localizedDensityCoefficient ρ (P.chart i) (P.weight i))) ∧
    coefficientIntegral (localizedDensityCoefficient ρ (P.chart i) (P.weight i)) =
      ∫ u, zeroExtension (localizedDensityCoefficient ρ (P.chart i) (P.weight i)) u

end Specs.SmoothManifolds.Integration.EmbeddedCompatibility

namespace Specs.SmoothManifolds.Integration.EmbeddedCompatibility
open _root_.SmoothManifolds
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData
  ExteriorData EmbeddedCalculusData EmbeddedAtlasData OrientationData
  LocalIntegrationData GlobalIntegrationData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.FiniteCompactPartition.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Set MeasureTheory


def integral_comparisonType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)} (hM : IsEmbeddedManifold ∞ n M)
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (o : OrientationData.Orientation S),
    ∃ O : ManifoldOrientation 2 n M,
      (∀ (p : M) (b : Module.Basis (Fin n) ℝ (tangentSpace 2 n M p.val)),
        EmbeddedIntegrationData.D04PositiveBasis n M O p b ↔
          IsPositive (o.val p) (exteriorPower.ιMulti ℝ n (fun j => (I p).symm (b j)))) ∧
      ∀ (J : CompactTopForm S → ℝ), IsIntegral o J → ∀ ξ : CompactTopForm S,
        Specs.D04.C15.GeneralizedStokes.Model.HasManifoldIntegral 2 n O
          (transportField S I n ξ.field) (J ξ)

end Specs.SmoothManifolds.Integration.EmbeddedCompatibility

namespace Specs.SmoothManifolds.Integration.EmbeddedCompatibility
open _root_.SmoothManifolds
open ModelData AtlasData TangentData DifferentialData BoundaryData
  BoundaryOrientationData BundleOperationsData ExteriorData ExteriorDerivativeData
  FormPullbackData OrientationData LocalIntegrationData GlobalIntegrationData
  EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model (tangentSpace)
open Specs.D04.C14.EmbeddedManifoldCharts.Model (IsEmbeddedManifold)

open EmbeddedIntegrationData

/-- Full shared-domain Stokes specialization. All comparison identities are
conclusions. The original compact support and local C¹ hypotheses are retained. -/
def stokes_specializationType : Prop :=
  ∀ {d N : ℕ} {a : ModelKind} {M : Set (E N)}
    (hM : IsEmbeddedManifold ∞ (d+1) M)
    (S : SmoothManifold (d+1) a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 (d+1) M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (B : SmoothManifold d .euclidean (intrinsicBoundary S)) (A : CotangentBundle B)
    (hB : IsNaturalBoundary S B) (o : Orientation S) (q : Orientation B)
    (hq : IsInducedOrientation o q)
    (Jbulk : CompactTopForm S → ℝ) (Jbdry : CompactTopForm B → ℝ)
    (hJbulk : IsIntegral o Jbulk) (hJbdry : IsIntegral q Jbdry)
    (ξ : Field S d) (hξ : IsRegularField C 1 d ξ)
    (hc : IsCompact (sectionSupport ξ)),
    ∃ (hb : ∀ p : intrinsicBoundary S, p.val.val ∈
        Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M)
      (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (K : (p : intrinsicBoundary S) → TangentSpace B p ≃ₗ[ℝ]
        tangentSpace 2 d
          (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) p.val.val)
      (η : CompactTopForm S) (β : CompactTopForm B),
      (∀ p, IsDifferential B S Subtype.val p (L p)) ∧
      (∀ p v, (K p v).val = (I p.val (L p v)).val) ∧
      HasExteriorDerivative C ξ η.field ∧
      sectionSupport η.field ⊆ sectionSupport ξ ∧
      β.field = pullbackField B S Subtype.val L ξ ∧
      transportField S I (d+1) η.field =
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicExteriorDerivative
          (transportField S I d ξ) ∧
      (∀ p : intrinsicBoundary S,
        transportCovector (K p) d (β.field p) =
          Specs.D04.C15.GeneralizedStokes.Model.boundaryRestriction
            (transportField S I d ξ) ⟨p.val.val, hb p⟩) ∧
      Jbulk η = Jbdry β ∧
      ∃ O : Specs.D04.C14.OrientationsAndChartSigns.Model.PositiveManifoldOrientation 2 (d+1) M,
        (∀ (p : M) (b : Module.Basis (Fin (d+1)) ℝ (tangentSpace 2 (d+1) M p.val)),
          b.orientation = O.atPoint p.val p.property ↔
            IsPositive (o.val p) (exteriorPower.ιMulti ℝ (d+1)
              (fun j => (I p).symm (b j)))) ∧
        Specs.D04.C15.GeneralizedStokes.Model.HasPositiveIntegral O
          (Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicExteriorDerivative
            (transportField S I d ξ)) (Jbulk η) ∧
        ∃ bO : Specs.D04.C14.OrientationsAndChartSigns.Model.ManifoldOrientation 2 d
            (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M),
          Specs.D04.C15.GeneralizedStokes.Model.OutwardFirst d O bO ∧
          (∀ (p : intrinsicBoundary S) (b : Module.Basis (Fin d) ℝ
              (tangentSpace 2 d
                (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M)
                p.val.val)),
            D04PositiveBasis d
                (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M)
                bO ⟨p.val.val, hb p⟩ b ↔
              IsPositive (q.val p) (exteriorPower.ιMulti ℝ d
                (fun j => (K p).symm (b j)))) ∧
          Specs.D04.C15.GeneralizedStokes.Model.HasManifoldIntegral 2 d bO
            (Specs.D04.C15.GeneralizedStokes.Model.boundaryRestriction
              (transportField S I d ξ)) (Jbdry β)


end Specs.SmoothManifolds.Integration.EmbeddedCompatibility

namespace Specs.SmoothManifolds.Integration.EmbeddedCompatibility
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.EmbeddedCalculusData _root_.SmoothManifolds.EmbeddedAtlasData
  _root_.SmoothManifolds.MetricVolumeData _root_.SmoothManifolds.DensityIntegrationData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open scoped Classical ContDiff BigOperators

/-- The actual induced Euclidean metric and its canonical volume density exist.
Every compactly supported continuous scalar density gives an actual abstract
compact continuous section, with exactly the original scalar support. -/
def induced_density_existsType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M), IsInducedSmoothStructure S →
    ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val,
    IsInclusionIdentification S I → ∀ C : CotangentBundle S,
    ∃ (g : Metric C) (μ : DensityField S),
      (∀ p v z, metricForm g p v z = inner ℝ (I p v).val (I p z).val) ∧
      IsMetricDensity g μ ∧ IsSmoothDensity μ ∧ IsContinuousDensity μ ∧
      IsPositiveDensity μ ∧ (∀ p, μ p ≠ 0) ∧
      ∀ (ρ : M → ℝ), Continuous ρ → IsCompact (sectionSupport ρ) →
      ∃ σ : CompactDensity S, σ.field = (fun p => ρ p • μ p) ∧
        sectionSupport σ.field = sectionSupport ρ

/-- Comparison for any actual abstract compact scalar-density section and every
actual C² D04 partition. The full metric-free public conclusion is below. -/
def density_integral_comparisonType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M), IsInducedSmoothStructure S →
    ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val,
    IsInclusionIdentification S I → IsEmbeddedManifold ∞ n M →
    ∀ (C : CotangentBundle S) (g : Metric C),
    (∀ p v z, metricForm g p v z = inner ℝ (I p v).val (I p z).val) →
    ∀ μ : DensityField S, IsMetricDensity g μ →
    ∀ ρ : M → ℝ, Continuous ρ → HasCompactSupport ρ →
    ∀ σ : CompactDensity S, σ.field = (fun p => ρ p • μ p) →
    ∀ J : CompactDensity S → ℝ, IsDensityIntegral J →
    ∀ P : Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.ChartPartition 2 n M
      (tsupport ρ),
      J σ = Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.densityIntegral ρ P

/-- Full unsigned density comparison, with the metric, its volume density and
all compact continuous scalar-density sections constructed in the conclusion.
No orientation is required; dimension zero and either model kind are included. -/
def density_comparisonType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M), IsInducedSmoothStructure S →
    ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val,
    IsInclusionIdentification S I → IsEmbeddedManifold ∞ n M →
    ∀ C : CotangentBundle S,
    ∃ (g : Metric C) (μ : DensityField S),
      (∀ p v z, metricForm g p v z = inner ℝ (I p v).val (I p z).val) ∧
      IsMetricDensity g μ ∧ IsSmoothDensity μ ∧ IsContinuousDensity μ ∧
      IsPositiveDensity μ ∧ (∀ p, μ p ≠ 0) ∧
      ∀ ρ : M → ℝ, Continuous ρ → HasCompactSupport ρ →
      ∃ σ : CompactDensity S, σ.field = (fun p => ρ p • μ p) ∧
        sectionSupport σ.field = tsupport ρ ∧
        ∀ J : CompactDensity S → ℝ, IsDensityIntegral J →
        ∀ P : Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.ChartPartition 2 n M
          (tsupport ρ),
          J σ = Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.densityIntegral ρ P

/-- The zero-dimensional normalization identifies the actual unsigned point
sum and every actual D04 C² density integral, including noncompact bases. -/
def zero_density_comparisonType : Prop :=
  ∀ {N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold 0 a M) (C : CotangentBundle S) (g : Metric C)
    (μ : DensityField S), IsMetricDensity g μ →
    ∀ ρ : M → ℝ, HasCompactSupport ρ →
    ∀ σ : CompactDensity S, σ.field = (fun p => ρ p • μ p) →
    ∀ J : CompactDensity S → ℝ, IsDensityIntegral J →
    IsEmbeddedManifold 2 0 M →
    ∀ P : Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.ChartPartition 2 0 M
      (tsupport ρ),
      J σ = Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.densityIntegral ρ P
end Specs.SmoothManifolds.Integration.EmbeddedCompatibility
