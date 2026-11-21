import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.RegularDomainGeometryAndJordanMeasurability
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.ManifoldIntegralIndependence

/-! Independent specification of paper.tex, d04:12:region-interface.
The scalar field below is the actual restriction of f dx₁ ∧ ... ∧ dxₙ to
canonical tangent spaces. The integral is the upstream signed partition
integral, and the region integrals are the upstream Darboux integrals.
No representation-equivalence certificate is assumed. -/
noncomputable section
open Set Function
open scoped ContDiff BigOperators
namespace Specs.D04.C12.RegularDomainRiemannManifoldBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C06.JordanRegions.Model
namespace Model

/-- Restriction of the normalized ambient volume covector, with scalar f. -/
def volumeField {n : ℕ} {M : Set (E n)} (f : M → ℝ) : TangentTopField 1 n M :=
  fun x => f x • (omega n).compLinearMap (tangentSpace 1 n M x).subtype

/-- The usual ambient orientation, expressed intrinsically by positivity on
ordered tangent bases. This definition does not assert any integral identity. -/
def IsAmbientOrientation {n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 n M) : Prop :=
  ∀ (x : M) (b : Module.Basis (Fin n) ℝ (tangentSpace 1 n M x)),
    b.orientation = o.atPoint x x.property ↔ 0 < omega n (fun i => (b i).val)

end Model
open Model

abbrev volumeFieldType := ∀ {n : ℕ} {M : Set (E n)},
  (M → ℝ) → TangentTopField 1 n M
def volumeFieldValue : volumeFieldType := @Model.volumeField

abbrev IsAmbientOrientationType := ∀ {n : ℕ} {M : Set (E n)},
  PositiveManifoldOrientation 1 n M → Prop
def IsAmbientOrientationValue : IsAmbientOrientationType := @Model.IsAmbientOrientation

/-- The signed, unweighted coefficient in every chart, including flat boundaries. -/
def volume_coefficientType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)} (f : M → ℝ)
    (c : EmbeddedChart 1 n n M) (u : c.source),
    topCoefficient (volumeField f) c u = f (chartPoint c u) * (chartDifferential c u).det

/-- No connectedness or positive-atlas hypothesis is imposed. -/
def ambient_orientation_existsType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)}, 0 < n → IsEmbeddedManifold 1 n M →
    ∃ o : PositiveManifoldOrientation 1 n M, IsAmbientOrientation o

def ambient_chart_signType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation 1 n M),
    IsAmbientOrientation o → ∀ (c : EmbeddedChart 1 n n M) (u : c.source),
      chartSign o.atPoint c u u.property = Real.sign ((chartDifferential c u).det)

/-- The pointwise identity required before absolute-Jacobian substitution. -/
def signed_volume_coefficientType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation 1 n M),
    IsAmbientOrientation o → ∀ (f : M → ℝ) {L : Set M}
      (P : SignedChartPartition o L) (i : Fin P.count) (u : (P.chart i).source),
      (P.sign i).val * localizedTopCoefficient (volumeField f) (P.chart i) (P.weight i) u =
        P.weight i ((P.chart i).toFun u) * f (chartPoint (P.chart i) u) *
          |(chartDifferential (P.chart i) u).det|

def volume_field_continuousType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)} (f : M → ℝ), Continuous f →
    ContinuousTopField (volumeField f)

/-- Full regular-domain interface, for every positive dimension (n = d+1).
All allowed signed partitions are compared with the actual region integral.
The existence clause prevents vacuous quantification over chart partitions. -/
def regular_domain_interfaceType : Prop :=
  ∀ {d : ℕ} {D : Set (E (d+1))} (hD : IsClassicalRegularDomain D),
    ∃ o : PositiveManifoldOrientation 1 (d+1) (closure D),
      IsAmbientOrientation o ∧ IsCompact (closure D) ∧
      IsEmbeddedManifold 1 (d+1) (closure D) ∧
      intrinsicBoundary 1 (d+1) (closure D) = frontier D ∧
      Jordan D ∧ Jordan (closure D) ∧
      (∀ p : frontier D,
        IsOutwardUnitConormal 1 d (closure D) p (outwardNormal hD p)) ∧
      (∀ (U : Set (E (d+1))) (ρ : E (d+1) → ℝ), IsDefiningFunction D U ρ →
        ∀ p ∈ frontier D ∩ U,
          IsOutwardUnitConormal 1 d (closure D) p (normalFromDefining ρ p)) ∧
      ∀ (f : closure D → ℝ), Continuous f →
        ContinuousTopField (volumeField f) ∧ IsCompact (topSupport (volumeField f)) ∧
        Nonempty (SignedChartPartition o (topSupport (volumeField f))) ∧
        RegionIntegrable f ∧
        RegionIntegrable (fun x : D => f ⟨x, subset_closure x.property⟩) ∧
        ∀ P : SignedChartPartition o (topSupport (volumeField f)),
          orientedIntegral (volumeField f) P =
            regionIntegral (fun x : D => f ⟨x, subset_closure x.property⟩) ∧
          regionIntegral (fun x : D => f ⟨x, subset_closure x.property⟩) = regionIntegral f

end Specs.D04.C12.RegularDomainRiemannManifoldBridge
