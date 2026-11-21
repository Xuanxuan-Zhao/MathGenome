import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.FiniteCompactPartition
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.MetricTopFormsAndDensities
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.DirectedSubstitution
import Mathlib.Algebra.BigOperators.Finprod

/-! The chart expression of d04:15:manifold-integral. Choice independence is
reserved for the next goal. Supports and continuity are relative to M. A density
is represented by its value on orthonormal tangent frames; its value on any
frame is this scalar times the canonical Gram density. This representation
requires no orientation, and permits signed as well as nonnegative densities. -/
noncomputable section
open Set Function
open scoped ContDiff BigOperators
namespace Specs.D04.C15.OrientedManifoldAndDensityIntegrals
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C14.FiniteCompactPartition.Model
open Specs.D04.C15.DirectedSubstitution.Model
namespace Model

def chartPoint {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (u : c.source) : M :=
  ⟨c.toFun u, (c.map_source u.property).1⟩

def topCoefficient {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M) (c : EmbeddedChart r k n M) (u : c.source) : ℝ :=
  tangentPullback η c u u.property (standardBasis k)

/-- This is continuity in the usual tangent bundle trivializations. -/
def ContinuousTopField {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M) : Prop :=
  ∀ c : EmbeddedChart r k n M, Continuous (topCoefficient η c)

def topSupport {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M) : Set M := closure {x | η x ≠ 0}

/-- A finite choice of the partition and its subordinate charts, without any
assumed coefficient integrability. -/
structure ChartPartition (r : ℕ∞ω) (k : ℕ) {n : ℕ} (M : Set (E n)) (K : Set M) where
  count : ℕ
  chart : Fin count → EmbeddedChart r k n M
  weight : Fin count → E n → ℝ
  partition : PartitionNear M K (fun i => Subtype.val ⁻¹' (chart i).ambient)
    count id weight

structure SignedChartPartition {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (K : Set M) extends ChartPartition r k M K where
  sign : Fin count → PointSign
  agrees : ∀ i (u : (chart i).source),
    chartSign o.atPoint (chart i) u u.property = (sign i).val

def localizedTopCoefficient {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M) (c : EmbeddedChart r k n M)
    (w : E n → ℝ) (u : c.source) : ℝ :=
  w (c.toFun u) * topCoefficient η c u

def orientedIntegral {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    {o : PositiveManifoldOrientation r k M} (η : TangentTopField r k M)
    (P : SignedChartPartition o (topSupport η)) : ℝ :=
  ∑ i, (P.sign i).val * coefficientIntegral (localizedTopCoefficient η (P.chart i) (P.weight i))

abbrev DensityField {n : ℕ} (M : Set (E n)) := M → ℝ

def densityValue {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (ρ : DensityField M)
    (x : M) (v : Fin k → tangentSpace r k M x) : ℝ := ρ x * tangentDensity x v

def densityCoefficient {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (ρ : DensityField M) (c : EmbeddedChart r k n M) (u : c.source) : ℝ :=
  ρ (chartPoint c u) * chartDensity c u

def localizedDensityCoefficient {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (ρ : DensityField M) (c : EmbeddedChart r k n M)
    (w : E n → ℝ) (u : c.source) : ℝ := w (c.toFun u) * densityCoefficient ρ c u

def densityIntegral {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (ρ : DensityField M)
    (P : ChartPartition r k M (tsupport ρ)) : ℝ :=
  ∑ i, coefficientIntegral (localizedDensityCoefficient ρ (P.chart i) (P.weight i))

/-- Under the zero-manifold hypotheses the summand has finite support. -/
def zeroIntegral {n : ℕ} {M : Set (E n)} (o : ZeroManifoldOrientation M) (f : M → ℝ) : ℝ :=
  ∑ᶠ x : M, (o x).val * f x

/-- Compact zero-manifolds can equivalently sum over all their points. -/
def compactZeroIntegral {n : ℕ} {M : Set (E n)} (hM : M.Finite)
    (o : ZeroManifoldOrientation M) (f : M → ℝ) : ℝ :=
  letI := hM.fintype
  ∑ x : M, (o x).val * f x
end Model
open Model

-- Expected values for the constructions; these Specs import no implementation.
def chart_partition_existsType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
  ∀ K : Set M, IsCompact K → Nonempty (ChartPartition r k M K)

def signed_partition_existsType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation r k M)
    (K : Set M), IsCompact K → Nonempty (SignedChartPartition o K)

def top_coefficients_integrableType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (η : TangentTopField r k M),
    ContinuousTopField η → ∀ {K : Set M} (P : ChartPartition r k M K) (i : Fin P.count),
      Continuous (localizedTopCoefficient η (P.chart i) (P.weight i)) ∧
      HasCompactSupport (localizedTopCoefficient η (P.chart i) (P.weight i)) ∧
      ProperIntegrable (localizedTopCoefficient η (P.chart i) (P.weight i))

def localizedTopCoefficient_pullbackType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (η : TangentTopField r k M)
    (c : EmbeddedChart r k n M) (w : E n → ℝ) (u : c.source),
    localizedTopCoefficient η c w u =
      tangentPullback (fun x => w x • η x) c u u.property (standardBasis k)

def density_coefficients_integrableType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
    ∀ (ρ : DensityField M), Continuous ρ → ∀ {K : Set M}
      (P : ChartPartition r k M K) (i : Fin P.count),
      Continuous (localizedDensityCoefficient ρ (P.chart i) (P.weight i)) ∧
      HasCompactSupport (localizedDensityCoefficient ρ (P.chart i) (P.weight i)) ∧
      ProperIntegrable (localizedDensityCoefficient ρ (P.chart i) (P.weight i))

def density_coefficient_changeType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
    ∀ (ρ : DensityField M) (c d : EmbeddedChart r k n M)
      (u : E k) (hu : u ∈ Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model.chartOverlap c d)
      (hv : Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model.chartTransition c d u ∈ d.source),
      densityCoefficient ρ c ⟨u, hu.1⟩ =
        |(fderivWithin ℝ
          (Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model.chartTransition c d)
          (Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model.chartOverlap c d) u).det| *
        densityCoefficient ρ d ⟨Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model.chartTransition c d u, hv⟩

def density_frame_changeType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (ρ : DensityField M) (x : M)
    (F : E k →ₗ[ℝ] tangentSpace r k M x) (A : E k →ₗ[ℝ] E k),
    densityValue ρ x (fun i => F (A (standardBasis k i))) =
      |A.det| * densityValue ρ x (fun i => F (standardBasis k i))

def zero_support_finiteType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r 0 M →
    ∀ f : M → ℝ, HasCompactSupport f → (support f).Finite

def zero_integral_support_sumType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r 0 M →
    ∀ (o : ZeroManifoldOrientation M) (f : M → ℝ) (hf : HasCompactSupport f),
      ∃ h : (support f).Finite, zeroIntegral o f = ∑ x ∈ h.toFinset, (o x).val * f x

def compact_zero_agreesType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r 0 M →
    IsCompact M → ∀ (o : ZeroManifoldOrientation M) (f : M → ℝ),
      ∃ h : M.Finite, zeroIntegral o f = compactZeroIntegral h o f


/-- The coefficient is the value of the intrinsic density on the actual chart frame. -/
def densityCoefficient_frameType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (ρ : DensityField M)
    (c : EmbeddedChart r k n M) (u : c.source),
    densityCoefficient ρ c u = densityValue ρ (chartPoint c u)
      (fun i => tangentChartMap c u u.property (standardBasis k i))

/-- The full construction for precisely the compactly supported continuous fields. -/
def oriented_constructionType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation r k M)
    (η : TangentTopField r k M), ContinuousTopField η → IsCompact (topSupport η) →
    ∃ P : SignedChartPartition o (topSupport η),
      (∀ i, ProperIntegrable (localizedTopCoefficient η (P.chart i) (P.weight i))) ∧
      orientedIntegral η P = ∑ i, (P.sign i).val *
        coefficientIntegral (localizedTopCoefficient η (P.chart i) (P.weight i))

def density_constructionType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
    ∀ ρ : DensityField M, Continuous ρ → HasCompactSupport ρ →
    ∃ P : ChartPartition r k M (tsupport ρ),
      (∀ i, ProperIntegrable (localizedDensityCoefficient ρ (P.chart i) (P.weight i))) ∧
      densityIntegral ρ P = ∑ i,
        coefficientIntegral (localizedDensityCoefficient ρ (P.chart i) (P.weight i))

abbrev chartPointType := ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (u : c.source), M
def chartPointValue : chartPointType := @Model.chartPoint

abbrev topCoefficientType := ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M) (c : EmbeddedChart r k n M) (u : c.source), ℝ
def topCoefficientValue : topCoefficientType := @Model.topCoefficient

abbrev ContinuousTopFieldType := ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M), Prop
def ContinuousTopFieldValue : ContinuousTopFieldType := @Model.ContinuousTopField

abbrev topSupportType := ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M), Set M
def topSupportValue : topSupportType := @Model.topSupport

abbrev localizedTopCoefficientType := ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M) (c : EmbeddedChart r k n M)
    (w : E n → ℝ) (u : c.source), ℝ
def localizedTopCoefficientValue : localizedTopCoefficientType := @Model.localizedTopCoefficient

abbrev orientedIntegralType := ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    {o : PositiveManifoldOrientation r k M} (η : TangentTopField r k M)
    (P : SignedChartPartition o (topSupport η)), ℝ
def orientedIntegralValue : orientedIntegralType := @Model.orientedIntegral

abbrev densityValueType := ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (ρ : DensityField M)
    (x : M) (v : Fin k → tangentSpace r k M x), ℝ
def densityValueValue : densityValueType := @Model.densityValue

abbrev densityCoefficientType := ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (ρ : DensityField M) (c : EmbeddedChart r k n M) (u : c.source), ℝ
def densityCoefficientValue : densityCoefficientType := @Model.densityCoefficient

abbrev localizedDensityCoefficientType := ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (ρ : DensityField M) (c : EmbeddedChart r k n M)
    (w : E n → ℝ) (u : c.source), ℝ
def localizedDensityCoefficientValue : localizedDensityCoefficientType := @Model.localizedDensityCoefficient

abbrev densityIntegralType := ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (ρ : DensityField M)
    (P : ChartPartition r k M (tsupport ρ)), ℝ
def densityIntegralValue : densityIntegralType := @Model.densityIntegral

abbrev zeroIntegralType := ∀ {n : ℕ} {M : Set (E n)} (o : ZeroManifoldOrientation M) (f : M → ℝ), ℝ
def zeroIntegralValue : zeroIntegralType := @Model.zeroIntegral

abbrev compactZeroIntegralType := ∀ {n : ℕ} {M : Set (E n)} (hM : M.Finite)
    (o : ZeroManifoldOrientation M) (f : M → ℝ), ℝ
def compactZeroIntegralValue : compactZeroIntegralType := @Model.compactZeroIntegral

abbrev ChartPartitionType := (r : ℕ∞ω) → (k : ℕ) → {n : ℕ} →
  (M : Set (E n)) → Set M → Type
def ChartPartitionValue : ChartPartitionType := @Model.ChartPartition
abbrev SignedChartPartitionType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} →
  PositiveManifoldOrientation r k M → Set M → Type
def SignedChartPartitionValue : SignedChartPartitionType := @Model.SignedChartPartition
abbrev DensityFieldType := {n : ℕ} → Set (E n) → Type
def DensityFieldValue : DensityFieldType := @Model.DensityField

end Specs.D04.C15.OrientedManifoldAndDensityIntegrals
