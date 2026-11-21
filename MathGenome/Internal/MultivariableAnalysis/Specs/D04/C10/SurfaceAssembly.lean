import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.AreaIntegral
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.MetricTopFormsAndDensities
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.ManifoldIntegralIndependence

/-! Surface assembly (paper.tex, d04:10:patch and d04:10:assembly).
The integral uses the existing Chapter 15 density integral. The conditional
only totalizes it on sets on which no chart partition exists. The construction
theorem eliminates that branch for every compact embedded C¹ surface.
All scalar and vector data are functions on the surface itself.
Boundary charts retain their relative half-space source. -/
noncomputable section
open Set Function Topology
open scoped RealInnerProductSpace BigOperators ContDiff Classical
namespace Specs.D04.C10.SurfaceAssembly
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C10.PatchGeometryGram.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model

namespace Model

/-- The global scalar integral is the canonical unsigned density integral
of f times the intrinsic Gram density, without an orientation choice. -/
def surfaceIntegral {n : ℕ} (M : Set (E n)) (f : M → ℝ) : ℝ :=
  if h : Nonempty (ChartPartition 1 2 M (tsupport f)) then
    densityIntegral f (Classical.choice h)
  else 0

/-- Exactly a chosen continuous unit normal, with orthogonality to the actual
canonical tangent plane, including at boundary points. -/
structure UnitNormalField (M : Set (E 3)) where
  toFun : M → E 3
  continuous : Continuous toFun
  normal : ∀ x : M, IsUnitNormal (tangentSpace 1 2 M x) (toFun x)

def surfaceFlux {M : Set (E 3)} (N : UnitNormalField M) (F : M → E 3) : ℝ :=
  surfaceIntegral M (fun x => ⟪F x, N.toFun x⟫)

/-- Tangent restriction of beta_F, for data defined only on M. -/
def surfaceFluxForm {M : Set (E 3)} (F : M → E 3) : TangentTopField 1 2 M :=
  fun x => (beta (fun _ => F x) x).compLinearMap (tangentSpace 1 2 M x).subtype

def surfaceChartNormal {M : Set (E 3)} (c : EmbeddedChart 1 2 3 M) (u : c.source) : E 3 :=
  let v := euclideanCross (chartDifferential c u (standardBasis 2 0))
    (chartDifferential c u (standardBasis 2 1))
  ‖v‖⁻¹ • v

def normalChartSign {M : Set (E 3)} (N : UnitNormalField M)
    (c : EmbeddedChart 1 2 3 M) (u : c.source) : ℝ :=
  ⟪N.toFun (chartPoint c u), surfaceChartNormal c u⟫

/-- Coordinate-null sets, with the same box-cover nullity as Chapter 6.
The positive Gram density gives the corresponding notion of zero surface area. -/
def AreaNull {n : ℕ} (M A : Set (E n)) : Prop :=
  ∀ c : EmbeddedChart 1 2 n M,
    Specs.D04.C06.NullCovers.Model.Null (c.source ∩ c.toFun ⁻¹' A)

/-- A regular compact Jordan piece. The parameter region can have corners;
it is not required to be a manifold with smooth boundary. -/
structure ChartPiece {n : ℕ} (M : Set (E n)) where
  chart : EmbeddedChart 1 2 n M
  domain : Set (E 2)
  compact : IsCompact domain
  jordan : Specs.D04.C06.JordanRegions.Model.Jordan domain
  subset_source : domain ⊆ chart.source

def pieceImage {n : ℕ} {M : Set (E n)} (p : ChartPiece M) : Set (E n) :=
  p.chart.toFun '' p.domain

def pieceCoefficient {n : ℕ} {M : Set (E n)} (p : ChartPiece M)
    (f : M → ℝ) (u : p.domain) : ℝ :=
  f (chartPoint p.chart ⟨u, p.subset_source u.property⟩) * chartDensity p.chart u

def pieceIntegral {n : ℕ} {M : Set (E n)} (p : ChartPiece M) (f : M → ℝ) : ℝ :=
  Specs.D04.C06.JordanRegions.Model.regionIntegral (pieceCoefficient p f)

end Model
open Model

abbrev surfaceIntegralType := {n : ℕ} → (M : Set (E n)) → (M → ℝ) → ℝ
def surfaceIntegralValue : surfaceIntegralType := @Model.surfaceIntegral
abbrev UnitNormalFieldType := Set (E 3) → Type
def UnitNormalFieldValue : UnitNormalFieldType := Model.UnitNormalField
abbrev surfaceFluxType := {M : Set (E 3)} → UnitNormalField M → (M → E 3) → ℝ
def surfaceFluxValue : surfaceFluxType := @Model.surfaceFlux
abbrev surfaceFluxFormType := {M : Set (E 3)} → (M → E 3) → TangentTopField 1 2 M
def surfaceFluxFormValue : surfaceFluxFormType := @Model.surfaceFluxForm
abbrev surfaceChartNormalType := {M : Set (E 3)} →
  (c : EmbeddedChart 1 2 3 M) → c.source → E 3
def surfaceChartNormalValue : surfaceChartNormalType := @Model.surfaceChartNormal
abbrev normalChartSignType := {M : Set (E 3)} → UnitNormalField M →
  (c : EmbeddedChart 1 2 3 M) → c.source → ℝ
def normalChartSignValue : normalChartSignType := @Model.normalChartSign

def scalar_constructionType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ f : M → ℝ, Continuous f →
    ∃ P : ChartPartition 1 2 M (tsupport f),
      (∀ i, ProperIntegrable (localizedDensityCoefficient f (P.chart i) (P.weight i))) ∧
      surfaceIntegral M f = ∑ i,
        coefficientIntegral (fun u : (P.chart i).source =>
          P.weight i ((P.chart i).toFun u) * f (chartPoint (P.chart i) u) *
            Real.sqrt (Matrix.det
              ((matrixOfLinearMap (chartDifferential (P.chart i) u).toLinearMap).transpose *
                matrixOfLinearMap (chartDifferential (P.chart i) u).toLinearMap)))

/-- Every allowed chart/partition choice gives the same Chapter 15 integral. -/
def scalar_chart_formulaType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (f : M → ℝ), Continuous f →
    ∀ {K : Set M} (P : ChartPartition 1 2 M K), tsupport f ⊆ K →
      surfaceIntegral M f =
        ∑ i, coefficientIntegral (localizedDensityCoefficient f (P.chart i) (P.weight i))

def scalar_density_identificationType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (f : M → ℝ), Continuous f →
    ∀ P : ChartPartition 1 2 M (tsupport f), surfaceIntegral M f = densityIntegral f P

def scalar_addType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (f g : M → ℝ), Continuous f → Continuous g →
      surfaceIntegral M (f + g) = surfaceIntegral M f + surfaceIntegral M g

def scalar_smulType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (a : ℝ) (f : M → ℝ), Continuous f →
      surfaceIntegral M (a • f) = a * surfaceIntegral M f

def scalar_localizationType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (f : M → ℝ), Continuous f → ∀ {m : ℕ} (w : Fin m → E n → ℝ),
      (∀ i, Continuous (w i)) → (∀ x : M, f x ≠ 0 → ∑ i, w i x = 1) →
      surfaceIntegral M f = ∑ i, surfaceIntegral M (fun x => w i x * f x)

def scalar_single_chartType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (f : M → ℝ), Continuous f → ∀ c : EmbeddedChart 1 2 n M,
      tsupport f ⊆ Subtype.val ⁻¹' c.ambient →
      ProperIntegrable (densityCoefficient f c) ∧
        surfaceIntegral M f = coefficientIntegral (densityCoefficient f c)

def tangent_chart_independenceType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 1 2 M →
    ∀ (c d : EmbeddedChart 1 2 n M) (u : c.source) (v : d.source),
      c.toFun u = d.toFun v →
      tangentSpace 1 2 M (c.toFun u) = LinearMap.range (chartDifferential c u).toLinearMap ∧
      LinearMap.range (chartDifferential c u).toLinearMap =
        LinearMap.range (chartDifferential d v).toLinearMap

def regular_locally_embeddedType : Prop :=
  ∀ {n : ℕ} {U : Set (E 2)} {φ : E 2 → E n}, RegularPatch U φ →
    ∀ u ∈ U, ∃ V : Set (E 2), IsOpen V ∧ u ∈ V ∧ V ⊆ U ∧ EmbeddedPatch V φ

def flux_chart_formulaType : Prop :=
  ∀ {M : Set (E 3)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (N : UnitNormalField M) (F : M → E 3), Continuous F →
    ∀ P : ChartPartition 1 2 M (tsupport (fun x => ⟪F x, N.toFun x⟫)),
      surfaceFlux N F = ∑ i, coefficientIntegral (fun u : (P.chart i).source =>
        P.weight i ((P.chart i).toFun u) *
          ⟪F (chartPoint (P.chart i) u), N.toFun (chartPoint (P.chart i) u)⟫ *
          chartDensity (P.chart i) u)

def normal_chart_signType : Prop :=
  ∀ {M : Set (E 3)}, IsEmbeddedManifold 1 2 M → ∀ N : UnitNormalField M,
    ∀ (c : EmbeddedChart 1 2 3 M) (u : c.source),
      (normalChartSign N c u = 1 ∨ normalChartSign N c u = -1) ∧
      N.toFun (chartPoint c u) = normalChartSign N c u • surfaceChartNormal c u ∧
      ∀ F : M → E 3,
        normalChartSign N c u * topCoefficient (surfaceFluxForm F) c u =
          ⟪F (chartPoint c u), N.toFun (chartPoint c u)⟫ * chartDensity c u

def flux_beta_identificationType : Prop :=
  ∀ {M : Set (E 3)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ N : UnitNormalField M, ∃ o : PositiveManifoldOrientation 1 2 M,
      (∀ (c : EmbeddedChart 1 2 3 M) (u : c.source),
        chartSign o.atPoint c u u.property = normalChartSign N c u) ∧
      ∀ (F : M → E 3), Continuous F →
        ContinuousTopField (surfaceFluxForm F) ∧
        ∀ P : SignedChartPartition o (topSupport (surfaceFluxForm F)),
          surfaceFlux N F = orientedIntegral (surfaceFluxForm F) P

def flux_adjusted_chart_formulaType : Prop :=
  ∀ {M : Set (E 3)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (N : UnitNormalField M) (F : M → E 3), Continuous F →
    ∀ P : ChartPartition 1 2 M (tsupport (fun x => ⟪F x, N.toFun x⟫)),
      surfaceFlux N F = ∑ i, coefficientIntegral (fun u : (P.chart i).source =>
        P.weight i ((P.chart i).toFun u) * normalChartSign N (P.chart i) u *
          topCoefficient (surfaceFluxForm F) (P.chart i) u)

def flux_constructionType : Prop :=
  ∀ {M : Set (E 3)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (N : UnitNormalField M) (F : M → E 3), Continuous F →
      ∃ o : PositiveManifoldOrientation 1 2 M,
        (∀ (c : EmbeddedChart 1 2 3 M) (u : c.source),
          chartSign o.atPoint c u u.property = normalChartSign N c u) ∧
        ∃ P : SignedChartPartition o (topSupport (surfaceFluxForm F)),
          (∀ i, ProperIntegrable (localizedTopCoefficient (surfaceFluxForm F)
            (P.chart i) (P.weight i))) ∧
          surfaceFlux N F = ∑ i, (P.sign i).val * coefficientIntegral
            (localizedTopCoefficient (surfaceFluxForm F) (P.chart i) (P.weight i))

/-- Whole-chart contributions count a nonzero overlap twice. -/
def overlap_double_countType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (f : M → ℝ), Continuous f → ∀ (c d : EmbeddedChart 1 2 n M),
      tsupport f ⊆ Subtype.val ⁻¹' c.ambient →
      tsupport f ⊆ Subtype.val ⁻¹' d.ambient →
      coefficientIntegral (densityCoefficient f c) + coefficientIntegral (densityCoefficient f d) =
        2 * surfaceIntegral M f ∧
      (surfaceIntegral M f ≠ 0 →
        coefficientIntegral (densityCoefficient f c) + coefficientIntegral (densityCoefficient f d) ≠
          surfaceIntegral M f)

abbrev AreaNullType := {n : ℕ} → Set (E n) → Set (E n) → Prop
def AreaNullValue : AreaNullType := @Model.AreaNull
abbrev ChartPieceType := {n : ℕ} → Set (E n) → Type
def ChartPieceValue : ChartPieceType := @Model.ChartPiece
abbrev pieceImageType := {n : ℕ} → {M : Set (E n)} → ChartPiece M → Set (E n)
def pieceImageValue : pieceImageType := @Model.pieceImage
abbrev pieceCoefficientType := {n : ℕ} → {M : Set (E n)} →
  (p : ChartPiece M) → (M → ℝ) → p.domain → ℝ
def pieceCoefficientValue : pieceCoefficientType := @Model.pieceCoefficient
abbrev pieceIntegralType := {n : ℕ} → {M : Set (E n)} → ChartPiece M → (M → ℝ) → ℝ
def pieceIntegralValue : pieceIntegralType := @Model.pieceIntegral

def piece_integrableType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 1 2 M →
    ∀ (p : ChartPiece M) (f : M → ℝ), Continuous f →
      Specs.D04.C06.JordanRegions.Model.RegionIntegrable (pieceCoefficient p f)

/-- The full geometric finite-additivity obligation. It is separate from
finite localization by continuous weights. Each integral on the right is an
ordinary compact-region Gram integral in its own regular chart. -/
def finite_piece_additivityType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (f : M → ℝ), Continuous f → ∀ {m : ℕ} (p : Fin m → ChartPiece M),
      (⋃ i, pieceImage (p i)) = M →
      (∀ i j, i ≠ j → AreaNull M (pieceImage (p i) ∩ pieceImage (p j))) →
      surfaceIntegral M f = ∑ i, pieceIntegral (p i) f

def finite_flux_piece_additivityType : Prop :=
  ∀ {M : Set (E 3)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (N : UnitNormalField M) (F : M → E 3), Continuous F →
    ∀ {m : ℕ} (p : Fin m → ChartPiece M),
      (⋃ i, pieceImage (p i)) = M →
      (∀ i j, i ≠ j → AreaNull M (pieceImage (p i) ∩ pieceImage (p j))) →
      surfaceFlux N F = ∑ i, pieceIntegral (p i) (fun x => ⟪F x, N.toFun x⟫)

end Specs.D04.C10.SurfaceAssembly
