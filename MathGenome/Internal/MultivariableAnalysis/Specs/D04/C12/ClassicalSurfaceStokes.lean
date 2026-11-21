import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.SurfaceAssembly
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.FinitePiecewiseStokes

/-! Classical surface Stokes, paper.tex d04:12:surface-stokes.
The surface flux is exactly Chapter 10's geometric integral. Boundary work
is evaluated in signed regular charts by the ordinary dot product with the
chart velocity; the chart and path bridges below fix its classical meaning.
All manifold regularity is C¹ and all vector fields are C¹ near the surface. -/
noncomputable section
open Set Function Topology
open scoped RealInnerProductSpace BigOperators ContDiff Classical
namespace Specs.D04.C12.ClassicalSurfaceStokes
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C10.SurfaceAssembly.Model
namespace Model

/-- Agreement with the normal orientation in every chart, including charts
with negative sign and half-space charts. -/
def NormalCompatible {M : Set (E 3)} (N : UnitNormalField M)
    (o : PositiveManifoldOrientation 1 2 M) : Prop :=
  ∀ (c : EmbeddedChart 1 2 3 M) (u : c.source),
    chartSign o.atPoint c u u.property = normalChartSign N c u

/-- The usual directed work coefficient in a regular one-dimensional chart.
Its signed version is F dot tau times the positive speed. -/
def workCoefficient {B : Set (E 3)} (F : E 3 → E 3)
    (c : EmbeddedChart 1 1 3 B) (u : c.source) : ℝ :=
  ⟪F (c.toFun u), chartDifferential c u (standardBasis 1 0)⟫

/-- The positively oriented unit tangent in a chart of sign s. -/
def chartUnitTangent {B : Set (E 3)} (c : EmbeddedChart 1 1 3 B)
    (u : c.source) (s : ℝ) : E 3 :=
  (s / ‖chartDifferential c u (standardBasis 1 0)‖) •
    chartDifferential c u (standardBasis 1 0)

/-- This is a chart definition of boundary work with explicit Riemann
integrability and independence of every signed partition. -/
def HasBoundaryWorkIntegral {B : Set (E 3)}
    (bO : PositiveManifoldOrientation 1 1 B) (F : E 3 → E 3) (I : ℝ) : Prop :=
  let eta := tangentRestriction 1 1 B (alpha F)
  ContinuousTopField eta ∧ IsCompact (topSupport eta) ∧
    Nonempty (SignedChartPartition bO (topSupport eta)) ∧
    ∀ P : SignedChartPartition bO (topSupport eta),
      (∀ i, ProperIntegrable (fun u : (P.chart i).source =>
        P.weight i ((P.chart i).toFun u) * workCoefficient F (P.chart i) u)) ∧
      (∑ i, (P.sign i).val * coefficientIntegral (fun u : (P.chart i).source =>
        P.weight i ((P.chart i).toFun u) * workCoefficient F (P.chart i) u)) = I

/-- Parametrized flux, using the actual C15 cell and its C10 cross-product
area coefficient. The equality to that coefficient is proved below. -/
def cellFlux {O : Set (E 3)}
    (c : Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell 1 2 O)
    (F : E 3 → E 3) : ℝ :=
  Specs.D04.C15.CellsChainsAndIntegrals.Model.cellIntegral c (beta F)

end Model
open Model

abbrev NormalCompatibleType := {M : Set (E 3)} → UnitNormalField M →
  PositiveManifoldOrientation 1 2 M → Prop
def NormalCompatibleValue : NormalCompatibleType := @Model.NormalCompatible
abbrev workCoefficientType := {B : Set (E 3)} → (E 3 → E 3) →
  (c : EmbeddedChart 1 1 3 B) → c.source → ℝ
def workCoefficientValue : workCoefficientType := @Model.workCoefficient
abbrev chartUnitTangentType := {B : Set (E 3)} → (c : EmbeddedChart 1 1 3 B) →
  c.source → ℝ → E 3
def chartUnitTangentValue : chartUnitTangentType := @Model.chartUnitTangent
abbrev HasBoundaryWorkIntegralType := {B : Set (E 3)} →
  PositiveManifoldOrientation 1 1 B → (E 3 → E 3) → ℝ → Prop
def HasBoundaryWorkIntegralValue : HasBoundaryWorkIntegralType := @Model.HasBoundaryWorkIntegral

abbrev cellFluxType := {O : Set (E 3)} →
  Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell 1 2 O → (E 3 → E 3) → ℝ
def cellFluxValue : cellFluxType := @Model.cellFlux

def positive_chart_fluxType : Prop :=
  ∀ {M : Set (E 3)} (N : UnitNormalField M)
    (o : PositiveManifoldOrientation 1 2 M), NormalCompatible N o →
    ∀ (F : E 3 → E 3) (c : EmbeddedChart 1 2 3 M) (u : c.source),
      chartSign o.atPoint c u u.property = 1 →
      topCoefficient (tangentRestriction 1 2 M (beta F)) c u =
        ⟪F (c.toFun u), euclideanCross (chartDifferential c u (standardBasis 2 0))
          (chartDifferential c u (standardBasis 2 1))⟫ ∧
      topCoefficient (tangentRestriction 1 2 M (beta F)) c u =
        ⟪F (c.toFun u), N.toFun (chartPoint c u)⟫ * chartDensity c u

def boundary_work_bridgeType : Prop :=
  ∀ {B : Set (E 3)} (bO : PositiveManifoldOrientation 1 1 B)
    (F : E 3 → E 3) (I : ℝ),
    HasBoundaryWorkIntegral bO F I ↔
      HasManifoldIntegral 1 1 bO (tangentRestriction 1 1 B (alpha F)) I

def boundary_chart_speedType : Prop :=
  ∀ {B : Set (E 3)} (c : EmbeddedChart 1 1 3 B) (u : c.source) (s : ℝ)
    (F : E 3 → E 3),
    s * workCoefficient F c u =
      ⟪F (c.toFun u), chartUnitTangent c u s⟫ * chartDensity c u ∧
    ((s = 1 ∨ s = -1) → ‖chartUnitTangent c u s‖ = 1)

def boundary_path_workType : Prop :=
  ∀ {a b : ℝ} {γ : Specs.D04.C09.PathsLength.Model.IntervalPath 3 a b}
    (d : Specs.D04.C09.PathsLength.Model.PiecewiseC1Data γ) (F : E 3 → E 3)
    (h : OneFormIntegrable d (alpha F)),
    oneFormIntegral d (alpha F) h =
      Specs.D04.C09.LineIntegrals.Model.workLineIntegral d F h

/-- Compatibility with the original orientation is a chart-sign condition,
not an integral or Stokes certificate. The conclusion includes the Chapter 10
geometric flux and its canonical Chapter 15 identification. -/
def surface_stokesType : Prop :=
  ∀ {M : Set (E 3)} (hM : IsEmbeddedManifold 1 2 M), IsCompact M →
    ∀ N : UnitNormalField M,
    ∃ o : PositiveManifoldOrientation 1 2 M, NormalCompatible N o ∧
      ∀ (O : Set (E 3)) (F : E 3 → E 3), IsOpen O → M ⊆ O → CrOn 1 O F →
      ∃ bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 M),
        OutwardFirst 1 o bO ∧
        HasPositiveIntegral o (surfaceFluxForm (fun x : M => curl F x))
          (surfaceFlux N (fun x : M => curl F x)) ∧
        HasBoundaryWorkIntegral bO F (surfaceFlux N (fun x : M => curl F x))

/-- The outward-first sign determines the actual unit boundary tangent. -/
def boundary_tangent_crossType : Prop :=
  ∀ {M : Set (E 3)} (N : UnitNormalField M)
    (o : PositiveManifoldOrientation 1 2 M), NormalCompatible N o →
    ∀ (x : intrinsicBoundary 1 2 M) (nu : E 3),
      IsOutwardUnitConormal 1 1 M x nu →
    ∀ b : OrthonormalBasis (Fin 1) ℝ (tangentSpace 1 1 (intrinsicBoundary 1 2 M) x),
      PositiveWithOutward o x nu b.toBasis →
        (b 0).val = euclideanCross (N.toFun ⟨x, x.property.1⟩) nu


open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteGeometricUnionIntegral.Model
/-- Finite oriented surface unions, with the complete C15 geometric matching
conditions. No manifold structure on the whole union is required. The bulk
value is identified with the sum of the existing geometric C10 fluxes. -/
def finite_surface_stokesType : Prop :=
∀ {q} {O : Set (E 3)} (M : Fin q → CompactManifold (0+1) 3 O)
    (N : (j : Fin q) → UnitNormalField (M j).carrier)
    (compatible : ∀ j, NormalCompatible (N j) (M j).orientation)
    (bO : (j : Fin q) → PositiveManifoldOrientation 1 (0+1)
      (intrinsicBoundary 1 (0+2) (M j).carrier)),
    (∀ j, OutwardFirst (0+1) (M j).orientation (bO j)) →
    ∀ (m : Fin q → ℕ) (P : (j : Fin q) → Fin (m j) → Patch (0+1) O)
      (s : (j : Fin q) → Fin (m j) → PointSign),
    (∀ j t, RegularPiece (bO j) (P j t) (s j t)) →
    ∀ Z : Fin q → Seams 3, (∀ j i, (Z j).dim i < 0+1) →
    (∀ j t u, u ∈ (P j t).region → ∀ v, v ∈ (P j t).region → u ≠ v →
      (P j t).map u = (P j t).map v → (P j t).map u ∈ (Z j).carrier) →
    (∀ j t u, t ≠ u → ((P j t).map '' (P j t).region) ∩
      ((P j u).map '' (P j u).region) ⊆ (Z j).carrier) →
    (∀ j, intrinsicBoundary 1 (0+2) (M j).carrier ⊆
      (⋃ t, (P j t).map '' (P j t).region) ∪ (Z j).carrier) →
    ∀ Zbulk : AmbientSeams (0+2) 3,
    (∀ i j, i ≠ j → (M i).carrier ∩ (M j).carrier ⊆ Zbulk.carrier) →
    ∀ {l p : ℕ}
      (e : (Fin l ⊕ (Fin p × Bool)) ≃ ((j : Fin q) × Fin (m j)))
      (Q : Fin l → Patch (0+1) O) (tSign : Fin l → PointSign) (b : Fin l → ℤ)
      (deltaOut : Fin l → ℝ),
    (∀ t, deltaOut t = 1 ∨ deltaOut t = -1) →
    ∀ hOut : (t : Fin l) → LocalReparametrization
      (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).region (Q t).region (deltaOut t),
    (∀ t, EqOn (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).map
      ((Q t).map ∘ (hOut t).map) (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).region ∧
      (s (e (Sum.inl t)).1 (e (Sum.inl t)).2).val * deltaOut t = (tSign t).val ∧
      b t = 1) →
    ∀ deltaPair : Fin p → ℝ, (∀ i, deltaPair i = 1 ∨ deltaPair i = -1) →
    ∀ hPair : (i : Fin p) → LocalReparametrization
      (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).region
      (P (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).region (deltaPair i),
    (∀ i, EqOn (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).map
      ((P (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).map ∘ (hPair i).map)
      (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).region ∧
      (s (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).val * deltaPair i =
        -(s (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).val) →
    ∀ F : E 3 → E 3, IsOpen O → CrOn 1 O F →
    ∃ D : GeometricDecomposition (0+2) 3 O,
      D.carrier = ⋃ j, (M j).carrier ∧
      geometricUnionIntegral D (exteriorDerivative (alpha F)) =
        ∑ j, surfaceFlux (N j) (fun x : (M j).carrier => curl F x) ∧
      (∑ j, surfaceFlux (N j) (fun x : (M j).carrier => curl F x)) =
        ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) (alpha F))

open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C15.FinitePiecewiseStokes.Model

/-- Regular cell assemblies include cornered pieces and piecewise regular
outer boundaries. Both directed seam matching and multiplicity one are explicit. -/
def finite_cell_surface_stokesType : Prop :=
∀ {N L : ℕ} {O : Set (E 3)} (c : Fin N → Cell 1 (1+1) O)
    (P : Fin N → Fin (1+1) → Bool → Patch 1 O),
    (∀ j i e, (P j i e).region = cube 1 ∧
      EqOn (P j i e).map (cellExtension (cellFace (c j) i e)) (cube 1)) →
    ∀ (outer : PatchChain 1 O) (left right : Fin L → WeightedPatch 1 O)
      (b s : Fin L → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) →
    (∀ i, ∃ h : LocalReparametrization (left i).patch.region (right i).patch.region (s i : ℝ),
      EqOn (left i).patch.map ((right i).patch.map ∘ h.map) (left i).patch.region) →
    (∀ i, EqOn (left i).weight (right i).weight ((right i).patch.map '' (right i).patch.region)) →
    GeometricEquivalent (∑ j, (1 : ℤ) • patchBoundary (P j))
      (outer + ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1)) →
    (∀ j, InjOn (cellExtension (c j)) (cube (1+1))) →
    (∀ j x, x ∈ cube (1+1) → Function.Injective (fderiv ℝ (cellExtension (c j)) x)) →
    ∀ Z : AmbientSeams (1+1) 3,
    (∀ i j, i ≠ j → (cellExtension (c i) '' cube (1+1)) ∩
      (cellExtension (c j) '' cube (1+1)) ⊆ Z.carrier) →
    ∀ F : E 3 → E 3, IsOpen O → CrOn 1 O F →
      ∃ D : GeometricDecomposition (1+1) 3 O,
        D.carrier = ⋃ j, cellExtension (c j) '' cube (1+1) ∧
        geometricUnionIntegral D (exteriorDerivative (alpha F)) = ∑ j, cellFlux (c j) (curl F) ∧
        (∑ j, cellFlux (c j) (curl F)) = patchChainIntegral (alpha F) outer

/-- The actual parametrized C10 flux integrand, with no assumed integral equality. -/
def cell_flux_coefficientType : Prop :=
  ∀ {O : Set (E 3)} (c : Cell 1 2 O) (F : E 3 → E 3) (u : E 2),
    cellCoefficient c (beta F) u =
      ⟪F (cellExtension c u), euclideanCross
        (fderiv ℝ (cellExtension c) u (standardBasis 2 0))
        (fderiv ℝ (cellExtension c) u (standardBasis 2 1))⟫

/-- Work on each outer or internal displayed boundary piece. -/
def patch_work_coefficientType : Prop :=
  ∀ {O : Set (E 3)} (P : Patch 1 O) (F : E 3 → E 3) (u : E 1),
    Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.coefficient P (alpha F) u =
      ⟪F (P.map u), fderiv ℝ P.map u (standardBasis 1 0)⟫

/-- The theorem applies to any supplied orientation and its corresponding
normal; it is not restricted to an existentially chosen orientation. -/
def surface_stokes_orientedType : Prop :=
  ∀ {M : Set (E 3)} (N : UnitNormalField M)
    (o : PositiveManifoldOrientation 1 2 M), NormalCompatible N o → IsCompact M →
    ∀ (O : Set (E 3)) (F : E 3 → E 3), IsOpen O → M ⊆ O → CrOn 1 O F →
    ∃ bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 M),
      OutwardFirst 1 o bO ∧
      HasPositiveIntegral o (surfaceFluxForm (fun x : M => curl F x))
        (surfaceFlux N (fun x : M => curl F x)) ∧
      HasBoundaryWorkIntegral bO F (surfaceFlux N (fun x : M => curl F x))

/-- Full normalized pullback forms, in addition to their coefficient equalities. -/
def positive_chart_pullbackType : Prop :=
  ∀ {M : Set (E 3)} (N : UnitNormalField M)
    (o : PositiveManifoldOrientation 1 2 M), NormalCompatible N o →
    ∀ (F : E 3 → E 3) (c : EmbeddedChart 1 2 3 M) (u : c.source),
      chartSign o.atPoint c u u.property = 1 →
      tangentPullback (tangentRestriction 1 2 M (beta F)) c u u.property =
        ⟪F (c.toFun u), euclideanCross (chartDifferential c u (standardBasis 2 0))
          (chartDifferential c u (standardBasis 2 1))⟫ • omega 2 ∧
      tangentPullback (tangentRestriction 1 2 M (beta F)) c u u.property =
        (⟪F (c.toFun u), N.toFun (chartPoint c u)⟫ * chartDensity c u) • omega 2

/-- The sign-adjusted chart tangent is the positive unit tangent of the
chosen boundary orientation, so the speed formula is F dot tau ds. -/
def chart_unit_tangent_positiveType : Prop :=
  ∀ {B : Set (E 3)} (bO : PositiveManifoldOrientation 1 1 B)
    (c : EmbeddedChart 1 1 3 B) (u : c.source),
    ∃ b : OrthonormalBasis (Fin 1) ℝ (tangentSpace 1 1 B (c.toFun u)),
      b.toBasis.orientation = bO.atPoint (c.toFun u) (c.map_source u.property).1 ∧
      (b 0).val = chartUnitTangent c u (chartSign bO.atPoint c u u.property)

/-- The cell value is the existing Chapter 10 parametrized geometric flux,
not merely a new name for a differential-form integral. -/
def cell_flux_geometricType : Prop :=
  ∀ {O : Set (E 3)} (c : Cell 1 2 O) (F : E 3 → E 3), ContinuousOn F O →
    cellFlux c F = Specs.D04.C10.AreaIntegral.Model.fluxIntegral (cube 2)
      (cellExtension c) (fun x => F x)

end Specs.D04.C12.ClassicalSurfaceStokes
