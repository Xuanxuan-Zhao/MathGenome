import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.GraphArea
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The geometric flux assertion used in paper.tex:242–267.
The boundary measure is the shared Euclidean-normalized Hausdorff measure.
Normal vectors are characterized geometrically, independently of any integration
identity. Dimension m+1 includes m=0, empty sets, and disconnected open sets.

C¹ data on an open neighborhood of the closure suffice for the identity; this
also covers the smooth-up-to-boundary data in the source. No boundary smoothness
beyond the shared one-sided Lipschitz graph condition is imposed.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology NNReal

namespace P201Specs.SmoothFlux

/-- The intrinsic outward unit normal in the canonical Euclidean graph frame.
The definition uses the tangent cone and the interior/exterior normal rays from
the graph-area interface, not a flux identity or a weak normal trace. -/
def GeometricNormalAt {m : ℕ} (Ω : Domain (m + 1))
    (p w : Space (m + 1)) : Prop :=
  P102.U4.GraphArea.OutwardUnitNormal
    (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set _)
    (frontier (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set _))
    ((graphFrame m).symm p) ((graphFrame m).symm w)

/-- An actual measurable geometric normal, specified up to boundary a.e. equality. -/
def IsGeometricNormalField {m : ℕ} (Ω : Domain (m + 1))
    (ν : Space (m + 1) → Space (m + 1)) : Prop :=
  AEStronglyMeasurable ν (boundaryMeasure Ω) ∧
    ∀ᵐ p ∂boundaryMeasure Ω, GeometricNormalAt Ω p (ν p)

/-- The full assigned obligation. In particular normal existence, genuine
integrability, and the flux formula are conclusions, not input certificates. -/
def SmoothFluxStatement : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    ∃ ν : Space (m + 1) → Space (m + 1),
      IsGeometricNormalField Ω ν ∧
      ∀ (U : Set (Space (m + 1))) (F : Space (m + 1) → Space (m + 1))
        (v : Space (m + 1) → ℝ),
        IsOpen U → closure (Ω : Set (Space (m + 1))) ⊆ U →
        ContDiffOn ℝ 1 F U → ContDiffOn ℝ 1 v U →
        IntegrableOn (fun x => inner ℝ (F x) (gradient v x) + divergence F x * v x)
          (Ω : Set (Space (m + 1))) volume ∧
        Integrable (fun x => v x * inner ℝ (F x) (ν x)) (boundaryMeasure Ω) ∧
        (∫ x in (Ω : Set (Space (m + 1))),
          inner ℝ (F x) (gradient v x) + divergence F x * v x) =
            ∫ x, v x * inner ℝ (F x) (ν x) ∂boundaryMeasure Ω

/-- The product rule reducing the desired Green integrand to div(vF). -/
def DivergenceProductStatement : Prop :=
  ∀ {n : ℕ} (F : Space n → Space n) (v : Space n → ℝ) (x : Space n),
    DifferentiableAt ℝ F x → DifferentiableAt ℝ v x →
    divergence (fun y => v y • F y) x =
      inner ℝ (F x) (gradient v x) + divergence F x * v x

open P102.U4.GraphPieces P102.U4.GraphArea in
/-- The normalized area formula gives precisely (grad ψ,-1) dx'.
The equivalence also records that these are genuine integrable fluxes. -/
def GraphFluxStatement : Prop :=
  ∀ (m : ℕ) (U : Opens (Space m)) (ψ : Space m → ℝ) (L : ℝ≥0),
    LipschitzOnWith L ψ U →
    ∀ a : Space m → Space m, GradientRepresentative U ψ a →
    ∀ (F : Ambient m → Ambient m) (v : Ambient m → ℝ),
      (Integrable (fun z => v z * inner ℝ (F z) (normalField a z)) (surfaceMeasure U ψ) ↔
        IntegrableOn (fun x => v (graph ψ x) *
          inner ℝ (F (graph ψ x)) (conormal (a x))) U volume) ∧
      (∫ z, v z * inner ℝ (F z) (normalField a z) ∂surfaceMeasure U ψ) =
        ∫ x in (U : Set (Space m)), v (graph ψ x) *
          inner ℝ (F (graph ψ x)) (conormal (a x))

open P102.U4.GraphPieces P102.U4.GraphArea in
/-- The graph normal has the outward sign, for every nonnegative m. -/
def GraphNormalStatement : Prop :=
  ∀ (m : ℕ) (U : Opens (Space m)) (ψ : Space m → ℝ) (L : ℝ≥0),
    LipschitzOnWith L ψ U →
    ∀ a : Space m → Space m, GradientRepresentative U ψ a →
      (∀ᵐ z ∂surfaceMeasure U ψ,
        OutwardUnitNormal (epigraphSide U ψ) (graph ψ '' (U : Set (Space m)))
          z (normalField a z)) ∧
      ∀ x, jacobian (a x) • normalField a (graph ψ x) = conormal (a x)

/-- The signed endpoint computation in physical real coordinates.
Integrability of derivatives follows from the C¹ hypotheses. -/
def IntervalFluxStatement : Prop :=
  ∀ (a b : ℝ) (F v : ℝ → ℝ), a ≤ b →
    ContDiffOn ℝ 1 F (Icc a b) → ContDiffOn ℝ 1 v (Icc a b) →
    (∫ x in Ioo a b, F x * derivWithin v (Icc a b) x +
      derivWithin F (Icc a b) x * v x) = v b * F b - v a * F a

/-- Boundary finiteness is geometric, without a trace or flux hypothesis. -/
def BoundaryFiniteStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    boundaryMeasure Ω univ < ⊤

def BulkIntegrableStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    ∀ (U : Set (Space (m + 1))) (F : Space (m + 1) → Space (m + 1))
      (v : Space (m + 1) → ℝ), IsOpen U →
      closure (Ω : Set (Space (m + 1))) ⊆ U →
      ContDiffOn ℝ 1 F U → ContDiffOn ℝ 1 v U →
      IntegrableOn (fun x => inner ℝ (F x) (gradient v x) + divergence F x * v x)
        (Ω : Set (Space (m + 1))) volume

def BoundaryFluxIntegrableStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    ∀ ν : Space (m + 1) → Space (m + 1), IsGeometricNormalField Ω ν →
    ∀ (F : Space (m + 1) → Space (m + 1)) (v : Space (m + 1) → ℝ),
      ContinuousOn F (frontier (Ω : Set (Space (m + 1)))) →
      ContinuousOn v (frontier (Ω : Set (Space (m + 1)))) →
      Integrable (fun x => v x * inner ℝ (F x) (ν x)) (boundaryMeasure Ω)

/-- The interior pieces in the partition have no boundary contribution. -/
def InteriorDivergenceStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (W : Space n → Space n),
    ContDiff ℝ 1 W → HasCompactSupport W → tsupport W ⊆ (Ω : Set (Space n)) →
    IntegrableOn (divergence W) (Ω : Set (Space n)) volume ∧
      (∫ x in (Ω : Set (Space n)), divergence W x) = 0

open P102.U4.GraphPieces in
/-- Vertical FTC in an epigraph, with its outward (negative) sign.
This is a slice identity, not the full epigraph divergence formula. -/
def VerticalSliceStatement : Prop :=
  ∀ {m : ℕ} (W : Ambient m → Ambient m),
    ContDiff ℝ 1 W → HasCompactSupport W →
    ∀ (x : Space m) (b : ℝ),
      IntegrableOn
        (fun t => fderiv ℝ (fun z => (W z).ofLp.2) (WithLp.toLp 2 (x, t))
          (WithLp.toLp 2 (0, (1 : ℝ)))) (Ioi b) volume ∧
      (∫ t in Ioi b,
        fderiv ℝ (fun z => (W z).ofLp.2) (WithLp.toLp 2 (x, t))
          (WithLp.toLp 2 (0, (1 : ℝ)))) = -(W (WithLp.toLp 2 (x, b))).ofLp.2

open P102.U4.GraphPieces P102.U4.GraphArea in
/-- The full vertical contribution to the local epigraph computation. -/
def VerticalEpigraphStatement : Prop :=
  ∀ {m : ℕ} (U : Opens (Space m)) (ψ : Space m → ℝ) (L : ℝ≥0),
    LipschitzOnWith L ψ U → ∀ W : Ambient m → Ambient m,
    ContDiff ℝ 1 W → HasCompactSupport W →
      IntegrableOn
        (fun z => fderiv ℝ (fun z => (W z).ofLp.2) z (WithLp.toLp 2 (0, (1 : ℝ))))
        (epigraphSide U ψ) volume ∧
      IntegrableOn (fun x => (W (graph ψ x)).ofLp.2) U volume ∧
      (∫ z in epigraphSide U ψ,
        fderiv ℝ (fun z => (W z).ofLp.2) z (WithLp.toLp 2 (0, (1 : ℝ)))) =
          -(∫ x in (U : Set (Space m)), (W (graph ψ x)).ofLp.2)

/-- Differentiating a partition that is one on a neighborhood cancels all
partition derivatives, pointwise in the shared divergence convention. -/
def PartitionDivergenceStatement : Prop :=
  ∀ {n k : ℕ} (χ : Fin k → Space n → ℝ) (W : Space n → Space n)
    (x : Space n), (∀ i, DifferentiableAt ℝ (χ i) x) →
    DifferentiableAt ℝ W x →
    (∀ᶠ y in 𝓝 x, ∑ i, χ i y = 1) →
      (∑ i, divergence (fun y => χ i y • W y) x) = divergence W x

/-- C¹ data near a compact set can be replaced by a global compact C¹
field agreeing on a neighborhood, with support inside the supplied data set. -/
def CompactLocalizationStatement : Prop :=
  ∀ {n : ℕ} (K U : Set (Space n)) (W : Space n → Space n),
    IsCompact K → IsOpen U → K ⊆ U → ContDiffOn ℝ 1 W U →
    ∃ (Z : Space n → Space n) (V : Set (Space n)),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ ContDiff ℝ 1 Z ∧
      HasCompactSupport Z ∧ tsupport Z ⊆ U ∧ EqOn Z W V

/-- Finite local flux identities combine whenever the weights are one near the
closure. The hypotheses are the individual identities to be obtained from the
interior and graph calculations; this is only their algebraic assembly. -/
def FiniteFluxAssemblyStatement : Prop :=
  ∀ {n k : ℕ} (Ω : Domain n) (μ : Measure (Space n))
    (ν W : Space n → Space n) (χ : Fin k → Space n → ℝ)
    (V : Set (Space n)), IsOpen V → closure (Ω : Set (Space n)) ⊆ V →
    ContDiffOn ℝ 1 W V → (∀ i, ContDiff ℝ 1 (χ i)) →
    (∀ x ∈ V, ∑ i, χ i x = 1) →
    (∀ᵐ x ∂μ, x ∈ closure (Ω : Set (Space n))) →
    (∀ i, IntegrableOn (divergence (fun x => χ i x • W x)) Ω volume) →
    (∀ i, Integrable (fun x => χ i x * inner ℝ (W x) (ν x)) μ) →
    (∀ i, (∫ x in (Ω : Set (Space n)), divergence (fun y => χ i y • W y) x) =
      ∫ x, χ i x * inner ℝ (W x) (ν x) ∂μ) →
    IntegrableOn (divergence W) Ω volume ∧
      Integrable (fun x => inner ℝ (W x) (ν x)) μ ∧
      (∫ x in (Ω : Set (Space n)), divergence W x) =
        ∫ x, inner ℝ (W x) (ν x) ∂μ

/-- The one-dimensional ACL fundamental theorem needed on horizontal lines.
The Lipschitz hypothesis permits an exceptional set of derivative points. -/
def CompactLipschitzFTCStatement : Prop :=
  ∀ (f : ℝ → ℝ) (L : ℝ≥0), LipschitzWith L f → HasCompactSupport f →
    Integrable (deriv f) ∧ (∫ x, deriv f x) = 0

open P102.U4.GraphPieces P102.U4.GraphArea P102.Sobolev.Geometry in
open P102.Sobolev.Extension in
/-- The chart surface measure is the exact physical boundary measure in its
chart image, with Euclidean normalization, including dimension one. -/
def ChartSurfaceMapStatement : Prop :=
  ∀ (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Domain (m + 1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))),
    Measure.map (fun z => e (C.frame z))
      (surfaceMeasure ⟨Metric.ball C.center C.radius, Metric.isOpen_ball⟩ C.graphFunction) =
      (boundaryMeasure Ω).restrict
        (e '' chartImage C.frame C.graphFunction C.center C.radius C.height)

open P102.U4.GraphPieces in
/-- Divergence is invariant under the rigid frame used by a boundary chart.
The last coordinate has the physical unit-speed normalization. -/
def AffineChartDivergenceStatement : Prop :=
  ∀ {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (F : Space (m + 1) → Space (m + 1)) (z : Ambient m),
    DifferentiableAt ℝ F (graphFrame m (e z)) →
    let W : Ambient m → Ambient m := fun y => e.linearIsometryEquiv.symm
      ((graphFrame m).symm (F (graphFrame m (e y))))
    divergence F (graphFrame m (e z)) =
      (∑ i : Fin m, fderiv ℝ (fun y => (W y).ofLp.1 i) z
        (WithLp.toLp 2 (coordinate m i, (0 : ℝ)))) +
      fderiv ℝ (fun y => (W y).ofLp.2) z
        (WithLp.toLp 2 ((0 : Space m), (1 : ℝ)))

/-- Differentiation of the primitive along an upward ray. Compact support
provides the uniform local bound required for differentiation under the integral. -/
def RayPrimitiveStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ), ContDiff ℝ 1 f → HasCompactSupport f →
    ∀ (e : E), ‖e‖ = 1 → ∀ z₀ : E,
      HasFDerivAt (fun z => ∫ t in Ioi (0 : ℝ), f (z + t • e))
        (∫ t in Ioi (0 : ℝ), fderiv ℝ f (z₀ + t • e)) z₀

open P102.U4.GraphPieces P102.U4.GraphArea P102.Sobolev.Geometry in
/-- A differentiable chart point gives a genuine normal to the original set
and the complete tangent hyperplane, independent of any flux identity. -/
def ChartNormalStatement : Prop :=
  ∀ {m : ℕ} {G : Set (Ambient m)} (C : BoundaryChart G)
    (x a : Space m), x ∈ Metric.ball C.center C.radius →
    HasFDerivAt C.graphFunction (innerSL ℝ a) x →
    OutwardUnitNormal G (frontier G) (C.frame (graph C.graphFunction x))
      (C.frame.linearIsometryEquiv (unitNormal a)) ∧
    tangentConeAt ℝ (frontier G) (C.frame (graph C.graphFunction x)) =
      ((ℝ ∙ C.frame.linearIsometryEquiv (unitNormal a))ᗮ : Set (Ambient m))

open P102.U4.GraphPieces P102.Sobolev.Extension in
/-- A genuine Borel outward unit normal exists on every bounded Lipschitz open
set. The tangent hyperplane characterization also gives a.e. uniqueness. -/
def GeometricNormalExistsStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    ∃ ν : Space (m + 1) → Space (m + 1), Measurable ν ∧
      IsGeometricNormalField Ω ν ∧
      ∀ᵐ p ∂boundaryMeasure Ω,
        tangentConeAt ℝ (frontier (geometricOpen (graphFrame m) Ω : Set (Ambient m)))
          ((graphFrame m).symm p) =
            ((ℝ ∙ (graphFrame m).symm (ν p))ᗮ : Set (Ambient m))

open P102.U4.GraphPieces in
/-- The variable lower-limit derivative at every graph differentiability point.
No differentiability of the Lipschitz graph at other points is required. -/
def GraphPrimitiveDerivativeStatement : Prop :=
  ∀ {m : ℕ} (f : Ambient m → ℝ), ContDiff ℝ 1 f → HasCompactSupport f →
    ∀ (ψ : Space m → ℝ) {x a : Space m}, HasFDerivAt ψ (innerSL ℝ a) x →
    ∀ q : Space m,
    fderiv ℝ (fun x => ∫ t in Ioi (0 : ℝ),
      f (graph ψ x + t • (WithLp.toLp 2 (0, (1 : ℝ)) : Ambient m))) x q =
      (∫ t in Ioi (0 : ℝ),
        fderiv ℝ f (graph ψ x + t • (WithLp.toLp 2 (0, (1 : ℝ)) : Ambient m))
          (WithLp.toLp 2 (q, (0 : ℝ)))) - inner ℝ a q * f (graph ψ x)

open P102.U4.GraphPieces P102.U4.GraphArea P102.Sobolev.Geometry P102.Sobolev.Extension in
/-- Every geometric normal field has the same chart representative a.e. for
the actual Euclidean-normalized graph surface measure. -/
def GeometricNormalChartStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1))
    (C : BoundaryChart (geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (a : Space m → Space m),
    GradientRepresentative ⟨Metric.ball C.center C.radius, Metric.isOpen_ball⟩ C.graphFunction a →
    ∀ ν : Space (m + 1) → Space (m + 1), IsGeometricNormalField Ω ν →
    ∀ᵐ z ∂surfaceMeasure ⟨Metric.ball C.center C.radius, Metric.isOpen_ball⟩ C.graphFunction,
      ν (graphFrame m (C.frame z)) =
        graphFrame m (C.frame.linearIsometryEquiv (normalField a z))

/-- The measurable outward unit normal is unique modulo boundary-null sets. -/
def GeometricNormalUniqueStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    ∀ ν η : Space (m + 1) → Space (m + 1),
    IsGeometricNormalField Ω ν → IsGeometricNormalField Ω η →
      ν =ᵐ[boundaryMeasure Ω] η

open P102.U4.GraphPieces P102.U4.GraphArea P102.Sobolev.Geometry P102.Sobolev.Extension in
/-- Localized physical flux has exactly the conormal graph integral, with the
same genuine integrability condition on each side. -/
def PhysicalChartFluxStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1))
    (C : BoundaryChart (geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (a : Space m → Space m),
    GradientRepresentative ⟨Metric.ball C.center C.radius, Metric.isOpen_ball⟩ C.graphFunction a →
    ∀ ν : Space (m + 1) → Space (m + 1), IsGeometricNormalField Ω ν →
    ∀ W : Space (m + 1) → Space (m + 1),
    tsupport W ⊆ graphFrame m ''
      chartImage C.frame C.graphFunction C.center C.radius C.height →
    (∫ p, inner ℝ (W p) (ν p) ∂boundaryMeasure Ω) =
      ∫ x in Metric.ball C.center C.radius,
        inner ℝ (C.frame.linearIsometryEquiv.symm ((graphFrame m).symm
          (W (graphFrame m (C.frame (graph C.graphFunction x)))))) (conormal (a x))

open P102.U4.GraphPieces P102.U4.GraphArea P102.Sobolev.Geometry P102.Sobolev.Extension in
def PhysicalChartFluxIntegrableStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1))
    (C : BoundaryChart (geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (a : Space m → Space m),
    GradientRepresentative ⟨Metric.ball C.center C.radius, Metric.isOpen_ball⟩ C.graphFunction a →
    ∀ ν : Space (m + 1) → Space (m + 1), IsGeometricNormalField Ω ν →
    ∀ W : Space (m + 1) → Space (m + 1),
    tsupport W ⊆ graphFrame m ''
      chartImage C.frame C.graphFunction C.center C.radius C.height →
    (Integrable (fun p => inner ℝ (W p) (ν p)) (boundaryMeasure Ω) ↔
      IntegrableOn (fun x =>
        inner ℝ (C.frame.linearIsometryEquiv.symm ((graphFrame m).symm
          (W (graphFrame m (C.frame (graph C.graphFunction x)))))) (conormal (a x)))
        (Metric.ball C.center C.radius) volume)

open Metric P102.U4.GraphPieces P102.U4.GraphArea P102.Sobolev.Geometry
  P102.Sobolev.Extension in
/-- Exact bulk transport to the epigraph for a compact C¹ field supported in
one chart. This uses the chart's actual one-sided set equality. -/
def LocalBulkTransportStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m+1))
    (C : BoundaryChart (geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (W : Space (m+1) → Space (m+1)) (hW : ContDiff ℝ 1 W)
    (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ (graphFrame m) ''
      chartImage C.frame C.graphFunction C.center C.radius C.height),
    let Z : Ambient m → Ambient m := fun y => C.frame.linearIsometryEquiv.symm
      ((graphFrame m).symm (W (graphFrame m (C.frame y))))
    let d : Ambient m → ℝ := fun z =>
      (∑ i : Fin m, fderiv ℝ (fun y => (Z y).ofLp.1 i) z
        (WithLp.toLp 2 (coordinate m i, (0 : ℝ)))) +
      fderiv ℝ (fun y => (Z y).ofLp.2) z
        (WithLp.toLp 2 ((0 : Space m), (1 : ℝ)))
    let D := epigraphSide (⟨ball C.center C.radius, isOpen_ball⟩ : Opens (Space m)) C.graphFunction
    IntegrableOn (divergence W) Ω ∧ IntegrableOn d D ∧
      (∫ x in Ω, divergence W x) = ∫ z in D, d z

/-- Compact Lipschitz functions have integrable directional derivatives and
zero total directional derivative integral. -/
def CompactLipschitzDirectionalStatement : Prop :=
  ∀ {m : ℕ} {f : Space m → ℝ} {L : ℝ≥0}, LipschitzWith L f →
    HasCompactSupport f → ∀ q : Space m,
      Integrable (fun x => fderiv ℝ f x q) ∧ (∫ x, fderiv ℝ f x q) = 0

open P102.U4.GraphPieces P102.U4.GraphArea in
/-- The horizontal contribution for an arbitrary direction in a Lipschitz
epigraph. The graph term and volume derivative are genuinely integrable. -/
def HorizontalEpigraphScalarStatement : Prop :=
  ∀ {m : ℕ} (U : Opens (Space m)) (ψ : Space m → ℝ) (L : ℝ≥0),
    LipschitzOnWith L ψ U → ∀ a : Space m → Space m,
    GradientRepresentative U ψ a → ∀ f : Ambient m → ℝ,
    ContDiff ℝ 1 f → HasCompactSupport f →
    tsupport f ⊆ (horizontal (m := m)) ⁻¹' (U : Set (Space m)) →
    ∀ q : Space m,
    IntegrableOn (fun z => fderiv ℝ f z (WithLp.toLp 2 (q, (0 : ℝ))))
      (epigraphSide U ψ) volume ∧
    IntegrableOn (fun x => f (graph ψ x) * inner ℝ (a x) q) U volume ∧
    (∫ z in epigraphSide U ψ, fderiv ℝ f z (WithLp.toLp 2 (q, (0 : ℝ)))) =
      ∫ x in (U : Set (Space m)), f (graph ψ x) * inner ℝ (a x) q

open P102.U4.GraphPieces P102.U4.GraphArea in
/-- The complete local divergence identity in an epigraph, including dimension
one, with the exact unnormalized conormal and genuine integrability. -/
def EpigraphFluxStatement : Prop :=
  ∀ {m : ℕ} (U : Opens (Space m)) (ψ : Space m → ℝ) (L : ℝ≥0),
    LipschitzOnWith L ψ U → ∀ a : Space m → Space m,
    GradientRepresentative U ψ a → ∀ W : Ambient m → Ambient m,
    ContDiff ℝ 1 W → HasCompactSupport W →
    tsupport W ⊆ (horizontal (m := m)) ⁻¹' (U : Set (Space m)) →
    IntegrableOn (fun z =>
      (∑ i : Fin m, fderiv ℝ (fun y => (W y).ofLp.1 i) z
        (WithLp.toLp 2 (coordinate m i, (0 : ℝ)))) +
      fderiv ℝ (fun y => (W y).ofLp.2) z
        (WithLp.toLp 2 ((0 : Space m), (1 : ℝ)))) (epigraphSide U ψ) volume ∧
    IntegrableOn (fun x => inner ℝ (W (graph ψ x)) (conormal (a x))) U volume ∧
    (∫ z in epigraphSide U ψ,
      (∑ i : Fin m, fderiv ℝ (fun y => (W y).ofLp.1 i) z
        (WithLp.toLp 2 (coordinate m i, (0 : ℝ)))) +
      fderiv ℝ (fun y => (W y).ofLp.2) z
        (WithLp.toLp 2 ((0 : Space m), (1 : ℝ)))) =
      ∫ x in (U : Set (Space m)), inner ℝ (W (graph ψ x)) (conormal (a x))

end P201Specs.SmoothFlux
