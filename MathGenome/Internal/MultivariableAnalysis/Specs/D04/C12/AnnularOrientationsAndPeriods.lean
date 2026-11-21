import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.GreenCirculationAndFlux
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.CircleMultiplicity

/-! The annulus in d04:12:annulus. Norms are the shared Euclidean norms;
all directed curve integrals are the shared proper Riemann integrals. -/
noncomputable section
open Set
open scoped ContDiff
namespace Specs.D04.C12.AnnularOrientationsAndPeriods
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model
open Specs.D04.C09.CircleMultiplicity.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C06.JordanRegions.Model
namespace Model

def annulus (a b : ℝ) : Set (E 2) := {x | a < ‖x‖ ∧ ‖x‖ < b}

def leftTurn (v : E 2) : E 2 := WithLp.toLp 2 ![-v 1, v 0]

/-- m=1 is the usual counterclockwise traversal; m=-1 is clockwise. -/
def radiusCircle (r : ℝ) (m : ℤ) (t : ℝ) : E 2 := r • circle m t

def radiusVelocity (r : ℝ) (m : ℤ) (t : ℝ) : E 2 := r • circleVelocity m t

def radiusPath (r : ℝ) (m : ℤ) : IntervalPath 2 0 (2 * Real.pi) where
  ordered := (circlePath m).ordered
  toFun := radiusCircle r m
  continuousOn := by
    change ContinuousOn (fun t => r • circle m t) _
    exact (continuousOn_const (c := r)).smul (circlePath m).continuousOn
end Model
open Model

abbrev annulusType := ℝ → ℝ → Set (E 2)
def annulusValue : annulusType := Model.annulus
abbrev leftTurnType := E 2 → E 2
def leftTurnValue : leftTurnType := Model.leftTurn
abbrev radiusCircleType := ℝ → ℤ → ℝ → E 2
def radiusCircleValue : radiusCircleType := Model.radiusCircle
def radiusVelocityValue : radiusCircleType := Model.radiusVelocity
abbrev radiusPathType := ℝ → ℤ → IntervalPath 2 0 (2 * Real.pi)
def radiusPathValue : radiusPathType := Model.radiusPath

def annulus_coordinatesType : Prop := ∀ a b : ℝ,
  annulus a b = {x : E 2 | a < Real.sqrt ((x 0)^2 + (x 1)^2) ∧
    Real.sqrt ((x 0)^2 + (x 1)^2) < b}

def annulus_closureType : Prop := ∀ {a b : ℝ}, 0 < a → a < b →
  closure (annulus a b) = {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}

def annulus_frontierType : Prop := ∀ {a b : ℝ}, 0 < a → a < b →
  frontier (annulus a b) = {x | ‖x‖ = a ∨ ‖x‖ = b}

def annulus_regularType : Prop := ∀ {a b : ℝ}, 0 < a → a < b →
  IsClassicalRegularDomain (annulus a b)

def outward_normalsType : Prop := ∀ {a b : ℝ}, 0 < a → a < b →
  ∀ (hD : IsClassicalRegularDomain (annulus a b)) (p : frontier (annulus a b)),
    (‖(p : E 2)‖ = b → outwardNormal hD p = b⁻¹ • (p : E 2)) ∧
    (‖(p : E 2)‖ = a → outwardNormal hD p = -(a⁻¹ • (p : E 2)))

/-- The rotation is the unit tangent in the actual induced manifold orientation. -/
def induced_tangentType : Prop := ∀ {a b : ℝ}, 0 < a → a < b →
  ∀ (hD : IsClassicalRegularDomain (annulus a b))
    (hb : intrinsicBoundary 1 2 (closure (annulus a b)) = frontier (annulus a b))
    (o : PositiveManifoldOrientation 1 2 (closure (annulus a b))), IsAmbientOrientation o →
    ∀ (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure (annulus a b)))),
      OutwardFirst 1 o bO → ∀ (x : intrinsicBoundary 1 2 (closure (annulus a b)))
      (e : OrthonormalBasis (Fin 1) ℝ
        (tangentSpace 1 1 (intrinsicBoundary 1 2 (closure (annulus a b))) x)),
      e.toBasis.orientation = bO.atPoint x x.property →
      (e 0).val = leftTurn (outwardNormal hD ⟨x, hb ▸ x.property⟩)

/-- Tangents are rotated outward normals. A short step to their left is in D,
which specifies the side of the traversal without a drawing convention. -/
def region_leftType : Prop := ∀ {a b : ℝ}, 0 < a → a < b →
  ∀ (hD : IsClassicalRegularDomain (annulus a b)) (p : frontier (annulus a b)),
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      (p : E 2) + ε • leftTurn (leftTurn (outwardNormal hD p)) ∈ annulus a b

def radius_path_geometryType : Prop := ∀ {r : ℝ}, 0 < r → ∀ m : ℤ, m ≠ 0 →
  trace (radiusPath r m) = {x | ‖x‖ = r} ∧
  radiusCircle r m 0 = radiusCircle r m (2 * Real.pi) ∧
  PiecewiseRegular (radiusPath r m)

/-- The two distinct traces exhaust the boundary. -/
def boundary_traceType : Prop := ∀ {a b : ℝ}, 0 < a → a < b →
  frontier (annulus a b) = trace (radiusPath b 1) ∪ trace (radiusPath a (-1)) ∧
  Disjoint (trace (radiusPath b 1)) (trace (radiusPath a (-1)))

/-- The positive outer and inner traversal velocities are positive multiples
of the tangent obtained by rotating the actual classical outward normal. -/
def boundary_traversalsType : Prop := ∀ {a b : ℝ}, 0 < a → a < b →
  ∀ (hD : IsClassicalRegularDomain (annulus a b)) (t : ℝ),
    (∃ hp : radiusCircle b 1 t ∈ frontier (annulus a b),
      radiusVelocity b 1 t = b • leftTurn (outwardNormal hD ⟨_, hp⟩)) ∧
    (∃ hp : radiusCircle a (-1) t ∈ frontier (annulus a b),
      radiusVelocity a (-1) t = a • leftTurn (outwardNormal hD ⟨_, hp⟩))

def field_neighborhoodType : Prop := ∀ {a b : ℝ}, 0 < a → a < b →
  IsOpen puncturedPlane ∧ closure (annulus a b) ⊆ puncturedPlane ∧
  CrOn 1 puncturedPlane angularField ∧
  ∀ x ∈ puncturedPlane,
    circulationDensity (fun y => angularField y 0) (fun y => angularField y 1) x = 0

def radius_periodType : Prop := ∀ {r : ℝ}, 0 < r → ∀ (m : ℤ)
  (d : PiecewiseC1Data (radiusPath r m)),
    ∃ h : WorkIntegrable d angularField,
      workLineIntegral d angularField h = 2 * Real.pi * (m : ℝ)

def boundary_periodsType : Prop := ∀ {a b : ℝ}, 0 < a → a < b →
  ∀ (outer : PiecewiseC1Data (radiusPath b 1))
    (inner : PiecewiseC1Data (radiusPath a (-1))),
    ∃ ho : WorkIntegrable outer angularField, ∃ hi : WorkIntegrable inner angularField,
      workLineIntegral outer angularField ho = 2 * Real.pi ∧
      workLineIntegral inner angularField hi = -(2 * Real.pi) ∧
      workLineIntegral outer angularField ho + workLineIntegral inner angularField hi = 0

/-- Green's actual induced-boundary integral, with no extra domain assumption. -/
def green_zeroType : Prop := ∀ {a b : ℝ}, 0 < a → a < b →
  ∃ (o : PositiveManifoldOrientation 1 2 (closure (annulus a b)))
    (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure (annulus a b)))),
    IsAmbientOrientation o ∧ OutwardFirst 1 o bO ∧
    regionIntegral (fun x : annulus a b =>
      circulationDensity (fun y => angularField y 0) (fun y => angularField y 1) x) = 0 ∧
    HasPositiveIntegral bO
      (tangentRestriction 1 1 (intrinsicBoundary 1 2 (closure (annulus a b)))
        (circulationForm (fun y => angularField y 0) (fun y => angularField y 1))) 0

/-- For the very same field, the total induced-boundary integral is the sum
of the two displayed proper curve integrals, and equals the Green bulk value. -/
def green_boundary_sumType : Prop := ∀ {a b : ℝ}, 0 < a → a < b →
  ∀ (outer : PiecewiseC1Data (radiusPath b 1))
    (inner : PiecewiseC1Data (radiusPath a (-1))),
  ∃ (ho : WorkIntegrable outer angularField) (hi : WorkIntegrable inner angularField)
    (o : PositiveManifoldOrientation 1 2 (closure (annulus a b)))
    (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure (annulus a b)))),
    IsAmbientOrientation o ∧ OutwardFirst 1 o bO ∧
    workLineIntegral outer angularField ho = 2 * Real.pi ∧
    workLineIntegral inner angularField hi = -(2 * Real.pi) ∧
    regionIntegral (fun x : annulus a b =>
      circulationDensity (fun y => angularField y 0) (fun y => angularField y 1) x) =
        workLineIntegral outer angularField ho + workLineIntegral inner angularField hi ∧
    HasPositiveIntegral bO
      (tangentRestriction 1 1 (intrinsicBoundary 1 2 (closure (annulus a b)))
        (circulationForm (fun y => angularField y 0) (fun y => angularField y 1)))
      (workLineIntegral outer angularField ho + workLineIntegral inner angularField hi)

def disk_excludedType : Prop := ∀ (c : E 2) (r : ℝ),
  (0 : E 2) ∈ Metric.ball c r → ¬ closure (Metric.ball c r) ⊆ puncturedPlane

end Specs.D04.C12.AnnularOrientationsAndPeriods
