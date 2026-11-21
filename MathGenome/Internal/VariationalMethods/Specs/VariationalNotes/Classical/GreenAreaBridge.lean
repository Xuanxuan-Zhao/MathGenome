import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.Dulac
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.PathsLength
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! Independent statements for the C¹ Jordan/Green stage of paper.tex,
Theorem v07-08-02, lines 3592–3611.  The plane ℂ has its real Euclidean
structure and orientation (1,i); the input circle is ℝ/ℤ. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Specs.VariationalNotes.Classical.GreenAreaBridge
open Specs.D13Unified.Ch21.Collar
open Specs.D13Unified.Ch21.SmoothJordan
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model

/-- Standard real orthonormal coordinates on the complex plane. -/
abbrev planeCoordinates : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) := Specs.D13Unified.Ch13.Dulac.planeCoordinatesValue

/-- Counterclockwise quarter turn: (x,y) ↦ (-y,x). -/
def J0 (z : ℂ) : ℂ := Complex.I * z

/-- Lebesgue area, as a real number. Finiteness is proved separately. -/
def area (Ω : Set ℂ) : ℝ := (volume Ω).toReal

/-- Geometric length: the supremum of polygonal lengths on one turn. -/
def curveLength (c : Circle → ℂ) : ℝ≥0∞ :=
  Specs.D04.C09.PathsLength.Model.length (fun t => planeCoordinates (realLift c t)) 0 1

/-- A C¹ curve on a closed interval, with its continuous one-sided velocity
at the endpoints. No regularity outside the interval is imposed. -/
def C1Curve (γ v : ℝ → ℂ) (T : ℝ) : Prop :=
  ContinuousOn γ (Icc 0 T) ∧ ContinuousOn v (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (v t) (Icc 0 T) t

/-- Positive orientation means that the geometric left normal points into Ω
and the right normal points into the exterior, locally at every curve point. -/
def PositivelyOriented (Ω : Set ℂ) (γ v : ℝ → ℂ) (T : ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Ioo 0 ε,
    γ t + s • J0 (v t) ∈ Ω ∧ γ t - s • J0 (v t) ∉ closure Ω

/-- A single regular traversal with unit speed. Endpoint velocities agree,
so the parametrization admits a periodic C¹ extension. -/
def ArcLengthParametrization (c : Circle → ℂ) (T : ℝ) (γ v : ℝ → ℂ) : Prop :=
  0 < T ∧ curveLength c = ENNReal.ofReal T ∧ C1Curve γ v T ∧
    γ 0 = γ T ∧ v 0 = v T ∧ InjOn γ (Ico 0 T) ∧
    γ '' Icc 0 T = range c ∧ ∀ t ∈ Icc 0 T, ‖v t‖ = 1

/-- A regular C¹ embedded loop has a single closed unit-speed traversal,
with matching endpoint velocities and its original geometric length. -/
def arc_length_parametrizationType : Prop :=
  ∀ (c : Circle → ℂ), RegularEmbeddedLoop c →
    ∃ (T : ℝ) (γ v : ℝ → ℂ), ArcLengthParametrization c T γ v

def boundaryIntegrand (γ v : ℝ → ℂ) (t : ℝ) : ℝ := inner ℝ (J0 (γ t)) (v t)

/-- The actual outward-first manifold boundary integral for the area field.
The certificate is a conclusion, never an assumption on the input curve. -/
def GreenBoundaryArea (Ω : Set ℂ) : Prop :=
  let W := planeCoordinates.symm ⁻¹' Ω
  ∃ (_hW : IsClassicalRegularDomain W)
    (_hb : intrinsicBoundary 1 2 (closure W) = frontier W)
    (o : PositiveManifoldOrientation 1 2 (closure W))
    (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure W))),
    IsAmbientOrientation o ∧ OutwardFirst 1 o bO ∧
    HasPositiveIntegral bO
      (Specs.D04.C15.GeneralizedStokes.Model.tangentRestriction 1 1
        (intrinsicBoundary 1 2 (closure W))
        (circulationForm (fun x => -(x 1) / 2) (fun x => x 0 / 2))) (area Ω)

def jordan_areaType : Prop :=
  ∀ (c : Circle → ℂ), RegularEmbeddedLoop c → ∃ Ω E : Set ℂ,
    TwoComponents (range c)ᶜ Ω E ∧ IsOpen Ω ∧ IsOpen E ∧
    IsPathConnected Ω ∧ IsPathConnected E ∧
    Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded E ∧
    frontier Ω = range c ∧ frontier E = range c ∧
    closure Ω = Ω ∪ range c ∧ HasC1Boundary Ω ∧
    0 < volume Ω ∧ volume Ω < ⊤ ∧ 0 < area Ω ∧
    IsClassicalRegularDomain (planeCoordinates.symm ⁻¹' Ω)

/-- Jordan geometry together with a positively oriented C¹ unit-speed
traversal, constructed from the original regular embedded loop. -/
def positive_arc_length_jordanType : Prop :=
  ∀ (c : Circle → ℂ), RegularEmbeddedLoop c → ∃ (Ω E : Set ℂ)
    (T : ℝ) (γ v : ℝ → ℂ),
    TwoComponents (range c)ᶜ Ω E ∧ IsOpen Ω ∧ IsOpen E ∧
    IsPathConnected Ω ∧ IsPathConnected E ∧
    Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded E ∧
    frontier Ω = range c ∧ frontier E = range c ∧
    closure Ω = Ω ∪ range c ∧ HasC1Boundary Ω ∧
    0 < volume Ω ∧ volume Ω < ⊤ ∧ 0 < area Ω ∧
    ArcLengthParametrization c T γ v ∧ PositivelyOriented Ω γ v T

def green_boundary_areaType : Prop :=
  ∀ Ω : Set ℂ, IsOpen Ω → Bornology.IsBounded Ω → HasC1Boundary Ω →
    GreenBoundaryArea Ω

def translation_invarianceType : Prop :=
  ∀ (T : ℝ) (γ v : ℝ → ℂ), 0 ≤ T → C1Curve γ v T → γ 0 = γ T →
    ∀ m : ℂ,
      (∫ t in (0 : ℝ)..T, boundaryIntegrand (fun t => γ t - m) v t) =
        ∫ t in (0 : ℝ)..T, boundaryIntegrand γ v t

/-- Full assigned obligation. Every geometric and analytic witness is obtained
from the regular C¹ embedding; no area or orientation certificate is assumed. -/
def green_area_bridgeType : Prop :=
  ∀ (c : Circle → ℂ), RegularEmbeddedLoop c → ∃ (Ω E : Set ℂ)
    (T : ℝ) (γ v : ℝ → ℂ),
    TwoComponents (range c)ᶜ Ω E ∧ IsOpen Ω ∧ IsOpen E ∧
    IsPathConnected Ω ∧ IsPathConnected E ∧
    Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded E ∧
    frontier Ω = range c ∧ frontier E = range c ∧
    closure Ω = Ω ∪ range c ∧ HasC1Boundary Ω ∧
    0 < volume Ω ∧ volume Ω < ⊤ ∧ 0 < area Ω ∧
    ArcLengthParametrization c T γ v ∧ PositivelyOriented Ω γ v T ∧
    GreenBoundaryArea Ω ∧
    area Ω = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, boundaryIntegrand γ v t ∧
    ∀ m : ℂ,
      (∫ t in (0 : ℝ)..T, boundaryIntegrand (fun t => γ t - m) v t) =
        ∫ t in (0 : ℝ)..T, boundaryIntegrand γ v t

end Specs.VariationalNotes.Classical.GreenAreaBridge
