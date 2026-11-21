import Mathlib.Tactic.FinCases
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.GaussDivergenceTheorem
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.ClassicalSurfaceStokes
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.DiskHemisphereAndBoxSigns
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.SphereAreaFlux

/-! Exact calibrations in paper.tex, d04:12:calibration. All integrals use the
existing Riemann or Gram-density definitions. The planar disk is represented
by its injective affine parametrization, with the displayed upward normal. -/
noncomputable section
open Set
open scoped RealInnerProductSpace BigOperators
namespace Specs.D04.C12.ClassicalIntegralCalibrations
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C10.AreaIntegral.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C10.SphereAreaFlux.Model
open Specs.D04.C12.DiskHemisphereAndBoxSigns.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
local notation "Eucl" => Specs.D04.C01.EuclideanInterfaces.Model.E
namespace Model

def rotationField (x : Eucl 3) : Eucl 3 := WithLp.toLp 2 ![-x 1 / 2, x 0 / 2, 0]
def plane (u : Eucl 2) : Eucl 3 := WithLp.toLp 2 ![u 0, u 1, 0]
def diskParameters (R : ℝ) : Set (Eucl 2) := {u | u 0 ^ 2 + u 1 ^ 2 ≤ R ^ 2}
def lengths (a b c : ℝ) : Eucl 3 := WithLp.toLp 2 ![a,b,c]
def rectangle (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Box 3 :=
  ⟨0, lengths a b c, by
    intro i
    fin_cases i
    · exact ha.le
    · exact hb.le
    · exact hc.le⟩
def faceFlux (a b c : ℝ) (i : Fin 3) (upper : Bool) : ℝ :=
  normalFluxIntegral (cube 2) (boxFace 0 (lengths a b c) i upper) (fun x => x.val)
    (fun _ => if upper then standardBasis 3 i else -standardBasis 3 i)
def circleWork (R t : ℝ) : ℝ := ⟪rotationField (circle R t), deriv (circle R) t⟫
def reversedCircle (R t : ℝ) : Eucl 3 := circle R (2 * Real.pi - t)
def reversedWork (R t : ℝ) : ℝ :=
  ⟪rotationField (reversedCircle R t), deriv (reversedCircle R) t⟫
end Model
open Model

def radial_divergenceType : Prop := ∀ x : Eucl 3, divergence (fun y : Eucl 3 => y) x = 3

def sphere_calibrationType : Prop := ∀ R : ℝ, 0 < R →
  surfaceIntegral (sphere R) (fun x => ⟪(x : Eucl 3), radialNormal R x⟫) = 4 * Real.pi * R ^ 3

def ball_calibrationType : Prop := ∀ R : ℝ, 0 < R →
  Jordan (Metric.ball (0 : Eucl 3) R) ∧
  volume (Metric.ball (0 : Eucl 3) R) = 4 * Real.pi * R ^ 3 / 3 ∧
  RegionIntegrable (fun x : Metric.ball (0 : Eucl 3) R => divergence (fun y : Eucl 3 => y) x) ∧
  regionIntegral (fun x : Metric.ball (0 : Eucl 3) R => divergence (fun y : Eucl 3 => y) x) =
    surfaceIntegral (sphere R) (fun x => ⟪(x : Eucl 3), radialNormal R x⟫)

def box_facesType : Prop := ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
  (∀ i : Fin 3, faceFlux a b c i false = 0 ∧ faceFlux a b c i true = a*b*c) ∧
  (∀ (i : Fin 3) (upper : Bool),
    RegionIntegrable (fun u : cube 2 =>
      ⟪boxFace 0 (lengths a b c) i upper u,
        (if upper then standardBasis 3 i else -standardBasis 3 i)⟫ *
      Specs.D04.C10.PatchGeometryGram.Model.patchJacobian
        (boxFace 0 (lengths a b c) i upper) u))

def box_totalType : Prop := ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c),
  Integrable (fun x : Eucl 3 => divergence (fun y : Eucl 3 => y) x) (rectangle a b c ha hb hc) ∧
  (∑ i : Fin 3, (faceFlux a b c i true + faceFlux a b c i false)) = 3*a*b*c ∧
  lowerIntegral (fun x : Eucl 3 => divergence (fun y : Eucl 3 => y) x) (rectangle a b c ha hb hc) =
    ∑ i : Fin 3, (faceFlux a b c i true + faceFlux a b c i false)

def rotation_curlType : Prop := ∀ x : Eucl 3, curl rotationField x = standardBasis 3 2

def disk_geometryType : Prop := ∀ R : ℝ, 0 < R →
  plane '' diskParameters R = disk R ∧ Function.Injective plane ∧
  Specs.D04.C10.PatchGeometryGram.Model.RegularPatch Set.univ plane ∧
  (∀ u : Eucl 2, areaVector plane u = standardBasis 3 2) ∧ Jordan (diskParameters R)

def disk_fluxType : Prop := ∀ R : ℝ, 0 < R →
  FluxIntegrable (diskParameters R) plane (fun x => curl rotationField x) ∧
  fluxIntegral (diskParameters R) plane (fun x => curl rotationField x) = Real.pi * R ^ 2 ∧
  normalFluxIntegral (diskParameters R) plane (fun x => curl rotationField x)
    (fun _ => standardBasis 3 2) = Real.pi * R ^ 2 ∧
  normalFluxIntegral (diskParameters R) plane (fun x => curl rotationField x)
    (fun _ => -standardBasis 3 2) = -(Real.pi * R ^ 2)

def circle_workType : Prop := ∀ R : ℝ, 0 < R →
  (∀ t : ℝ, circleWork R t = R ^ 2 / 2) ∧
  ∃ h : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue (circleWork R) 0 (2*Real.pi),
    Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue (circleWork R) h = Real.pi * R ^ 2

def reversalType : Prop := ∀ R : ℝ, 0 < R →
  (∀ x ∈ equator R,
    Specs.D04.C13.OrientedEuclideanDictionary.Model.euclideanCross
      (-standardBasis 3 2) (radial R x) = -ccw R x) ∧
  (∀ t : ℝ, reversedWork R t = -(R ^ 2 / 2)) ∧
  ∃ h : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue (reversedWork R) 0 (2*Real.pi),
    Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue (reversedWork R) h = -(Real.pi * R ^ 2)

open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model
/-- The actual work integral on a single counterclockwise traversal, with its
geometric conormal and tangent, equals the upward disk flux. -/
def boundary_circulationType : Prop := ∀ R : ℝ, 0 < R →
  ∃ γ : IntervalPath 3 0 (2*Real.pi),
    (∀ t, γ t = circle R t) ∧ trace γ = equator R ∧
    Set.InjOn γ (Ico 0 (2*Real.pi)) ∧ γ 0 = γ (2*Real.pi) ∧
    (∀ x ∈ trace γ,
      Specs.D04.C14.OutwardFirstBoundaryOrientation.Model.IsOutwardUnitConormal
        1 1 (disk R) x (radial R x) ∧
      Specs.D04.C13.OrientedEuclideanDictionary.Model.euclideanCross
        (standardBasis 3 2) (radial R x) = ccw R x) ∧
    ∃ d : PiecewiseC1Data γ, ∃ h : WorkIntegrable d rotationField,
      workLineIntegral d rotationField h = Real.pi*R^2 ∧
      workLineIntegral d rotationField h =
        normalFluxIntegral (diskParameters R) plane (fun x => curl rotationField x)
          (fun _ => standardBasis 3 2)
end Specs.D04.C12.ClassicalIntegralCalibrations
