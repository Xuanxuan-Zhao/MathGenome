import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.OrientedEuclideanDictionary
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.ExactFormsIntegrateToZeroOnCycles
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.SphereAreaFlux

/-! The radial obstruction of d04:15:radial-obstruction and the nonexistence
conclusions of d04:11:vector-potential and d04:11:punctured-three.
Ambient functions represent restrictions to the open punctured domain. -/
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Specs.D04.C15.RadialFluxObstruction
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C10.SphereAreaFlux.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.GeneralizedStokes.Model
namespace Model

def puncturedSpace : Set (E 3) := {0}ᶜ

def radialField (x : E 3) : E 3 := (‖x‖ ^ 3)⁻¹ • x

def radialForm : FormField 3 2 := beta radialField

end Model
open Model
abbrev puncturedSpaceType := Set (E 3)
def puncturedSpaceValue : puncturedSpaceType := puncturedSpace
abbrev radialFieldType := E 3 → E 3
def radialFieldValue : radialFieldType := radialField
abbrev radialFormType := FormField 3 2
def radialFormValue : radialFormType := radialForm

def radialField_smoothType : Prop := SmoothOn puncturedSpace radialField
def radialForm_smoothType : Prop := IsCrForm none puncturedSpace radialForm

def divergence_formulaType : Prop := ∀ x ∈ puncturedSpace,
  divergence radialField x =
    3 * (‖x‖ ^ 3)⁻¹ - 3 * (‖x‖ ^ 5)⁻¹ * ∑ i : Fin 3, (x i)^2

def divergence_zeroType : Prop := ∀ x ∈ puncturedSpace, divergence radialField x = 0

def radialForm_closedType : Prop := ∀ x ∈ puncturedSpace,
  exteriorDerivative radialForm x = 0

def sphere_normal_pairingType : Prop := ∀ x ∈ sphere 1,
  radialField x = x ∧ ⟪radialField x, radialNormal 1 x⟫ = 1

/-- Unsigned density presentation of outward flux. -/
def sphere_fluxType : Prop :=
  surfaceIntegral (sphere 1) (fun x => ⟪radialField x, radialNormal 1 x⟫) = 4 * Real.pi

/-- The oriented form integral uses an orientation agreeing in every chart
with the outward radial unit normal. This is the actual global integral. -/
def sphere_form_integralType : Prop :=
  ∃ o : PositiveManifoldOrientation 1 2 (sphere 1),
    (∀ (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 2 3 (sphere 1))
      (u : c.source), chartSign o.atPoint c u u.property =
        ⟪radialNormal 1 (Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.chartPoint c u),
          surfaceChartNormal c u⟫) ∧
    HasPositiveIntegral o (tangentRestriction 1 2 (sphere 1) radialForm) (4 * Real.pi)

def no_C1_primitiveType : Prop := ¬ ∃ eta : FormField 3 1,
  IsCrForm (some 1) puncturedSpace eta ∧
    ∀ x ∈ puncturedSpace, exteriorDerivative eta x = radialForm x

def no_C2_primitiveType : Prop := ¬ ∃ eta : FormField 3 1,
  IsCrForm (some 2) puncturedSpace eta ∧
    ∀ x ∈ puncturedSpace, exteriorDerivative eta x = radialForm x

def no_vector_potentialType : Prop := ¬ ∃ A : E 3 → E 3,
  CrOn 1 puncturedSpace A ∧ ∀ x ∈ puncturedSpace, curl A x = radialField x

end Specs.D04.C15.RadialFluxObstruction
