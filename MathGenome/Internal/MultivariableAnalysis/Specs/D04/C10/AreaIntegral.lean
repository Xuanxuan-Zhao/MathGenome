import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.PatchGeometryGram
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions

/-! Parametrized surface integrals (paper.tex, d04:10:area).
Data live on the image, but integration is over the parameter domain. In
particular no injectivity or quotient of traversals is built into this model.
All integrals below are the shared Darboux integral of a zero extension.
The admissibility predicates record bounded data and the actual Riemann
integrability requirement; the total value functions are used as integrals
only under these predicates. -/
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Specs.D04.C10.AreaIntegral
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C10.PatchGeometryGram.Model
open Specs.D04.C06.JordanRegions.Model
namespace Model

def imagePoint {n : ℕ} (D : Set (E 2)) (φ : E 2 → E n) (x : D) : φ '' D :=
  ⟨φ x, ⟨x, x.property, rfl⟩⟩

def areaIntegrand {n : ℕ} (D : Set (E 2)) (φ : E 2 → E n)
    (f : φ '' D → ℝ) (x : D) : ℝ :=
  f (imagePoint D φ x) * patchJacobian φ x

def AreaIntegrable {n : ℕ} (D : Set (E 2)) (φ : E 2 → E n)
    (f : φ '' D → ℝ) : Prop :=
  RegionBounded f ∧ RegionIntegrable (areaIntegrand D φ f)

def areaIntegral {n : ℕ} (D : Set (E 2)) (φ : E 2 → E n)
    (f : φ '' D → ℝ) : ℝ := regionIntegral (areaIntegrand D φ f)

def parametrizedArea {n : ℕ} (D : Set (E 2)) (φ : E 2 → E n) : ℝ :=
  areaIntegral D φ (fun _ => 1)

/-- Scalar area integration for a scalar field along the parametrization.
This also permits F·N when different visits to an image point have different normals. -/
def parameterAreaIntegral {n : ℕ} (D : Set (E 2)) (φ : E 2 → E n)
    (g : D → ℝ) : ℝ := regionIntegral (fun x => g x * patchJacobian φ x)

def areaVector (φ : E 2 → E 3) (x : E 2) : E 3 :=
  cross (columns (fderiv ℝ φ x).toLinearMap 0)
    (columns (fderiv ℝ φ x).toLinearMap 1)

def fluxIntegrand (D : Set (E 2)) (φ : E 2 → E 3)
    (F : φ '' D → E 3) (x : D) : ℝ :=
  ⟪F (imagePoint D φ x), areaVector φ x⟫

def FluxIntegrable (D : Set (E 2)) (φ : E 2 → E 3)
    (F : φ '' D → E 3) : Prop :=
  RegionBounded F ∧ RegionIntegrable (fluxIntegrand D φ F)

def fluxIntegral (D : Set (E 2)) (φ : E 2 → E 3)
    (F : φ '' D → E 3) : ℝ := regionIntegral (fluxIntegrand D φ F)

/-- The normal may vary along visits to the same image point. -/
def normalFluxIntegral (D : Set (E 2)) (φ : E 2 → E 3)
    (F : φ '' D → E 3) (N : E 2 → E 3) : ℝ :=
  parameterAreaIntegral D φ (fun x => ⟪F (imagePoint D φ x), N x⟫)

def oppositeNormal (φ : E 2 → E 3) (x : E 2) : E 3 := -unitNormal φ x

end Model
open Model

abbrev imagePointType := {n : ℕ} → (D : Set (E 2)) → (φ : E 2 → E n) → D → φ '' D
def imagePointValue : imagePointType := @Model.imagePoint

abbrev areaIntegrandType := {n : ℕ} → (D : Set (E 2)) → (φ : E 2 → E n) → (φ '' D → ℝ) → D → ℝ
def areaIntegrandValue : areaIntegrandType := @Model.areaIntegrand

abbrev AreaIntegrableType := {n : ℕ} → (D : Set (E 2)) → (φ : E 2 → E n) → (φ '' D → ℝ) → Prop
def AreaIntegrableValue : AreaIntegrableType := @Model.AreaIntegrable

abbrev areaIntegralType := {n : ℕ} → (D : Set (E 2)) → (φ : E 2 → E n) → (φ '' D → ℝ) → ℝ
def areaIntegralValue : areaIntegralType := @Model.areaIntegral

abbrev parametrizedAreaType := {n : ℕ} → Set (E 2) → (E 2 → E n) → ℝ
def parametrizedAreaValue : parametrizedAreaType := @Model.parametrizedArea

abbrev parameterAreaIntegralType := {n : ℕ} → (D : Set (E 2)) → (E 2 → E n) → (D → ℝ) → ℝ
def parameterAreaIntegralValue : parameterAreaIntegralType := @Model.parameterAreaIntegral

abbrev areaVectorType := (E 2 → E 3) → E 2 → E 3
def areaVectorValue : areaVectorType := @Model.areaVector

abbrev fluxIntegrandType := (D : Set (E 2)) → (φ : E 2 → E 3) → (φ '' D → E 3) → D → ℝ
def fluxIntegrandValue : fluxIntegrandType := @Model.fluxIntegrand

abbrev FluxIntegrableType := (D : Set (E 2)) → (φ : E 2 → E 3) → (φ '' D → E 3) → Prop
def FluxIntegrableValue : FluxIntegrableType := @Model.FluxIntegrable

abbrev fluxIntegralType := (D : Set (E 2)) → (φ : E 2 → E 3) → (φ '' D → E 3) → ℝ
def fluxIntegralValue : fluxIntegralType := @Model.fluxIntegral

abbrev normalFluxIntegralType := (D : Set (E 2)) → (φ : E 2 → E 3) → (φ '' D → E 3) → (E 2 → E 3) → ℝ
def normalFluxIntegralValue : normalFluxIntegralType := @Model.normalFluxIntegral

abbrev oppositeNormalType := (E 2 → E 3) → E 2 → E 3
def oppositeNormalValue : oppositeNormalType := @Model.oppositeNormal

def continuousOn_patchJacobianType : Prop :=
  ∀ {n : ℕ} {U : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ),
    ContinuousOn (patchJacobian φ) U

def continuous_areaIntegrandType : Prop :=
  ∀ {n : ℕ} {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hDU : D ⊆ U) (f : φ '' D → ℝ)
    (hf : Continuous f),
    Continuous (areaIntegrand D φ f)

def area_integrableType : Prop :=
  ∀ {n : ℕ} {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (f : φ '' D → ℝ) (hf : Continuous f),
    AreaIntegrable D φ f

def area_integral_formulaType : Prop :=
  ∀ {n : ℕ} (D : Set (E 2)) (φ : E 2 → E n) (f : φ '' D → ℝ),
    areaIntegral D φ f = regionIntegral (fun x : D =>
      f (imagePoint D φ x) * patchJacobian φ x)

def area_admissible_iffType : Prop :=
  ∀ {n : ℕ} (D : Set (E 2)) (φ : E 2 → E n) (f : φ '' D → ℝ),
    AreaIntegrable D φ f ↔ RegionBounded f ∧
      RegionIntegrable (fun x : D => f (imagePoint D φ x) * patchJacobian φ x)

def parametrized_area_formulaType : Prop :=
  ∀ {n : ℕ} (D : Set (E 2)) (φ : E 2 → E n),
    parametrizedArea D φ = areaIntegral D φ (fun _ => 1) ∧
    parametrizedArea D φ = regionIntegral (fun x : D => patchJacobian φ x)

def parametrized_area_integrableType : Prop :=
  ∀ {n : ℕ} {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U),
    AreaIntegrable D φ (fun _ => 1)

def continuousOn_areaVectorType : Prop :=
  ∀ {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ),
    ContinuousOn (areaVector φ) U

def continuous_fluxIntegrandType : Prop :=
  ∀ {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hDU : D ⊆ U) (F : φ '' D → E 3)
    (hF : Continuous F),
    Continuous (fluxIntegrand D φ F)

def flux_integrableType : Prop :=
  ∀ {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (F : φ '' D → E 3) (hF : Continuous F),
    FluxIntegrable D φ F

def flux_integral_formulaType : Prop :=
  ∀ (D : Set (E 2)) (φ : E 2 → E 3) (F : φ '' D → E 3),
    fluxIntegral D φ F = regionIntegral (fun x : D =>
      ⟪F (imagePoint D φ x), cross (columns (fderiv ℝ φ x).toLinearMap 0)
        (columns (fderiv ℝ φ x).toLinearMap 1)⟫)

def flux_admissible_iffType : Prop :=
  ∀ (D : Set (E 2)) (φ : E 2 → E 3) (F : φ '' D → E 3),
    FluxIntegrable D φ F ↔ RegionBounded F ∧
      RegionIntegrable (fluxIntegrand D φ F)

def flux_normal_integrandType : Prop :=
  ∀ {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hDU : D ⊆ U) (F : φ '' D → E 3),
    (fun x : D => ⟪F (imagePoint D φ x), unitNormal φ x⟫ * patchJacobian φ x) =
      fluxIntegrand D φ F

def flux_eq_normal_integralType : Prop :=
  ∀ {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hDU : D ⊆ U) (F : φ '' D → E 3),
    fluxIntegral D φ F = normalFluxIntegral D φ F (unitNormal φ)

def normal_flux_integrableType : Prop :=
  ∀ {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hDU : D ⊆ U) (F : φ '' D → E 3)
    (hF : FluxIntegrable D φ F),
    RegionIntegrable (fun x : D =>
      ⟪F (imagePoint D φ x), unitNormal φ x⟫ * patchJacobian φ x)

def opposite_normal_is_unitType : Prop :=
  ∀ {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) {x : E 2} (hx : x ∈ U),
    IsUnitNormal (tangentPlane φ x) (oppositeNormal φ x)

def opposite_fluxType : Prop :=
  ∀ {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hDU : D ⊆ U) (F : φ '' D → E 3)
    (hF : FluxIntegrable D φ F),
    RegionIntegrable (fun x : D =>
      ⟪F (imagePoint D φ x), oppositeNormal φ x⟫ * patchJacobian φ x) ∧
    normalFluxIntegral D φ F (oppositeNormal φ) = -fluxIntegral D φ F

def area_emptyType : Prop :=
  ∀ {n : ℕ} (φ : E 2 → E n) (f : φ '' (∅ : Set (E 2)) → ℝ),
    AreaIntegrable ∅ φ f ∧ areaIntegral ∅ φ f = 0

def parametrized_area_emptyType : Prop :=
  ∀ {n : ℕ} (φ : E 2 → E n),
    parametrizedArea ∅ φ = 0

def flux_emptyType : Prop :=
  ∀ (φ : E 2 → E 3) (F : φ '' (∅ : Set (E 2)) → E 3),
    FluxIntegrable ∅ φ F ∧ fluxIntegral ∅ φ F = 0

def normal_flux_emptyType : Prop :=
  ∀ (φ : E 2 → E 3) (F : φ '' (∅ : Set (E 2)) → E 3)
    (N : E 2 → E 3),
    normalFluxIntegral ∅ φ F N = 0

def area_zero_volumeType : Prop :=
  ∀ {n : ℕ} {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (hv : volume D = 0) (f : φ '' D → ℝ) (hf : RegionBounded f),
    AreaIntegrable D φ f ∧ areaIntegral D φ f = 0

def flux_zero_volumeType : Prop :=
  ∀ {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (hv : volume D = 0) (F : φ '' D → E 3) (hF : RegionBounded F),
    FluxIntegrable D φ F ∧ fluxIntegral D φ F = 0

def parametrized_area_zero_volumeType : Prop :=
  ∀ {n : ℕ} {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (hv : volume D = 0),
    parametrizedArea D φ = 0

def area_zero_contentType : Prop :=
  ∀ {n : ℕ} {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (hZ : Specs.D04.C06.NullCovers.Model.ContentZero D) (f : φ '' D → ℝ) (hf : RegionBounded f),
    AreaIntegrable D φ f ∧ areaIntegral D φ f = 0

def flux_zero_contentType : Prop :=
  ∀ {U D : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (hZ : Specs.D04.C06.NullCovers.Model.ContentZero D) (F : φ '' D → E 3) (hF : RegionBounded F),
    FluxIntegrable D φ F ∧ fluxIntegral D φ F = 0

def parametrized_area_zero_contentType : Prop :=
  ∀ {n : ℕ} {U D : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (hD : IsCompact D) (hJ : Jordan D) (hDU : D ⊆ U)
    (hZ : Specs.D04.C06.NullCovers.Model.ContentZero D),
    parametrizedArea D φ = 0

end Specs.D04.C10.AreaIntegral
