import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.AreaIntegral
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.NegligibleSeams
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The ruled example, paper.tex, d04:10:ruled. Areas below use the shared
Riemann/Gram integral. The cone apex is never asserted to be a manifold point. -/
noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace
namespace Specs.D04.C10.RuledAreas
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C10.PatchGeometryGram.Model
open Specs.D04.C10.AreaIntegral.Model
namespace Model

def ruled (a b : ℝ → E 3) (x : E 2) : E 3 := a (x 0) + x 1 • b (x 0)
def cylinder (R : ℝ) (x : E 2) : E 3 :=
  WithLp.toLp 2 ![R * Real.cos (x 0), R * Real.sin (x 0), x 1]
def cone (R H : ℝ) (x : E 2) : E 3 :=
  WithLp.toLp 2 ![(1-x 1)*R*Real.cos (x 0), (1-x 1)*R*Real.sin (x 0), x 1*H]
def rectangle (l r a b : ℝ) : Set (E 2) :=
  {x | x 0 ∈ Icc l r ∧ x 1 ∈ Icc a b}
def cylinderTruncation (H δ : ℝ) := rectangle δ (2*Real.pi-δ) 0 H
def coneTruncation (δ : ℝ) := rectangle δ (2*Real.pi-δ) 0 (1-δ)
def cylinderSeam (R H : ℝ) : Set (E 3) :=
  (fun t : ℝ => WithLp.toLp 2 ![R, 0, t]) '' Icc 0 H
def coneSeam (R H : ℝ) : Set (E 3) :=
  (fun t : ℝ => WithLp.toLp 2 ![(1-t)*R, 0, t*H]) '' Icc 0 1
end Model
open Model
open Specs.D04.C06.JordanRegions.Model

def ruled_columnsType : Prop :=
  ∀ (a b : ℝ → E 3) (x : E 2) (da db : E 3)
    (ha : HasDerivAt a da (x 0)) (hb : HasDerivAt b db (x 0)),
    columns (fderiv ℝ (ruled a b) x).toLinearMap 0 = da + x 1 • db ∧
    columns (fderiv ℝ (ruled a b) x).toLinearMap 1 = b (x 0)

def ruled_densityType : Prop :=
  ∀ (a b : ℝ → E 3) (x : E 2) (da db : E 3)
    (ha : HasDerivAt a da (x 0)) (hb : HasDerivAt b db (x 0)),
    patchJacobian (ruled a b) x = ‖cross (da + x 1 • db) (b (x 0))‖

def ruled_rankType : Prop :=
  ∀ (a b : ℝ → E 3) (x : E 2) (da db : E 3)
    (ha : HasDerivAt a da (x 0)) (hb : HasDerivAt b db (x 0)),
    Function.Injective (fderiv ℝ (ruled a b) x) ↔
      cross (da + x 1 • db) (b (x 0)) ≠ 0

def ruled_contDiffType : Prop :=
  ∀ (a b : ℝ → E 3) (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b),
    ContDiff ℝ 1 (ruled a b)

def ruled_regularType : Prop :=
  ∀ (a b : ℝ → E 3) (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (U : Set (E 2)) (hU : IsOpen U)
    (hr : ∀ x ∈ U, cross (deriv a (x 0) + x 1 • deriv b (x 0)) (b (x 0)) ≠ 0),
    RegularPatch U (ruled a b)

def cylinder_contDiffType : Prop :=
  ∀ (R : ℝ),
    ContDiff ℝ 1 (cylinder R)

def cone_contDiffType : Prop :=
  ∀ (R H : ℝ),
    ContDiff ℝ 1 (cone R H)

def cylinder_columnsType : Prop :=
  ∀ (R : ℝ) (x : E 2),
    columns (fderiv ℝ (cylinder R) x).toLinearMap 0 =
      WithLp.toLp 2 ![-R * Real.sin (x 0), R * Real.cos (x 0), 0] ∧
    columns (fderiv ℝ (cylinder R) x).toLinearMap 1 =
      WithLp.toLp 2 ![0, 0, 1]

def cone_columnsType : Prop :=
  ∀ (R H : ℝ) (x : E 2),
    columns (fderiv ℝ (cone R H) x).toLinearMap 0 =
      WithLp.toLp 2 ![-(1-x 1)*R*Real.sin (x 0), (1-x 1)*R*Real.cos (x 0), 0] ∧
    columns (fderiv ℝ (cone R H) x).toLinearMap 1 =
      WithLp.toLp 2 ![-R*Real.cos (x 0), -R*Real.sin (x 0), H]

def cylinder_crossType : Prop :=
  ∀ (R : ℝ) (x : E 2),
    cross (columns (fderiv ℝ (cylinder R) x).toLinearMap 0)
      (columns (fderiv ℝ (cylinder R) x).toLinearMap 1) =
      WithLp.toLp 2 ![R*Real.cos (x 0), R*Real.sin (x 0), 0]

def cone_crossType : Prop :=
  ∀ (R H : ℝ) (x : E 2),
    cross (columns (fderiv ℝ (cone R H) x).toLinearMap 0)
      (columns (fderiv ℝ (cone R H) x).toLinearMap 1) =
      WithLp.toLp 2 ![(1-x 1)*R*H*Real.cos (x 0),
        (1-x 1)*R*H*Real.sin (x 0), (1-x 1)*R^2]

def cylinder_densityType : Prop :=
  ∀ (R : ℝ) (hR : 0 < R) (x : E 2),
    patchJacobian (cylinder R) x = R

def cone_densityType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R) (x : E 2) (ht : x 1 ≤ 1),
    patchJacobian (cone R H) x = R*(1-x 1)*Real.sqrt (R^2+H^2)

def cylinder_regularType : Prop :=
  ∀ (R : ℝ) (hR : 0 < R),
    RegularPatch univ (cylinder R)

def cone_regularType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R),
    RegularPatch {x | x 1 < 1} (cone R H)

def cone_apexType : Prop :=
  ∀ (R H s : ℝ),
    cone R H (WithLp.toLp 2 ![s, 1]) = WithLp.toLp 2 ![0, 0, H] ∧
    ¬ Function.Injective (fderiv ℝ (cone R H) (WithLp.toLp 2 ![s, 1]))

def rectangle_jordanType : Prop :=
  ∀ (l r a b : ℝ) (hlr : l ≤ r) (hab : a ≤ b),
    Jordan (rectangle l r a b)

def rectangle_compactType : Prop :=
  ∀ (l r a b : ℝ) (hlr : l ≤ r) (hab : a ≤ b),
    IsCompact (rectangle l r a b)

def rectangle_affine_integralType : Prop :=
  ∀ (l r a b c d : ℝ) (hlr : l ≤ r) (hab : a ≤ b),
    RegionIntegrable (fun x : rectangle l r a b => c+d*(x : E 2) 1) ∧
    regionIntegral (fun x : rectangle l r a b => c+d*(x : E 2) 1) =
      (r-l)*(c*(b-a)+d*(b^2-a^2)/2)

def cylinder_rectangle_areaType : Prop :=
  ∀ (R H l r : ℝ) (hR : 0 < R) (hH : 0 ≤ H) (hlr : l ≤ r),
    AreaIntegrable (rectangle l r 0 H) (cylinder R) (fun _ => 1) ∧
    parametrizedArea (rectangle l r 0 H) (cylinder R) = (r-l)*R*H

def cylinder_areaType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R) (hH : 0 ≤ H),
    AreaIntegrable (rectangle 0 (2*Real.pi) 0 H) (cylinder R) (fun _ => 1) ∧
    parametrizedArea (rectangle 0 (2*Real.pi) 0 H) (cylinder R) = 2*Real.pi*R*H

def cone_rectangle_areaType : Prop :=
  ∀ (R H l r a b : ℝ) (hR : 0 < R)
    (hlr : l ≤ r) (hab : a ≤ b) (hb : b ≤ 1),
    AreaIntegrable (rectangle l r a b) (cone R H) (fun _ => 1) ∧
    parametrizedArea (rectangle l r a b) (cone R H) =
      (r-l)*R*Real.sqrt (R^2+H^2)*((b-a)-(b^2-a^2)/2)

def cone_areaType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R),
    AreaIntegrable (rectangle 0 (2*Real.pi) 0 1) (cone R H) (fun _ => 1) ∧
    parametrizedArea (rectangle 0 (2*Real.pi) 0 1) (cone R H) =
      Real.pi*R*Real.sqrt (R^2+H^2)

def cone_apex_capType : Prop :=
  ∀ (R H ε : ℝ) (hR : 0 < R) (hε : 0 ≤ ε),
    AreaIntegrable (rectangle 0 (2*Real.pi) (1-ε) 1) (cone R H) (fun _ => 1) ∧
    parametrizedArea (rectangle 0 (2*Real.pi) (1-ε) 1) (cone R H) =
      Real.pi*R*Real.sqrt (R^2+H^2)*ε^2

def cone_apex_zero_areaType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R),
    AreaIntegrable (rectangle 0 (2*Real.pi) 1 1) (cone R H) (fun _ => 1) ∧
    parametrizedArea (rectangle 0 (2*Real.pi) 1 1) (cone R H) = 0

def cylinder_injectiveType : Prop :=
  ∀ (R : ℝ) (hR : 0 < R),
    InjOn (cylinder R) {x | x 0 ∈ Ioo 0 (2*Real.pi)}

def cone_injectiveType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R),
    InjOn (cone R H) {x | x 0 ∈ Ioo 0 (2*Real.pi) ∧ x 1 < 1}

def cylinder_truncationType : Prop :=
  ∀ (R H δ : ℝ) (hR : 0 < R) (hH : 0 ≤ H)
    (hδ : 0 < δ) (hπ : δ < Real.pi),
    IsCompact (cylinderTruncation H δ) ∧ Jordan (cylinderTruncation H δ) ∧
    InjOn (cylinder R) (cylinderTruncation H δ) ∧
    AreaIntegrable (cylinderTruncation H δ) (cylinder R) (fun _ => 1) ∧
    parametrizedArea (cylinderTruncation H δ) (cylinder R) =
      (2*Real.pi-2*δ)*R*H

def cone_truncationType : Prop :=
  ∀ (R H δ : ℝ) (hR : 0 < R)
    (hδ : 0 < δ) (hπ : δ < Real.pi) (h1 : δ < 1),
    IsCompact (coneTruncation δ) ∧ Jordan (coneTruncation δ) ∧
    (coneTruncation δ ⊆ {x | x 1 < 1}) ∧
    InjOn (cone R H) (coneTruncation δ) ∧
    AreaIntegrable (coneTruncation δ) (cone R H) (fun _ => 1) ∧
    parametrizedArea (coneTruncation δ) (cone R H) =
      (2*Real.pi-2*δ)*R*Real.sqrt (R^2+H^2)*((1-δ)-(1-δ)^2/2)

def cylinder_area_limitType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R) (hH : 0 ≤ H),
    Tendsto (fun δ => parametrizedArea (cylinderTruncation H δ) (cylinder R))
      (𝓝[>] (0 : ℝ)) (𝓝 (2*Real.pi*R*H))

def cone_area_limitType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R),
    Tendsto (fun δ => parametrizedArea (coneTruncation δ) (cone R H))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi*R*Real.sqrt (R^2+H^2)))

def cylinder_seam_areaType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R) (hH : 0 ≤ H),
    cylinder R '' rectangle 0 0 0 H = cylinderSeam R H ∧
    AreaIntegrable (rectangle 0 0 0 H) (cylinder R) (fun _ => 1) ∧
    parametrizedArea (rectangle 0 0 0 H) (cylinder R) = 0

def cone_seam_areaType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R),
    cone R H '' rectangle 0 0 0 1 = coneSeam R H ∧
    AreaIntegrable (rectangle 0 0 0 1) (cone R H) (fun _ => 1) ∧
    parametrizedArea (rectangle 0 0 0 1) (cone R H) = 0

def cylinder_seam_endpointsType : Prop :=
  ∀ (R t : ℝ),
    cylinder R (WithLp.toLp 2 ![0,t]) = cylinder R (WithLp.toLp 2 ![2*Real.pi,t])

def cone_seam_endpointsType : Prop :=
  ∀ (R H t : ℝ),
    cone R H (WithLp.toLp 2 ![0,t]) = cone R H (WithLp.toLp 2 ![2*Real.pi,t])

def cylinder_seam_compact_curveType : Prop :=
  ∀ (R H : ℝ) (hH : 0 ≤ H),
    IsCompact (cylinderSeam R H) ∧ Specs.D04.C10.NegligibleSeams.Model.FiniteSeam (cylinderSeam R H)

def cone_seam_compact_curveType : Prop :=
  ∀ (R H : ℝ),
    IsCompact (coneSeam R H) ∧ Specs.D04.C10.NegligibleSeams.Model.FiniteSeam (coneSeam R H)

def cylinder_truncations_cofinalType : Prop :=
  ∀ (H : ℝ) (K : Set (E 2)) (hK : IsCompact K)
    (hsub : K ⊆ {x | x 0 ∈ Ioo 0 (2*Real.pi) ∧ x 1 ∈ Icc 0 H}),
    ∀ᶠ δ : ℝ in 𝓝[>] 0, K ⊆ cylinderTruncation H δ

def cone_truncations_cofinalType : Prop :=
  ∀ (K : Set (E 2)) (hK : IsCompact K)
    (hsub : K ⊆ {x | x 0 ∈ Ioo 0 (2*Real.pi) ∧ x 1 ∈ Ico 0 1}),
    ∀ᶠ δ : ℝ in 𝓝[>] 0, K ⊆ coneTruncation δ

def cylinder_complement_coveredType : Prop :=
  ∀ (R H : ℝ),
    cylinder R '' rectangle 0 (2*Real.pi) 0 H \ cylinderSeam R H ⊆
      cylinder R '' {x | x 0 ∈ Ioo 0 (2*Real.pi) ∧ x 1 ∈ Icc 0 H}

def cone_complement_coveredType : Prop :=
  ∀ (R H : ℝ),
    cone R H '' rectangle 0 (2*Real.pi) 0 1 \ coneSeam R H ⊆
      cone R H '' {x | x 0 ∈ Ioo 0 (2*Real.pi) ∧ x 1 ∈ Ico 0 1}

def cylinder_strip_avoids_seamType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R) (x : E 2)
    (hx : x 0 ∈ Ioo 0 (2*Real.pi)),
    cylinder R x ∉ cylinderSeam R H

def cone_strip_avoids_seamType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R) (x : E 2)
    (hx : x 0 ∈ Ioo 0 (2*Real.pi) ∧ x 1 < 1),
    cone R H x ∉ coneSeam R H

def cylinder_truncation_avoids_seamType : Prop :=
  ∀ (R H δ : ℝ) (hR : 0 < R) (hδ : 0 < δ),
    cylinder R '' cylinderTruncation H δ ⊆
      cylinder R '' rectangle 0 (2*Real.pi) 0 H \ cylinderSeam R H

def cone_truncation_avoids_seamType : Prop :=
  ∀ (R H δ : ℝ) (hR : 0 < R) (hδ : 0 < δ),
    cone R H '' coneTruncation δ ⊆
      cone R H '' rectangle 0 (2*Real.pi) 0 1 \ coneSeam R H

def cone_apex_cap_limitType : Prop :=
  ∀ (R H : ℝ) (hR : 0 < R),
    Tendsto (fun ε => parametrizedArea (rectangle 0 (2*Real.pi) (1-ε) 1) (cone R H))
      (𝓝[>] (0 : ℝ)) (𝓝 0)

def cone_disk_limitType : Prop :=
  ∀ (R : ℝ) (hR : 0 < R),
    Tendsto (fun δ => parametrizedArea (coneTruncation δ) (cone R 0))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi*R^2))

end Specs.D04.C10.RuledAreas
