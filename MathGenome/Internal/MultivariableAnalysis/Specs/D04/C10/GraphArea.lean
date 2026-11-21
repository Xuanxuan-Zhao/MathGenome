import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.AreaIntegral
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.CoordinateSeamsVolumes

/-! Graphs and the paraboloid example, paper.tex, d04:10:graph.
All surface integrals are the shared parametrized Gram/Darboux integrals.
The radial integral is the dimension-one Darboux integral, including a=0. -/
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Specs.D04.C10.GraphArea
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C10.PatchGeometryGram.Model
open Specs.D04.C10.AreaIntegral.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.DarbouxIntegral.Model (lowerIntegral intervalBox carrier Integrable)
open Specs.D04.C07.CoordinateSeamsVolumes.Model
open Specs.D04.C07.CoordinateCharts.Model
namespace Model

def graphMap (g : E 2 → ℝ) (x : E 2) : E 3 := WithLp.toLp 2 ![x 0, x 1, g x]
def graphPartial (g : E 2 → ℝ) (x : E 2) (i : Fin 2) : ℝ :=
  fderiv ℝ g x (standardBasis 2 i)
def paraboloidHeight (x : E 2) : ℝ := (x 0)^2 + (x 1)^2

def radialIntegral (a : ℝ) (ha : 0 ≤ a) : ℝ :=
  lowerIntegral (fun x : E 1 => x 0 * Real.sqrt (1 + 4 * (x 0)^2)) (intervalBox 0 a ha)

/-- The Cartesian image of the origin and the two angular faces; the two
angular faces describe the same ray, not two surface sheets. -/
def polarSeam (a : ℝ) (ha : 0 ≤ a) : Set (E 2) :=
  polar '' (carrier (polarBox a 0 ha) ∩
    {p | p 0 = 0 ∨ p 1 = 0 ∨ p 1 = 2 * Real.pi})
end Model
open Model

abbrev graphMapType := (E 2 → ℝ) → E 2 → E 3
def graphMapValue : graphMapType := graphMap
abbrev graphPartialType := (E 2 → ℝ) → E 2 → Fin 2 → ℝ
def graphPartialValue : graphPartialType := graphPartial
abbrev paraboloidHeightType := E 2 → ℝ
def paraboloidHeightValue : paraboloidHeightType := paraboloidHeight
abbrev radialIntegralType := (a : ℝ) → 0 ≤ a → ℝ
def radialIntegralValue : radialIntegralType := radialIntegral
abbrev polarSeamType := (a : ℝ) → 0 ≤ a → Set (E 2)
def polarSeamValue : polarSeamType := polarSeam

def graph_columnsType : Prop := ∀ (g : E 2 → ℝ) (x : E 2), DifferentiableAt ℝ g x →
  columns (fderiv ℝ (graphMap g) x).toLinearMap 0 = WithLp.toLp 2 ![1, 0, graphPartial g x 0] ∧
  columns (fderiv ℝ (graphMap g) x).toLinearMap 1 = WithLp.toLp 2 ![0, 1, graphPartial g x 1]

def graph_regularType : Prop := ∀ (U : Set (E 2)) (g : E 2 → ℝ),
  IsOpen U → ContDiffOn ℝ 1 g U → EmbeddedPatch U (graphMap g)

def graph_crossType : Prop := ∀ (g : E 2 → ℝ) (x : E 2), DifferentiableAt ℝ g x →
  areaVector (graphMap g) x = WithLp.toLp 2 ![-graphPartial g x 0, -graphPartial g x 1, 1]

def graph_densityType : Prop := ∀ (g : E 2 → ℝ) (x : E 2), DifferentiableAt ℝ g x →
  patchJacobian (graphMap g) x = Real.sqrt (1 + (graphPartial g x 0)^2 + (graphPartial g x 1)^2)

/-- Explicit upward unit normal and its positive vertical coordinate. -/
def graph_upwardType : Prop := ∀ (g : E 2 → ℝ) (x : E 2), DifferentiableAt ℝ g x →
  IsUnitNormal (tangentPlane (graphMap g) x) (unitNormal (graphMap g) x) ∧
  0 < (unitNormal (graphMap g) x) 2 ∧
  unitNormal (graphMap g) x =
    (Real.sqrt (1 + (graphPartial g x 0)^2 + (graphPartial g x 1)^2))⁻¹ •
      WithLp.toLp 2 ![-graphPartial g x 0, -graphPartial g x 1, 1]

def graph_areaType : Prop := ∀ (U D : Set (E 2)) (g : E 2 → ℝ),
  IsOpen U → ContDiffOn ℝ 1 g U → IsCompact D → Jordan D → D ⊆ U →
  AreaIntegrable D (graphMap g) (fun _ => 1) ∧
  parametrizedArea D (graphMap g) = regionIntegral (fun x : D =>
    Real.sqrt (1 + (graphPartial g x 0)^2 + (graphPartial g x 1)^2))

def graph_fluxType : Prop := ∀ (U D : Set (E 2)) (g : E 2 → ℝ),
  IsOpen U → ContDiffOn ℝ 1 g U → IsCompact D → Jordan D → D ⊆ U →
  ∀ F : graphMap g '' D → E 3, Continuous F →
  FluxIntegrable D (graphMap g) F ∧
  normalFluxIntegral D (graphMap g) F (unitNormal (graphMap g)) =
    regionIntegral (fun x : D =>
      -(F (imagePoint D (graphMap g) x) 0) * graphPartial g x 0 -
      (F (imagePoint D (graphMap g) x) 1) * graphPartial g x 1 +
      F (imagePoint D (graphMap g) x) 2)

def paraboloid_partialsType : Prop := ∀ x : E 2,
  graphPartial paraboloidHeight x 0 = 2 * x 0 ∧
  graphPartial paraboloidHeight x 1 = 2 * x 1

def paraboloid_polarType : Prop := ∀ a : ℝ, ∀ ha : 0 ≤ a,
  AreaIntegrable (disk a) (graphMap paraboloidHeight) (fun _ => 1) ∧
  parametrizedArea (disk a) (graphMap paraboloidHeight) = 2 * Real.pi * radialIntegral a ha

def radial_evaluationType : Prop := ∀ a : ℝ, ∀ ha : 0 ≤ a,
  Integrable (fun x : E 1 => x 0 * Real.sqrt (1 + 4 * (x 0)^2)) (intervalBox 0 a ha) ∧
  radialIntegral a ha = ((1 + 4 * a^2) ^ (3 / 2 : ℝ) - 1) / 12

def paraboloid_areaType : Prop := ∀ a : ℝ, 0 ≤ a →
  parametrizedArea (disk a) (graphMap paraboloidHeight) =
    Real.pi / 6 * ((1 + 4 * a^2) ^ (3 / 2 : ℝ) - 1)

def paraboloid_zeroType : Prop := parametrizedArea (disk 0) (graphMap paraboloidHeight) = 0

/-- Planar seams and their graph lifts have zero integral in the actual area
model. The polar equality above is obtained from the regular-chart truncation
formula, never from a regularity assertion at the radial origin. -/
def paraboloid_seamType : Prop := ∀ a : ℝ, ∀ ha : 0 ≤ a,
  Specs.D04.C06.NullCovers.Model.ContentZero (polarSeam a ha) ∧
  AreaIntegrable (polarSeam a ha) (graphMap paraboloidHeight) (fun _ => 1) ∧
  parametrizedArea (polarSeam a ha) (graphMap paraboloidHeight) = 0
end Specs.D04.C10.GraphArea
