import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionTopology
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Equivalences
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Independent statements for paper.tex 4972–4987, with the region hypotheses
of 4762–4770 and the orientation convention of 4747–4758.

A coordinate one-form is a field of continuous linear functionals. Its
exterior derivative is evaluated on the ordered standard coordinate frame.
The boundary integral is the sum over all boundary curves of integrals over
one real period, with the finite joins assigned value zero. Thus no term
integrating through a reflex corner is dropped: only the corner *points*
are excluded. The integral is required to exist. Equivalence to a sum over
any finite decomposition into smooth arcs is an implementation obligation.

`surfaceChartStokes` uses an actual intrinsic exterior one-form and its
actual tangent coordinate maps. Its integrals are written in a positive
surface chart. Smoothness is required only on a neighborhood of the region,
not on the entire surface, and compact support is not assumed.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff
open scoped Classical

namespace P202Specs.ChartRegionStokes
open P202Specs.PlanarRegionTopology

abbrev OneForm := Plane → Plane →L[ℝ] ℝ

def coordinateFrame (i : Fin 2) : Plane := EuclideanSpace.single i 1

/-- If omega = P dx + Q dy, this is partial_x Q - partial_y P. -/
def exteriorCoefficient (omega : OneForm) (x : Plane) : ℝ :=
  fderiv ℝ omega x (coordinateFrame 0) (coordinateFrame 1) -
    fderiv ℝ omega x (coordinateFrame 1) (coordinateFrame 0)

/-- Only the finitely many joins are omitted, not neighborhoods of them. -/
def boundaryIntegrand (omega : OneForm) (c : RegularJordanCurve) (t : ℝ) : ℝ :=
  if (t : ParameterCircle) ∈ c.joins then 0
  else omega (realLift c.parametrization t) (deriv (realLift c.parametrization) t)

def componentIntegral (omega : OneForm) (c : RegularJordanCurve) : ℝ :=
  ∫ t in (0 : ℝ)..1, boundaryIntegrand omega c t

/-- Multiplication by -1 reverses the chosen boundary parametrization. -/
def boundaryIntegral (R : PlanarRegion) (omega : OneForm)
    (s : Fin R.boundaryCount → ℝ) : ℝ :=
  ∑ i, s i * componentIntegral omega (R.curve i)

def bulkIntegral (R : PlanarRegion) (omega : OneForm) : ℝ :=
  ∫ x in R.carrier, exteriorCoefficient omega x

/-- The actual retained closed region after deleting the open corner disks.
The circle boundaries themselves are kept. -/
def truncatedCarrier (R : PlanarRegion) {N : ℕ} (p : Fin N → Plane)
    (epsilon : ℝ) : Set Plane :=
  R.carrier \ ⋃ j, Metric.ball (p j) epsilon

/-- Parameters on the original arcs retained after disk removal. A choice
between strict and weak inequalities affects only finitely many transverse
crossing parameters once the geometric construction is made. -/
def retainedParameters (c : RegularJordanCurve) {N : ℕ} (p : Fin N → Plane)
    (epsilon : ℝ) : Set ℝ :=
  {t | ∀ j, epsilon ≤ dist (realLift c.parametrization t) (p j)}

def retainedComponentIntegral (omega : OneForm) (c : RegularJordanCurve)
    {N : ℕ} (p : Fin N → Plane) (epsilon : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    (retainedParameters c p epsilon).indicator (boundaryIntegrand omega c) t

/-- The retained original boundary, with every original component and sign.
The added circle arcs are separate integrals in the truncation argument. -/
def retainedBoundaryIntegral (R : PlanarRegion) (omega : OneForm)
    (s : Fin R.boundaryCount → ℝ) {N : ℕ} (p : Fin N → Plane)
    (epsilon : ℝ) : ℝ :=
  ∑ i, s i * retainedComponentIntegral omega (R.curve i) p epsilon

open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
  SmoothManifolds.ExteriorData SmoothManifolds.OrientationData

universe u
variable {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 .euclidean M}

/-- The L2 plane and the library's ordinary coordinate plane have exactly
the same coordinates. No change of orientation or scale is made here. -/
def modelPoint (x : Plane) : ModelSpace 2 .euclidean :=
  ⟨EuclideanSpace.equiv (Fin 2) ℝ x, mem_univ _⟩

def chartTarget (c : ModelChart 2 .euclidean M) : Set Plane :=
  modelPoint ⁻¹' c.target

/-- Literal pullback of the intrinsic one-covector by the inverse chart's
tangent coordinate isomorphism. The arbitrary zero value outside the chart
target is never differentiated at a point outside that open target. -/
def chartOneForm (C : CotangentBundle S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (omega : Field S 1) : OneForm := fun x =>
  if hx : modelPoint x ∈ c.target then
    let p := c.symm (modelPoint x)
    let hp : p ∈ c.source := c.map_target hx
    let α := (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))) (omega p)
    LinearMap.toContinuousLinearMap
      (α.comp ((C.tangent.fiberCoordinates.equiv c hc p hp).symm.toLinearMap.comp
        (EuclideanSpace.equiv (Fin 2) ℝ).toLinearMap))
  else 0

def PositiveChart (C : CotangentBundle S) (o : Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val) : Prop :=
  ∀ p : c.source,
    IsPositive (o.val p.val) (coordinateVector C.tangent.fiberCoordinates c hc p)

namespace Expected

/-- The complete planar coordinate identity, including integrability, for
every original region, every smooth form near it, and every induced boundary
orientation. No collar, truncation, estimates, or Stokes certificate is input. -/
def stokes : Prop :=
  ∀ (R : PlanarRegion) (U : Set Plane) (omega : OneForm),
    IsOpen U → R.carrier ⊆ U → ContDiffOn ℝ ∞ omega U →
    ∀ s : Fin R.boundaryCount → ℝ, IsInducedBoundaryOrientation R s →
      IntegrableOn (exteriorCoefficient omega) R.carrier ∧
      (∀ i, IntervalIntegrable (boundaryIntegrand omega (R.curve i)) volume 0 1) ∧
      bulkIntegral R omega = boundaryIntegral R omega s

/-- The original oriented chart formulation on an arbitrary surface, with
the original intrinsic one-form. Smoothness of its pulled-back coefficients
on an open neighborhood is precisely local smoothness in this chart.
The bulk integrand is d omega in this same positive chart. -/
def surfaceChartStokes : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 .euclidean M) (C : CotangentBundle S)
    (o : Orientation S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val), PositiveChart C o c hc →
    ∀ (R : PlanarRegion) (U : Set Plane) (omega : Field S 1),
      IsOpen U → R.carrier ⊆ U → U ⊆ chartTarget c →
      ContDiffOn ℝ ∞ (chartOneForm C c hc omega) U →
      ∀ s : Fin R.boundaryCount → ℝ, IsInducedBoundaryOrientation R s →
        IntegrableOn (exteriorCoefficient (chartOneForm C c hc omega)) R.carrier ∧
        (∀ i, IntervalIntegrable
          (boundaryIntegrand (chartOneForm C c hc omega) (R.curve i)) volume 0 1) ∧
        bulkIntegral R (chartOneForm C c hc omega) =
          boundaryIntegral R (chartOneForm C c hc omega) s

end Expected
end P202Specs.ChartRegionStokes
