import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.CirclesReflections
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Meromorphic.Basic

/-! Schwarz reflection, paper.tex:2494–2499. All boundary conditions are
relative to the open disk: no condition on its circular boundary is imposed. -/
noncomputable section
namespace D12Complex.Reflection
open Complex Metric Set

def upper (c : ℂ) (r : ℝ) : Set ℂ := ball c r ∩ {z | 0 < z.im}
def upperClosure (c : ℂ) (r : ℝ) : Set ℂ := ball c r ∩ {z | 0 ≤ z.im}
def diameter (c : ℂ) (r : ℝ) : Set ℂ := ball c r ∩ {z | z.im = 0}

/-- The values on the diameter are the given values of f. -/
def extension (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then f z else star (f (star z))

open Mobius

/-- Inverse of a chosen Möbius coordinate, on its finite coordinate plane. -/
def chartParam (M : Coefficients) (z : ℂ) : RiemannSphere :=
  mobiusMap (inverseCoefficients M) (sphereFinite z)

def chartProjection (M : Coefficients) (p : RiemannSphere) : ℂ :=
  finiteCoordinate (mobiusMap M p)

/-- The part of a sphere chart represented by s; its chart pole is excluded. -/
def chartRegion (M : Coefficients) (s : Set ℂ) : Set RiemannSphere :=
  {p | mobiusMap M p ≠ sphereInfty ∧ chartProjection M p ∈ s}

/-- The finite-plane part of a source Möbius chart. -/
def planeChartRegion (M : Coefficients) (s : Set ℂ) : Set ℂ :=
  sphereFinite ⁻¹' chartRegion M s

/-- View an ordinary scalar representative as a sphere map. The value at
source infinity is a filler and is never used in the finite-source theorem. -/
def finiteLift (f : ℂ → ℂ) (p : RiemannSphere) : RiemannSphere :=
  sphereFinite (f (finiteCoordinate p))

def straightened (M N : Coefficients) (f : RiemannSphere → RiemannSphere)
    (z : ℂ) : ℂ := chartProjection N (f (chartParam M z))

/-- Reflect in coordinates and undo the two Möbius charts. The sphere value
is retained when the inverse target coordinate has a pole. -/
def circleExtension (M N : Coefficients) (f : RiemannSphere → RiemannSphere)
    (p : RiemannSphere) : RiemannSphere :=
  mobiusMap (inverseCoefficients N)
    (sphereFinite (extension (straightened M N f) (chartProjection M p)))

end D12Complex.Reflection
namespace Specs.D12Complex.Ch12.Reflection
open _root_.D12Complex _root_.D12Complex.Reflection Complex Metric Set

def extension_type := (ℂ → ℂ) → ℂ → ℂ
def extension_value : extension_type := fun f z =>
  if 0 ≤ z.im then f z else star (f (star z))

def continuous_line_gluing_type : Prop :=
  ∀ (U : Set ℂ) (F : ℂ → ℂ), IsOpen U → ContinuousOn F U →
    (∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ F z) → HolomorphicOn U F

def schwarz_reflection_type : Prop :=
  ∀ (c : ℂ) (r : ℝ) (f : ℂ → ℂ), c.im = 0 → 0 < r →
    HolomorphicOn (upper c r) f → ContinuousOn f (upperClosure c r) →
    (∀ z ∈ diameter c r, (f z).im = 0) →
    HolomorphicOn (ball c r) (extension f) ∧
      EqOn (extension f) f (upperClosure c r) ∧
      (∀ z ∈ ball c r, z.im < 0 → extension f z = star (f (star z))) ∧
      (∀ z ∈ ball c r, extension f (star z) = star (extension f z))

end Specs.D12Complex.Ch12.Reflection

namespace Specs.D12Complex.Ch12.Reflection
open _root_.D12Complex _root_.D12Complex.Reflection
open _root_.D12Complex.Mobius _root_.D12Complex.CirclesReflections Complex Metric Set

/-- Coordinate form of the local circle theorem. Avoidance of the target
chart pole is imposed only on the given upper side and diameter. The reflected
extension is sphere valued and can have poles, which are covered below. -/
def circle_reflection_in_charts_type : Prop :=
  ∀ (M N : Coefficients) (D : Set RiemannSphere) (c : ℂ) (r : ℝ)
    (f : RiemannSphere → RiemannSphere),
    Regular M → Regular N → mobiusMap N '' D = extendedRealLine →
    c.im = 0 → 0 < r →
    SphereHolomorphicOn (chartRegion M (upper c r)) f →
    ContinuousOn f (chartRegion M (upperClosure c r)) →
    MapsTo f (chartRegion M (diameter c r)) D →
    (∀ z ∈ upperClosure c r, mobiusMap N (f (chartParam M z)) ≠ sphereInfty) →
    SphereHolomorphicOn (chartRegion M (ball c r)) (circleExtension M N f) ∧
      EqOn (circleExtension M N f) f (chartRegion M (upperClosure c r)) ∧
      (∀ p ∈ chartRegion M (ball c r), (chartProjection M p).im < 0 →
        circleExtension M N f p = reflectionVia N (f (reflectionVia M p)))

/-- Both the ordinary finite chart and the reciprocal chart of the resulting
extension are holomorphic at every point where they are defined. In particular
at an infinite value the reciprocal germ vanishes. -/
def circle_reflection_coordinates_type : Prop :=
  ∀ (M N : Coefficients) (c : ℂ) (r : ℝ) (f : RiemannSphere → RiemannSphere),
    SphereHolomorphicOn (chartRegion M (ball c r)) (circleExtension M N f) →
    ∀ p ∈ chartRegion M (ball c r), ∀ b : SphereCoordinate,
      p ∈ (sphereCoordinate b).source →
      (circleExtension M N f p ≠ sphereInfty →
        HolomorphicGermAt
          (fun z => finiteCoordinate (circleExtension M N f ((sphereCoordinate b).symm z)))
          (sphereCoordinate b p)) ∧
      (circleExtension M N f p = sphereInfty →
        HolomorphicGermAt
          (fun z => infinityCoordinate (circleExtension M N f ((sphereCoordinate b).symm z)))
          (sphereCoordinate b p) ∧ infinityCoordinate (circleExtension M N f p) = 0)

/-- Arbitrary generalized circles admit the charts used in the preceding
coordinate assertion. Choosing a source chart pole excludes precisely that
point, as required by the local statement in the paper. -/
def generalized_circle_charts_type : Prop :=
  ∀ C D : Set RiemannSphere, IsGeneralizedCircle C → IsGeneralizedCircle D →
    ∃ M N : Coefficients, Regular M ∧ Regular N ∧
      mobiusMap M '' C = extendedRealLine ∧ mobiusMap N '' D = extendedRealLine ∧
      (∀ p, mobiusMap M p ≠ sphereInfty →
        (p ∈ C ↔ (chartProjection M p).im = 0)) ∧
      (∀ p, mobiusMap N p ≠ sphereInfty →
        (p ∈ D ↔ (chartProjection N p).im = 0))

/-- The genuinely local assertion: continuity allows shrinking the disk so
that the target coordinate is finite. If the original target chart takes the
center value to infinity, its reciprocal chart is used instead. No avoidance
hypothesis on the original half-disk is needed here. -/
def local_circle_reflection_type : Prop :=
  ∀ (M N : Coefficients) (D : Set RiemannSphere) (c : ℂ) (R : ℝ)
    (f : RiemannSphere → RiemannSphere),
    Regular M → Regular N → IsGeneralizedCircle D →
    mobiusMap N '' D = extendedRealLine → c.im = 0 → 0 < R →
    SphereHolomorphicOn (chartRegion M (upper c R)) f →
    ContinuousOn f (chartRegion M (upperClosure c R)) →
    MapsTo f (chartRegion M (diameter c R)) D →
    ∃ (r : ℝ) (K : Coefficients), 0 < r ∧ r ≤ R ∧ Regular K ∧
      mobiusMap K '' D = extendedRealLine ∧
      mobiusMap K (f (chartParam M c)) ≠ sphereInfty ∧
      SphereHolomorphicOn (chartRegion M (ball c r)) (circleExtension M K f) ∧
      EqOn (circleExtension M K f) f (chartRegion M (upperClosure c r)) ∧
      (∀ p ∈ chartRegion M (ball c r), (chartProjection M p).im < 0 →
        circleExtension M K f p = reflectionVia N (f (reflectionVia M p)))

def circleExtension_type := Coefficients → Coefficients →
  (RiemannSphere → RiemannSphere) → RiemannSphere → RiemannSphere

def circleExtension_value : circleExtension_type := fun M N f p =>
  mobiusMap (inverseCoefficients N)
    (sphereFinite (extension (straightened M N f) (chartProjection M p)))

/-- Explicit bridge from ordinary weak holomorphy to the sphere formulation;
no analyticity or continuity of the derivative is an extra assumption. -/
def finite_lift_holomorphic_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f →
    SphereHolomorphicOn {p | p ≠ sphereInfty ∧ finiteCoordinate p ∈ U}
      (fun p => sphereFinite (f (finiteCoordinate p)))

def finite_lift_continuous_type : Prop :=
  ∀ (s : Set ℂ) (f : ℂ → ℂ), ContinuousOn f s →
    ContinuousOn (fun p => sphereFinite (f (finiteCoordinate p)))
      {p | p ≠ sphereInfty ∧ finiteCoordinate p ∈ s}

/-- The ordinary scalar representative of the reflected sphere map is
meromorphic in every source chart. Its filler at an infinite value is ignored
by MeromorphicAt. The preceding coordinate theorem records the true sphere
value and the holomorphic reciprocal with value zero. -/
def circle_reflection_meromorphic_type : Prop :=
  ∀ (M N : Coefficients) (c : ℂ) (r : ℝ) (f : RiemannSphere → RiemannSphere),
    SphereHolomorphicOn (chartRegion M (ball c r)) (circleExtension M N f) →
    ∀ p ∈ chartRegion M (ball c r), ∀ b : SphereCoordinate,
      p ∈ (sphereCoordinate b).source →
      MeromorphicAt
        (fun z => finiteCoordinate (circleExtension M N f ((sphereCoordinate b).symm z)))
        (sphereCoordinate b p)

/-- Specialization to the original finite-plane functions. The source disk
is chosen away from the inverse source chart pole. At every diameter point
the extension is ordinarily holomorphic; throughout the disk it is
meromorphic, with the true infinite values carried by circleExtension. -/
def plane_circle_reflection_type : Prop :=
  ∀ (C D : Set RiemannSphere) (M N : Coefficients) (c : ℂ) (R : ℝ) (f : ℂ → ℂ),
    IsGeneralizedCircle C → IsGeneralizedCircle D → Regular M → Regular N →
    mobiusMap M '' C = extendedRealLine → mobiusMap N '' D = extendedRealLine →
    c.im = 0 → 0 < R →
    (∀ p ∈ chartRegion M (ball c R), p ≠ sphereInfty) →
    HolomorphicOn (planeChartRegion M (upper c R)) f →
    ContinuousOn f (planeChartRegion M (upperClosure c R)) →
    MapsTo (fun z => sphereFinite (f z)) (planeChartRegion M (diameter c R)) D →
    ∃ (r : ℝ) (K : Coefficients), 0 < r ∧ r ≤ R ∧ Regular K ∧
      mobiusMap K '' D = extendedRealLine ∧
      SphereHolomorphicOn (chartRegion M (ball c r)) (circleExtension M K (finiteLift f)) ∧
      MeromorphicOn
        (fun z => finiteCoordinate (circleExtension M K (finiteLift f) (sphereFinite z)))
        (planeChartRegion M (ball c r)) ∧
      EqOn (fun z => finiteCoordinate (circleExtension M K (finiteLift f) (sphereFinite z))) f
        (planeChartRegion M (upperClosure c r)) ∧
      (∀ z ∈ planeChartRegion M (diameter c r),
        HolomorphicGermAt
          (fun w => finiteCoordinate (circleExtension M K (finiteLift f) (sphereFinite w))) z)

/-- The finite-source restriction in the plane specialization is always
available locally around a finite center of a Möbius chart. -/
def source_chart_locally_finite_type : Prop :=
  ∀ (M : Coefficients) (c : ℂ) (R : ℝ), Regular M → 0 < R →
    chartParam M c ≠ sphereInfty →
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∀ p ∈ chartRegion M (ball c r), p ≠ sphereInfty

end Specs.D12Complex.Ch12.Reflection
