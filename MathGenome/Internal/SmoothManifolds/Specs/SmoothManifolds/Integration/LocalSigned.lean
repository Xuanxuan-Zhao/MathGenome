import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Equivalences
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.FormPullback
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-! Independent statement of M10.01, paper.tex 1783–1814.

The section fibers and coefficients are the actual exterior powers and ordered
coordinate evaluations from Chapter 7. Signs are the compatible signed charts
of Chapter 9, rather than a requirement that boundary charts be positive.
The coordinate integrand is extended by zero in the ambient Euclidean space.
In particular it need not be continuous across the true boundary hyperplane.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical Topology BigOperators

namespace SmoothManifolds.LocalIntegrationData
open ModelData AtlasData TangentData TangentBundleData ExteriorData FormPullbackData
  OrientationData Set MeasureTheory
universe u

/-- Continuity of a top section in its actual local coordinate trivializations. -/
def IsContinuousTopForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (ω : Field S n) : Prop :=
  ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
    Continuous (fun p : c.source => topCoefficient K c hc p.val p.property ω)

/-- A section with support compact in the manifold. Containment of this closed
support in a chart is imposed when taking its coordinate integral. -/
structure CompactTopForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) where
  field : Field S n
  continuous : IsContinuousTopForm field
  compact_support : IsCompact (sectionSupport field)

/-- Include a model function into the ambient space, with value zero off the model. -/
def extendModel {n : ℕ} {a : ModelKind} (f : ModelSpace n a → ℝ)
    (x : Euclidean n) : ℝ :=
  if hx : x ∈ modelSet n a then f ⟨x, hx⟩ else 0

/-- Unsigned coefficient, zero off the chart target within the model. -/
def modelCoefficient {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S n)
    (x : ModelSpace n a) : ℝ :=
  if hx : x ∈ c.target then
    topCoefficient K c hc (c.symm x) (c.map_target hx) ω else 0

/-- The sign is inside the integrand: it can vary between components. -/
def modelSignedCoefficient {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S n)
    (x : ModelSpace n a) : ℝ :=
  if hx : x ∈ c.target then
    signValue (s.sign c hc ⟨c.symm x, c.map_target hx⟩) *
      topCoefficient K c hc (c.symm x) (c.map_target hx) ω else 0

def coordinateCoefficient {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S n) :
    Euclidean n → ℝ := extendModel (modelCoefficient K c hc ω)

def signedCoordinateCoefficient {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (s : SignedCharts S)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S n) : Euclidean n → ℝ :=
  extendModel (modelSignedCoefficient s K c hc ω)

/-- The Euclidean Lebesgue integral of the signed coefficient, including n=0. -/
def coordinateIntegral {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S n) : ℝ :=
  ∫ x : Euclidean n, signedCoordinateCoefficient s K c hc ω x

/-- The canonical scalar represented by a zeroth exterior covector. -/
def zeroCoefficient {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (ω : Field S 0) (p : M) : ℝ :=
  exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p)) (ω p)

/-- The ray sign in Λ⁰=ℝ, retained independently at every point. -/
def zeroSign {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (o : Orientation S) (p : M) : ℝ :=
  if IsPositive (o.val p) ((exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1)
    then 1 else -1

/-- This finsum is a finite sum for every compactly supported zero-form. -/
def zeroIntegral {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (o : Orientation S) (ω : Field S 0) : ℝ :=
  ∑ᶠ p : M, zeroSign o p * zeroCoefficient ω p

end SmoothManifolds.LocalIntegrationData

namespace Specs.SmoothManifolds.Integration.LocalSigned
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.FormPullbackData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.LocalIntegrationData Set MeasureTheory Filter
universe u

/-- Every intrinsic orientation supplies the signed-chart convention used here. -/
def orientation_signsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (o : Orientation S),
    ∃! s : SignedCharts S, RepresentsSignedCharts o.val s

/-- The full signed transition coefficient, for any top section, including
boundary points and transitions whose signs vary between components. -/
def coefficient_transitionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : ↥(c.source ∩ d.source)) (ω : Field S n),
    topCoefficient K c hc p.val p.property.1 ω =
      topCoefficient K d hd p.val p.property.2 ω * transitionDeterminant K c d hc hd p

def coordinate_formulaType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S n)
    (ε : Bool), (∀ p, s.sign c hc p = ε) →
    coordinateIntegral s K c hc ω = signValue ε * ∫ x, coordinateCoefficient K c hc ω x

/-- No interior-support hypothesis: true boundary points may lie in the support. -/
def integrableType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : CompactTopForm S),
    sectionSupport ω.field ⊆ c.source →
      Integrable (signedCoordinateCoefficient s K c hc ω.field)

/-- Coordinate independence for the original oriented-manifold objects.
Different choices of genuine intrinsic tangent coordinates are allowed. -/
def chart_independenceType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (o : Orientation S) (s : SignedCharts S),
    RepresentsSignedCharts o.val s → ∀ (K L : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (ω : CompactTopForm S),
    sectionSupport ω.field ⊆ c.source → sectionSupport ω.field ⊆ d.source →
      coordinateIntegral s K c hc ω.field = coordinateIntegral s L d hd ω.field

/-- At each artificial edge, the ambient zero extension vanishes on a whole
Euclidean neighborhood. This does not assert vanishing on the true boundary. -/
def artificial_edgesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (s : SignedCharts S) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : CompactTopForm S),
    sectionSupport ω.field ⊆ c.source → ∀ x : ModelSpace n a, x ∉ c.target →
      ∃ U : Set (Euclidean n), IsOpen U ∧ x.val ∈ U ∧
        ∀ y ∈ U, signedCoordinateCoefficient s K c hc ω.field y = 0

/-- The true boundary hyperplane is null; deleting it leaves the integral
unchanged for any coefficient, with no assumption that it vanishes there. -/
def boundary_nullType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M) (s : SignedCharts S)
    (K : FiberCoordinates S) (c : ModelChart (n+1) .halfSpace M)
    (hc : c ∈ S.smoothStructure.val) (ω : Field S (n+1)),
    volume (halfSpaceFace (n+1)) = 0 ∧
      coordinateIntegral s K c hc ω =
        ∫ x in {x : Euclidean (n+1) | 0 < x (Fin.last n)},
          signedCoordinateCoefficient s K c hc ω x

/-- Compact supports are finite in dimension zero. The canonical scalar
identification and the intrinsic point signs give the global finite sum. -/
def zero_finite_sumType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (o : Orientation S) (ω : CompactTopForm S),
    ∃ h : (sectionSupport ω.field).Finite,
      zeroIntegral o ω.field = ∑ p ∈ h.toFinset, zeroSign o p * zeroCoefficient ω.field p

/-- Coordinate integration in dimension zero is signed evaluation, and agrees
with the global finite signed sum when the support lies in that chart. -/
def zero_coordinateType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (o : Orientation S) (s : SignedCharts S),
    RepresentsSignedCharts o.val s → ∀ (K : FiberCoordinates S)
    (c : ModelChart 0 a M) (hc : c ∈ S.smoothStructure.val) (ω : CompactTopForm S),
    sectionSupport ω.field ⊆ c.source →
      coordinateIntegral s K c hc ω.field = zeroIntegral o ω.field ∧
      ∀ p : c.source, coordinateIntegral s K c hc ω.field =
        zeroSign o p.val * zeroCoefficient ω.field p.val

end Specs.SmoothManifolds.Integration.LocalSigned
