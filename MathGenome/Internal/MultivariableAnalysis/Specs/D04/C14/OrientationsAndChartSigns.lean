import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.ChartIndependentTangentSpaces
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Basic.Real.Sign
import Mathlib.Topology.LocallyConstant.Basic

/-! Orientations and signed charts (d04:14:orientation).
The ray presentation of a vector-space orientation is identified with classes
of ordered bases by `basis_orientation_iffType` and `orientation_basisType`.
In dimension zero we use independent signs, not empty ordered bases.
No transition-sign identity is assumed in the manifold-orientation structure. -/
noncomputable section
universe u
open Set
open scoped ContDiff
namespace Specs.D04.C14.OrientationsAndChartSigns
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
namespace Model

abbrev SpaceOrientation (k : ℕ) (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  Orientation ℝ V (Fin k)

/-- The columns of the differential, regarded in the canonical tangent space.
Membership follows from the defining supremum, without chart independence. -/
def tangentChartMap {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (u : E k) (hu : u ∈ c.source) :
    E k →ₗ[ℝ] tangentSpace r k M (c.toFun u) :=
  (chartDifferential c u).toLinearMap.codRestrict _ (fun w => by
    have h : LinearMap.range (chartDifferential c u).toLinearMap ≤
        tangentSpace r k M (c.toFun u) :=
      le_iSup_of_le c (le_iSup_of_le u (le_iSup_of_le hu
        (le_iSup_of_le rfl le_rfl)))
    exact h ⟨w, rfl⟩)

abbrev TangentOrientationField (r : ℕ∞ω) (k : ℕ) {n : ℕ} (M : Set (E n)) :=
  ∀ x, x ∈ M → SpaceOrientation k (tangentSpace r k M x)

/-- Evaluation of any positive representative of the chosen orientation on the
ordered chart columns. Changing that representative multiplies this by a
positive scalar and therefore preserves its sign. -/
def chartCoefficient {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : TangentOrientationField r k M) (c : EmbeddedChart r k n M)
    (u : E k) (hu : u ∈ c.source) : ℝ :=
  (o (c.toFun u) (c.map_source hu).1).someVector
    (fun i => tangentChartMap c u hu (standardBasis k i))

def chartSign {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : TangentOrientationField r k M) (c : EmbeddedChart r k n M)
    (u : E k) (hu : u ∈ c.source) : ℝ := Real.sign (chartCoefficient o c u hu)

/-- Continuity of the tangent orientation means locally constant agreement
with every chart's ordered differential basis, including signed boundary charts. -/
structure PositiveManifoldOrientation (r : ℕ∞ω) (k : ℕ) {n : ℕ} (M : Set (E n)) where
  positive_dimension : 0 < k
  manifold : IsEmbeddedManifold r k M
  atPoint : TangentOrientationField r k M
  locally_constant : ∀ c : EmbeddedChart r k n M,
    IsLocallyConstant (fun u : c.source => chartSign atPoint c u u.property)

/-- Each zero-dimensional point has its own independent integration sign. -/
abbrev PointSign := {s : ℝ // s = 1 ∨ s = -1}
abbrev ZeroManifoldOrientation {n : ℕ} (M : Set (E n)) := M → PointSign

def ManifoldOrientation (r : ℕ∞ω) : (k : ℕ) → {n : ℕ} → Set (E n) → Type
  | 0, _, M => ZeroManifoldOrientation M
  | d+1, _, M => PositiveManifoldOrientation r (d+1) M

/-- Reflection in a single coordinate, expressed in the standard basis. -/
def coordinateReflection (k : ℕ) (i : Fin k) : E k ≃L[ℝ] E k :=
  ((standardBasis k).equiv
    ((standardBasis k).unitsSMul (Function.update 1 i (-1))) (Equiv.refl _)).toContinuousLinearEquiv

end Model
open Model

abbrev SpaceOrientationType := (k : ℕ) → (V : Type u) → [AddCommGroup V] → [Module ℝ V] → Type u
def SpaceOrientationValue : SpaceOrientationType := @Model.SpaceOrientation
abbrev TangentOrientationFieldType := (r : ℕ∞ω) → (k : ℕ) → {n : ℕ} → Set (E n) → Type
def TangentOrientationFieldValue : TangentOrientationFieldType := @Model.TangentOrientationField
abbrev chartCoefficientType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} →
  TangentOrientationField r k M → (c : EmbeddedChart r k n M) → (u : E k) → u ∈ c.source → ℝ
def chartCoefficientValue : chartCoefficientType := @Model.chartCoefficient
def chartSignValue : chartCoefficientType := @Model.chartSign
abbrev PositiveManifoldOrientationType := (r : ℕ∞ω) → (k : ℕ) → {n : ℕ} → Set (E n) → Type
def PositiveManifoldOrientationValue : PositiveManifoldOrientationType := @Model.PositiveManifoldOrientation
abbrev ZeroManifoldOrientationType := {n : ℕ} → Set (E n) → Type
def ZeroManifoldOrientationValue : ZeroManifoldOrientationType := @Model.ZeroManifoldOrientation
abbrev ManifoldOrientationType := ℕ∞ω → (k : ℕ) → {n : ℕ} → Set (E n) → Type
def ManifoldOrientationValue : ManifoldOrientationType := @Model.ManifoldOrientation
abbrev coordinateReflectionType := (k : ℕ) → Fin k → E k ≃L[ℝ] E k
def coordinateReflectionValue : coordinateReflectionType := Model.coordinateReflection

def basis_orientation_iffType : Prop :=
  ∀ {k : ℕ} {V : Type u} [AddCommGroup V] [Module ℝ V]
    (b c : Module.Basis (Fin k) ℝ V), b.orientation = c.orientation ↔ 0 < b.det c

def orientation_basisType : Prop :=
  ∀ {k : ℕ} {V : Type u} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis (Fin k) ℝ V), 0 < k → ∀ o : SpaceOrientation k V,
      ∃ c : Module.Basis (Fin k) ℝ V, c.orientation = o

def orientation_two_classesType : Prop :=
  ∀ {k : ℕ} {V : Type u} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis (Fin k) ℝ V),
      b.orientation ≠ -b.orientation ∧ ∀ o : SpaceOrientation k V,
        o = b.orientation ∨ o = -b.orientation

def chart_basis_existsType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M),
    ManifoldRegularity r → k ≤ n → ∀ u ∈ c.source,
      ∃ b : Module.Basis (Fin k) ℝ (tangentSpace r k M (c.toFun u)),
        ∀ i, (b i).val = chartDifferential c u (standardBasis k i)

/-- Positivity is exactly agreement of the actual ordered chart basis with the
chosen tangent orientation; this also makes representative independence explicit. -/
def chartSign_basisType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : TangentOrientationField r k M) (c : EmbeddedChart r k n M)
    (u : E k) (hu : u ∈ c.source)
    (b : Module.Basis (Fin k) ℝ (tangentSpace r k M (c.toFun u))),
    (∀ i, (b i).val = chartDifferential c u (standardBasis k i)) →
    (chartSign o c u hu = 1 ↔ b.orientation = o (c.toFun u) (c.map_source hu).1)

def chartSign_valuesType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (o : TangentOrientationField r k M)
    (c : EmbeddedChart r k n M), ManifoldRegularity r → k ≤ n →
    ∀ u (hu : u ∈ c.source), chartSign o c u hu = 1 ∨ chartSign o c u hu = -1

/-- h = φ⁻¹ψ, with ψ = c and φ = d. The within derivative is the unique full
Euclidean derivative also at a flat boundary point. -/
def chartSign_transitionType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (o : TangentOrientationField r k M)
    (c d : EmbeddedChart r k n M), ManifoldRegularity r → k ≤ n →
    ∀ u (hu : u ∈ chartOverlap c d), ∀ hv : chartTransition c d u ∈ d.source,
      chartSign o c u hu.1 = chartSign o d (chartTransition c d u) hv *
        Real.sign (LinearMap.det (fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).toLinearMap)

/-- This covers any reparametrization ψ = φ ∘ h, including relative
half-space domains: no assumption on the desired sign identity is used. -/
def chartSign_reparametrizeType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (o : TangentOrientationField r k M)
    (c d : EmbeddedChart r k n M), ManifoldRegularity r →
    ∀ (h : E k → E k) (hm : MapsTo h c.source d.source),
      EqOn c.toFun (d.toFun ∘ h) c.source →
      ∀ u (hu : u ∈ c.source) (A : E k →L[ℝ] E k),
        HasFDerivWithinAt h A c.source u →
        chartSign o c u hu = chartSign o d (h u) (hm hu) * Real.sign (LinearMap.det A.toLinearMap)

def reflection_propertiesType : Prop :=
  ∀ (k : ℕ) (i : Fin k),
    LinearMap.det (coordinateReflection k i).toLinearMap = -1 ∧
    (∀ u, coordinateReflection k i (coordinateReflection k i u) = u) ∧
    (∀ u (j : Fin k), coordinateReflection k i u j = if j = i then -u j else u j)

/-- Local positivity uses only an interior chart point and a single reflection.
The resulting chart has open Euclidean source and has positive sign throughout. -/
def positive_interior_chartType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation r k M)
    (c : EmbeddedChart r k n M) (u : E k),
    u ∈ c.source → ¬ IsBoundaryParameter c u →
    ∃ (d : EmbeddedChart r k n M) (v : E k),
      d.half = false ∧ v ∈ d.source ∧ d.toFun v = c.toFun u ∧
      (∀ w (hw : w ∈ d.source), chartSign o.atPoint d w hw = 1)

/-- Reflection reverses the fixed one-dimensional model half-space and so cannot
be used to demand positive boundary charts. -/
def one_dimensional_halfspace_reflectionType : Prop :=
  coordinateReflection 1 0 '' halfSpace 1 = {u : E 1 | u 0 ≤ 0} ∧
    ¬ Set.MapsTo (coordinateReflection 1 0) (halfSpace 1) (halfSpace 1)

/-- Reversing every tangent-space orientation reverses each agreement sign. -/
def chartSign_reverseType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (o : TangentOrientationField r k M)
    (c : EmbeddedChart r k n M), ManifoldRegularity r → k ≤ n →
    ∀ u (hu : u ∈ c.source),
      chartSign (fun x hx => -o x hx) c u hu = -chartSign o c u hu

/-- The fixed half-space forces every one-dimensional boundary transition
(at the flat boundary) to have positive determinant. -/
def boundary_line_transition_positiveType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)} (c d : EmbeddedChart r 1 n M),
    ManifoldRegularity r → 1 ≤ n → ∀ u ∈ chartOverlap c d,
      IsBoundaryParameter c u →
        0 < LinearMap.det (fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).toLinearMap

/-- Either orientation, after reversal if necessary, makes a given boundary
chart negative. Every other chart at that point is then necessarily negative,
since boundary reparametrizations must preserve u₁ ≥ 0. -/
def negative_boundary_chartType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation r 1 M)
    (c : EmbeddedChart r 1 n M) (u : E 1) (hu : u ∈ c.source), IsBoundaryParameter c u →
    ∃ p : PositiveManifoldOrientation r 1 M,
      (p.atPoint = o.atPoint ∨ p.atPoint = fun x hx => -o.atPoint x hx) ∧
      chartSign p.atPoint c u hu = -1 ∧
      ∀ (d : EmbeddedChart r 1 n M) (v : E 1) (hv : v ∈ d.source),
        d.toFun v = c.toFun u → chartSign p.atPoint d v hv = -1

/-- No continuity relation between the independently chosen point signs. -/
def zero_orientation_arbitraryType : Prop :=
  ∀ {n : ℕ} (M : Set (E n)) (s : M → ℝ),
    (∀ x, s x = 1 ∨ s x = -1) →
      ∃ o : ZeroManifoldOrientation M, ∀ x, (o x).val = s x

end Specs.D04.C14.OrientationsAndChartSigns
