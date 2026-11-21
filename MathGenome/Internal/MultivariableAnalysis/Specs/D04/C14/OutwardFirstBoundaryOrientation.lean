import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.OrientationsAndChartSigns
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! Independent statements for d04:14:boundary-orientation.
The outward direction is defined using a negative final parameter velocity,
not by assuming the existence of a normal or a boundary orientation. -/
noncomputable section
open Set
open scoped ContDiff
namespace Specs.D04.C14.OutwardFirstBoundaryOrientation
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
namespace Model

def IsOutwardVector (r : ℕ∞ω) (d : ℕ) {n : ℕ} (M : Set (E n))
    (x v : E n) : Prop :=
  ∃ (c : EmbeddedChart r (d+1) n M) (u w : E (d+1)),
    u ∈ c.source ∧ IsBoundaryParameter c u ∧ c.toFun u = x ∧
    chartDifferential c u w = v ∧ w (Fin.last d) < 0

def IsOutwardUnitConormal (r : ℕ∞ω) (d : ℕ) {n : ℕ} (M : Set (E n))
    (x v : E n) : Prop :=
  v ∈ tangentSpace r (d+1) M x ∧ ‖v‖ = 1 ∧
    (∀ w ∈ tangentSpace r d (intrinsicBoundary r (d+1) M) x,
      inner ℝ v w = 0) ∧ IsOutwardVector r d M x v

/-- The unnormalized inward dual to the last parameter coordinate. -/
def dualNormal {d n : ℕ} (A : E (d+1) →L[ℝ] E n) : E n :=
  A ((A.adjoint.comp A).inverse (standardBasis (d+1) (Fin.last d)))

def normalOfDifferential {d n : ℕ} (A : E (d+1) →L[ℝ] E n) : E n :=
  -(‖dualNormal A‖⁻¹) • dualNormal A

/-- Positivity of a boundary basis is tested by adjoining the outward vector
first. The full tuple is required to be an actual ordered tangent basis. -/
def PositiveWithOutward {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+1) M)
    (x : intrinsicBoundary r (d+1) M) (ν : E n)
    (b : Module.Basis (Fin d) ℝ
      (tangentSpace r d (intrinsicBoundary r (d+1) M) x)) : Prop :=
  ∃ B : Module.Basis (Fin (d+1)) ℝ (tangentSpace r (d+1) M x),
    (B 0).val = ν ∧ (∀ i : Fin d, (B i.succ).val = (b i).val) ∧
      B.orientation = o.atPoint x x.property.1

/-- A one-dimensional outward vector agrees with the chosen tangent-line
orientation precisely when it is the positive single-vector basis. -/
def PositiveOutwardLine {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r 1 M)
    (x : intrinsicBoundary r 1 M) (ν : E n) : Prop :=
  ∃ B : Module.Basis (Fin 1) ℝ (tangentSpace r 1 M x),
    (B 0).val = ν ∧ B.orientation = o.atPoint x x.property.1

/-- The concrete signed endpoint data, including the genuine boundary points
and the same continuous unit conormal used to define the point signs. -/
def IntervalBoundaryData (r : ℕ∞ω) (a b ε : ℝ)
    (o : PositiveManifoldOrientation r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}) : Prop :=
    ∃ (ha : (a • standardBasis 1 0) ∈ intrinsicBoundary r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})
      (hb : (b • standardBasis 1 0) ∈ intrinsicBoundary r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})
      (ν : intrinsicBoundary r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} → E 1)
      (s : ZeroManifoldOrientation (intrinsicBoundary r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})),
      Continuous ν ∧
      (∀ x : intrinsicBoundary r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}, IsOutwardUnitConormal r 0 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} x (ν x)) ∧
      (∀ x, (s x).val = 1 ↔ PositiveOutwardLine o x (ν x)) ∧
      (s ⟨a • standardBasis 1 0, ha⟩).val = -ε ∧
      (s ⟨b • standardBasis 1 0, hb⟩).val = ε

end Model
open Model

abbrev IsOutwardVectorType := ℕ∞ω → ℕ → {n : ℕ} → Set (E n) → E n → E n → Prop
def IsOutwardVectorValue : IsOutwardVectorType := @Model.IsOutwardVector
def IsOutwardUnitConormalValue : IsOutwardVectorType := @Model.IsOutwardUnitConormal
abbrev normalOfDifferentialType := {d n : ℕ} → (E (d+1) →L[ℝ] E n) → E n
def normalOfDifferentialValue : normalOfDifferentialType := @Model.normalOfDifferential

def outward_chart_independentType : Prop :=
  ∀ {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r (d+1) M →
    ∀ (c : EmbeddedChart r (d+1) n M) (u : E (d+1)),
      u ∈ c.source → IsBoundaryParameter c u → ∀ w : E (d+1),
        (IsOutwardVector r d M (c.toFun u) (chartDifferential c u w) ↔
          w (Fin.last d) < 0)

def conormal_exists_uniqueType : Prop :=
  ∀ {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r (d+1) M →
    ∀ x ∈ intrinsicBoundary r (d+1) M, ∃! v, IsOutwardUnitConormal r d M x v

def conormal_chart_formulaType : Prop :=
  ∀ {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r (d+1) M →
    ∀ (c : EmbeddedChart r (d+1) n M) (u : E (d+1)),
      u ∈ c.source → IsBoundaryParameter c u →
        IsOutwardUnitConormal r d M (c.toFun u)
          (normalOfDifferential (chartDifferential c u))

def continuous_conormalType : Prop :=
  ∀ {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r (d+1) M →
    ∃! ν : intrinsicBoundary r (d+1) M → E n,
      Continuous ν ∧ ∀ x : intrinsicBoundary r (d+1) M,
        IsOutwardUnitConormal r d M (x : E n) (ν x)

def boundary_orientationType : Prop :=
  ∀ {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+2) M)
    (ν : intrinsicBoundary r (d+2) M → E n),
    (∀ x : intrinsicBoundary r (d+2) M, IsOutwardUnitConormal r (d+1) M x (ν x)) →
    ∃! bO : PositiveManifoldOrientation r (d+1) (intrinsicBoundary r (d+2) M),
      ∀ (x : intrinsicBoundary r (d+2) M)
        (b : Module.Basis (Fin (d+1)) ℝ
          (tangentSpace r (d+1) (intrinsicBoundary r (d+2) M) x)),
        b.orientation = bO.atPoint x x.property ↔ PositiveWithOutward o x (ν x) b

def boundary_point_signType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r 1 M)
    (ν : intrinsicBoundary r 1 M → E n),
    (∀ x : intrinsicBoundary r 1 M, IsOutwardUnitConormal r 0 M x (ν x)) →
    ∃! s : ZeroManifoldOrientation (intrinsicBoundary r 1 M),
      ∀ x, ((s x).val = 1 ↔ PositiveOutwardLine o x (ν x)) ∧
        ((s x).val = -1 ↔ ¬ PositiveOutwardLine o x (ν x))

/-- Actual half-space conormal and tangent-space identifications, followed
by the determinant of the outward-first standard face basis. Thus the
coordinate determinant really compares tangent orientations. For d=0 it
is the signed-point convention. -/
def halfspace_orientationType : Prop :=
  ∀ (r : ℕ∞ω), ManifoldRegularity r → ∀ (d : ℕ) (x : E (d+1)),
    x ∈ flatBoundary (d+1) →
      IsOutwardUnitConormal r d (halfSpace (d+1)) x
        (-standardBasis (d+1) (Fin.last d)) ∧
      tangentSpace r (d+1) (halfSpace (d+1)) x = ⊤ ∧
      (tangentSpace r d (intrinsicBoundary r (d+1) (halfSpace (d+1))) x : Set (E (d+1))) = flatBoundary (d+1) ∧
      (standardBasis (d+1)).det
        (Fin.cons (-standardBasis (d+1) (Fin.last d))
          (fun i : Fin d => standardBasis (d+1) i.castSucc)) = (-1 : ℝ)^(d+1)

/-- A genuine interval with either directed orientation. The sign ε chooses
the positive tangent direction: when ε=1 the initial and terminal endpoints
are a,b; when ε=-1 they are b,a. -/
def interval_endpoint_signsType : Prop :=
  ∀ {r : ℕ∞ω} (a b : ℝ), a < b →
    ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (o : PositiveManifoldOrientation r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}),
    (∀ (x : E 1) (hx : a ≤ x 0 ∧ x 0 ≤ b)
      (B : Module.Basis (Fin 1) ℝ
        (tangentSpace r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} x)),
      B.orientation = o.atPoint x hx ↔ 0 < ε * (B 0).val 0) →
    IntervalBoundaryData r a b ε o

/-- Every continuous orientation of the interval chooses one of the two
constant coordinate directions; this is proved, rather than assumed. -/
def interval_orientation_classificationType : Prop :=
  ∀ {r : ℕ∞ω} (a b : ℝ), a < b →
    ∀ o : PositiveManifoldOrientation r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b},
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ (x : E 1) (hx : a ≤ x 0 ∧ x 0 ≤ b)
        (B : Module.Basis (Fin 1) ℝ
          (tangentSpace r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} x)),
        B.orientation = o.atPoint x hx ↔ 0 < ε * (B 0).val 0

/-- All oriented intervals: no coordinate-orientation hypothesis is added.
The derived ε identifies the initial and terminal endpoints. -/
def oriented_interval_endpoint_signsType : Prop :=
  ∀ {r : ℕ∞ω} (a b : ℝ), a < b →
    ∀ o : PositiveManifoldOrientation r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b},
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (∀ (x : E 1) (hx : a ≤ x 0 ∧ x 0 ≤ b)
        (B : Module.Basis (Fin 1) ℝ
          (tangentSpace r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} x)),
        B.orientation = o.atPoint x hx ↔ 0 < ε * (B 0).val 0) ∧
      IntervalBoundaryData r a b ε o

end Specs.D04.C14.OutwardFirstBoundaryOrientation
