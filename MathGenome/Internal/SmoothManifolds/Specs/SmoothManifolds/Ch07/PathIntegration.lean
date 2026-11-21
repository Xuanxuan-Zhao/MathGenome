import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Covectors
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Independent interface for the integral/FTC clauses of M07.05,
paper.tex 1574--1582. All tangent vectors and covectors are the upstream
intrinsic ones. A piece has local ambient coordinate extensions at both ends;
it need not have an extension as a map into the manifold across an end.
No immersion, injectivity, or nonzero velocity is required.

Total functions are used to represent maps of closed intervals. Only their
restrictions to those intervals matter. The canonical integrand uses two-sided
velocities; its values at the finitely many corners do not affect its integral.
The sum formula below compares it with the actual one-sided velocities of each
piece, including the endpoint values. Degenerate intervals are permitted.
-/
set_option autoImplicit false

namespace SmoothManifolds.PathIntegrationData
open ModelData AtlasData MapData PartitionData TangentData CovectorData Set Filter
open scoped Topology
universe u

/-- A finite strictly increasing subdivision; `count = 0` represents [a,a]. -/
structure Subdivision (a b : ℝ) where
  count : ℕ
  point : ℕ → ℝ
  first : point 0 = a
  last : point count = b
  increasing : StrictMonoOn point (Icc 0 count)

/-- The appropriate one-sided curve domain at the ends of a nontrivial piece. -/
noncomputable def sideAt (a b t : ℝ) : CurveSide :=
  if t = a then .forward else if t = b then .backward else .twoSided

/-- Smoothness on a closed interval in the manuscript's local extension sense.
The existing `CurveSmoothAt` tests every chart by ambient Euclidean extensions. -/
def SmoothOnInterval {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (γ : ℝ → M) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn γ (Icc a b) ∧
    ∀ t ∈ Icc a b, a < b →
      CurveSmoothAt S (γ t) (sideAt a b t) (fun h => γ (t + h))

/-- The path is continuous at its corners, and has finitely many smooth pieces. -/
def PiecewiseSmoothOn {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (γ : ℝ → M) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn γ (Icc a b) ∧
    ∃ s : Subdivision a b,
      ∀ i < s.count, SmoothOnInterval S γ (s.point i) (s.point (i + 1))

/-- The unique intrinsic velocity when it exists, and zero otherwise.
Existence for smooth curves is an upstream theorem, not an assumed field. -/
noncomputable def velocity {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (γ : ℝ → M) (side : CurveSide) (t : ℝ) :
    TangentSpace S (γ t) := by
  classical
  exact if h : ∃ v, CurveRepresentsDerivation S (γ t) side (fun h => γ (t + h)) v
    then h.choose else 0

noncomputable def coefficient {n : ℕ} {k : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n k M) (α : CovectorField S)
    (γ : ℝ → M) (t : ℝ) : ℝ :=
  α (γ t) (velocity S γ .twoSided t)

/-- The oriented integral. Integrability for the stated class is proved below. -/
noncomputable def pathIntegral {n : ℕ} {k : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n k M) (α : CovectorField S)
    (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, coefficient S α γ t

/-- Integral using one-sided velocities at the ends of each smooth piece. -/
noncomputable def pieceIntegral {n : ℕ} {k : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n k M) (α : CovectorField S)
    (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, α (γ t) (velocity S γ (sideAt a b t) t)

noncomputable def subdivisionIntegral {n : ℕ} {k : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n k M) (α : CovectorField S)
    (γ : ℝ → M) {a b : ℝ} (s : Subdivision a b) : ℝ :=
  ∑ i ∈ Finset.range s.count, pieceIntegral S α γ (s.point i) (s.point (i + 1))

def reverse {M : Type u} (γ : ℝ → M) (a b : ℝ) : ℝ → M :=
  fun t => γ (a + b - t)

/-- Concatenation on adjacent parameter intervals, with a common endpoint. -/
noncomputable def concatenate {M : Type u} (γ η : ℝ → M) (b : ℝ) : ℝ → M :=
  fun t => if t ≤ b then γ t else η t

/-- Scalar local extensions, permitting arbitrary behavior off the interval. -/
def ScalarSmoothOnInterval (φ : ℝ → ℝ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ∀ t ∈ Icc a b, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧
    ∃ F : ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧ EqOn F φ (U ∩ Icc a b)

def ScalarPiecewiseSmoothOn (φ : ℝ → ℝ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn φ (Icc a b) ∧ ∃ s : Subdivision a b,
    ∀ i < s.count, ScalarSmoothOnInterval φ (s.point i) (s.point (i + 1))

/-- Nondecreasing and onto; the derivative is allowed to vanish on intervals. -/
def IsReparametrization (φ : ℝ → ℝ) (c d a b : ℝ) : Prop :=
  a ≤ b ∧ ScalarPiecewiseSmoothOn φ c d ∧ MonotoneOn φ (Icc c d) ∧
    φ '' Icc c d = Icc a b

end SmoothManifolds.PathIntegrationData

namespace Specs.SmoothManifolds.Ch07.PathIntegration
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.PartitionData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.PathIntegrationData Set Filter
open scoped Topology
universe u

def SubdivisionType :=
  ℝ → ℝ → Type
noncomputable def SubdivisionValue : SubdivisionType :=
  @PathIntegrationData.Subdivision

def sideAtType :=
  ℝ → ℝ → ℝ → CurveSide
noncomputable def sideAtValue : sideAtType :=
  @PathIntegrationData.sideAt

def SmoothOnIntervalType :=
  {n : ℕ} → {k : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    (S : SmoothManifold n k M) → (ℝ → M) → ℝ → ℝ → Prop
noncomputable def SmoothOnIntervalValue : SmoothOnIntervalType :=
  @PathIntegrationData.SmoothOnInterval

def PiecewiseSmoothOnType :=
  {n : ℕ} → {k : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    (S : SmoothManifold n k M) → (ℝ → M) → ℝ → ℝ → Prop
noncomputable def PiecewiseSmoothOnValue : PiecewiseSmoothOnType :=
  @PathIntegrationData.PiecewiseSmoothOn

def velocityType :=
  {n : ℕ} → {k : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    (S : SmoothManifold n k M) → (γ : ℝ → M) → CurveSide → (t : ℝ) → TangentSpace S (γ t)
noncomputable def velocityValue : velocityType :=
  @PathIntegrationData.velocity

def coefficientType :=
  {n : ℕ} → {k : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    (S : SmoothManifold n k M) → CovectorField S → (ℝ → M) → ℝ → ℝ
noncomputable def coefficientValue : coefficientType :=
  @PathIntegrationData.coefficient

def pathIntegralType :=
  {n : ℕ} → {k : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    (S : SmoothManifold n k M) → CovectorField S → (ℝ → M) → ℝ → ℝ → ℝ
noncomputable def pathIntegralValue : pathIntegralType :=
  @PathIntegrationData.pathIntegral

def pieceIntegralType :=
  {n : ℕ} → {k : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    (S : SmoothManifold n k M) → CovectorField S → (ℝ → M) → ℝ → ℝ → ℝ
noncomputable def pieceIntegralValue : pieceIntegralType :=
  @PathIntegrationData.pieceIntegral

def subdivisionIntegralType :=
  {n : ℕ} → {k : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    (S : SmoothManifold n k M) → CovectorField S → (ℝ → M) → {a b : ℝ} → Subdivision a b → ℝ
noncomputable def subdivisionIntegralValue : subdivisionIntegralType :=
  @PathIntegrationData.subdivisionIntegral

def reverseType :=
  {M : Type u} → (ℝ → M) → ℝ → ℝ → ℝ → M
noncomputable def reverseValue : reverseType :=
  @PathIntegrationData.reverse

def concatenateType :=
  {M : Type u} → (ℝ → M) → (ℝ → M) → ℝ → ℝ → M
noncomputable def concatenateValue : concatenateType :=
  @PathIntegrationData.concatenate

def ScalarSmoothOnIntervalType :=
  (ℝ → ℝ) → ℝ → ℝ → Prop
noncomputable def ScalarSmoothOnIntervalValue : ScalarSmoothOnIntervalType :=
  @PathIntegrationData.ScalarSmoothOnInterval

def ScalarPiecewiseSmoothOnType :=
  (ℝ → ℝ) → ℝ → ℝ → Prop
noncomputable def ScalarPiecewiseSmoothOnValue : ScalarPiecewiseSmoothOnType :=
  @PathIntegrationData.ScalarPiecewiseSmoothOn

def IsReparametrizationType :=
  (ℝ → ℝ) → ℝ → ℝ → ℝ → ℝ → Prop
noncomputable def IsReparametrizationValue : IsReparametrizationType :=
  @PathIntegrationData.IsReparametrization

section Statements

/-- Every smooth translated curve has the velocity used by the integral. -/
def velocity_specType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (S : SmoothManifold n k M) (γ : ℝ → M) (side : CurveSide) (t : ℝ),
    CurveSmoothAt S (γ t) side (fun h => γ (t + h)) →
      CurveRepresentsDerivation S (γ t) side (fun h => γ (t + h))
        (velocity S γ side t)

/-- The integral is an actual integrable finite-piece integral. -/
def coefficient_integrableType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) (a b : ℝ), PiecewiseSmoothOn S γ a b →
      IntervalIntegrable (coefficient S α.field γ) MeasureTheory.volume a b

/-- The defining formula in terms of the smooth pieces and their endpoint
velocities. No chosen subdivision is part of the one-form or of the path. -/
def integral_eq_sumType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) {a b : ℝ} (s : Subdivision a b),
    (∀ i < s.count, SmoothOnInterval S γ (s.point i) (s.point (i + 1))) →
      pathIntegral S α.field γ a b = subdivisionIntegral S α.field γ s

/-- In particular, inserting or deleting any smooth-piece subdivision is harmless. -/
def subdivision_independentType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) {a b : ℝ} (s r : Subdivision a b),
    (∀ i < s.count, SmoothOnInterval S γ (s.point i) (s.point (i + 1))) →
    (∀ i < r.count, SmoothOnInterval S γ (r.point i) (r.point (i + 1))) →
      subdivisionIntegral S α.field γ s = subdivisionIntegral S α.field γ r

/-- Arbitrary path concatenation, including constant and degenerate pieces. -/
def concatenationType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    (γ η : ℝ → M) (a b c : ℝ),
    PiecewiseSmoothOn S γ a b → PiecewiseSmoothOn S η b c → γ b = η b →
      PiecewiseSmoothOn S (concatenate γ η b) a c ∧
        pathIntegral S α.field (concatenate γ η b) a c =
          pathIntegral S α.field γ a b + pathIntegral S α.field η b c

/-- Reverse the traversal, keeping the parameter interval increasing. -/
def reversalType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) (a b : ℝ), PiecewiseSmoothOn S γ a b →
      PiecewiseSmoothOn S (reverse γ a b) a b ∧
        pathIntegral S α.field (reverse γ a b) a b = -pathIntegral S α.field γ a b

/-- Nondecreasing surjections may pause, and need not have smooth inverses.
The closure of the path class under this operation is part of the conclusion. -/
def reparametrizationType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) (φ : ℝ → ℝ) (a b c d : ℝ),
    PiecewiseSmoothOn S γ a b → IsReparametrization φ c d a b →
      PiecewiseSmoothOn S (γ ∘ φ) c d ∧
        pathIntegral S α.field (γ ∘ φ) c d = pathIntegral S α.field γ a b

/-- The fundamental theorem for a global smooth function; du is the upstream
intrinsic differential of its smooth germ. -/
def integral_dFunctionType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (S : SmoothManifold n k M) (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u) (γ : ℝ → M) (a b : ℝ),
    PiecewiseSmoothOn S γ a b →
      pathIntegral S (dFunction S u hu) γ a b = u (γ b) - u (γ a)

end Statements
end Specs.SmoothManifolds.Ch07.PathIntegration
