import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.DirectionalSupport
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Real.Sqrt

/-! Independent statements for paper.tex 1163–1210, including the boundary
example. At an interior point the real representative `untopD 0` agrees
locally with the extended function, so its derivative is intrinsic. -/
noncomputable section
open Set Filter Topology
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

def subdifferential_eq_singleton_of_hasFDerivAt : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → WithTop ℝ), Proper f → IsConvex f → ∀ (x : E) (D : E →L[ℝ] ℝ),
    x ∈ interior (effectiveDomain f) →
    HasFDerivAt (fun z => (f z).untopD 0) D x → subdifferential f x = {D}

def hasFDerivAt_of_subdifferential_singleton : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → WithTop ℝ), Proper f → IsConvex f →
    ∀ (x : E) (D : E →L[ℝ] ℝ), x ∈ interior (effectiveDomain f) →
    subdifferential f x = {D} → HasFDerivAt (fun z => (f z).untopD 0) D x

/-- The global supporting inequalities imply monotonicity even without
convexity or properness. No norm or compatibility of the topology is needed;
in particular this covers all real Hausdorff locally convex spaces. -/
def subdifferential_monotone : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (f : E → WithTop ℝ), ∀ (x₁ x₂ : E)
    (y₁ y₂ : E →L[ℝ] ℝ), y₁ ∈ subdifferential f x₁ → y₂ ∈ subdifferential f x₂ →
    0 ≤ (y₁ - y₂) (x₁ - x₂)

/-- The derivative field is arbitrary but is certified to be the actual
Fréchet derivative at every point of the open convex domain. -/
def convexOn_iff_derivative_supports : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (g : E → ℝ) (D : E → E →L[ℝ] ℝ), IsOpen U → Convex ℝ U →
    (∀ x ∈ U, HasFDerivAt g (D x) x) →
    (ConvexOn ℝ U g ↔ ∀ x ∈ U, ∀ z ∈ U, g x + D x (z - x) ≤ g z)

def negativeSqrt (t : ℝ) : WithTop ℝ :=
  if 0 ≤ t then ((-Real.sqrt t : ℝ) : WithTop ℝ) else ⊤

def negativeSqrtType := ℝ → WithTop ℝ

def negativeSqrt_boundary : Prop :=
  Proper negativeSqrt ∧ IsConvex negativeSqrt ∧ IsLowerSemicontinuous negativeSqrt ∧
    directionalDerivative negativeSqrt 0 1 = ⊥ ∧ subdifferential negativeSqrt 0 = ∅

end VariationalNotes.ConvexAnalysis.Specs
