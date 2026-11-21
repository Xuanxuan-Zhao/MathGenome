import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.RefinedSlater
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Subgradients
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Independent statements for paper.tex §v04-07, theorem `thm:convex-kkt`
and its two stationarity equivalences. The common domain and extended
Lagrangian are the canonical objects of `ConvexProgramSpecs`. -/
noncomputable section
open Set
open scoped BigOperators
universe u v w z
namespace VariationalNotes.Ch04.KKTSpecs
open ConvexProgramSpecs

section Algebra
variable {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J]

def kkt_sufficient_at : Prop :=
  ∀ (q : ConvexProgram X I A J) (m : Multipliers I A J) (x : X),
    KKTConditions q m x → IsPrimalMinimizer q x

variable [TopologicalSpace X]

def lagrangian_minimizer_iff_subgradient_at : Prop :=
  ∀ (q : ConvexProgram X I A J) (m : Multipliers I A J) (x : X),
    x ∈ commonDomain q →
    (IsLagrangianMinimizer q m x ↔
      (0 : X →L[ℝ] ℝ) ∈ ConvexAnalysis.Specs.subdifferential (lagrangian q m) x)

def kkt_iff_subgradient_at : Prop :=
  ∀ (q : ConvexProgram X I A J) (m : Multipliers I A J) (x : X),
    KKTConditions q m x ↔
      x ∈ feasibleSet q ∧ admissible m ∧
      (0 : X →L[ℝ] ℝ) ∈ ConvexAnalysis.Specs.subdifferential (lagrangian q m) x ∧
      complementarity q m x
end Algebra

def kkt_necessary : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]
    [FiniteDimensional ℝ X]
    {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J]
    (q : ConvexProgram X I A J) (p : ℝ) (x : X),
    primalValue q = (p : EReal) →
    (∃ x₀, x₀ ∈ ConvexGeometry.Specs.relativeInterior (commonDomain q) ∧
      x₀ ∈ affinePolyhedron q ∧ ∀ i, q.g i x₀ < 0) →
    IsPrimalMinimizer q x → ∃ m, KKTConditions q m x

section Smooth
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J]

/-- Interior membership is enough: in particular this applies on an open
convex common domain. Differentiability is required only at the point. -/
def lagrangian_minimizer_iff_derivative_at : Prop :=
  ∀ (q : ConvexProgram X I A J) (m : Multipliers I A J) (x : X),
    admissible m → x ∈ interior (commonDomain q) →
    DifferentiableAt ℝ (fun y => (q.f y).untopD 0) x →
    (∀ i, DifferentiableAt ℝ (fun y => (q.g i y).untopD 0) x) →
    (∀ l, DifferentiableAt ℝ (q.a l) x) →
    (∀ j, DifferentiableAt ℝ (q.e j) x) →
    (IsLagrangianMinimizer q m x ↔
      fderiv ℝ (fun y => (q.f y).untopD 0) x +
      ∑ i, m.lam i • fderiv ℝ (fun y => (q.g i y).untopD 0) x +
      ∑ l, m.mu l • fderiv ℝ (q.a l) x +
      ∑ j, m.nu j • fderiv ℝ (q.e j) x = 0)
end Smooth

section Gradient
variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J]

def lagrangian_minimizer_iff_gradient_at : Prop :=
  ∀ (q : ConvexProgram X I A J) (m : Multipliers I A J) (x : X),
    admissible m → x ∈ interior (commonDomain q) →
    DifferentiableAt ℝ (fun y => (q.f y).untopD 0) x →
    (∀ i, DifferentiableAt ℝ (fun y => (q.g i y).untopD 0) x) →
    (∀ l, DifferentiableAt ℝ (q.a l) x) →
    (∀ j, DifferentiableAt ℝ (q.e j) x) →
    (IsLagrangianMinimizer q m x ↔
      gradient (fun y => (q.f y).untopD 0) x +
      ∑ i, m.lam i • gradient (fun y => (q.g i y).untopD 0) x +
      ∑ l, m.mu l • gradient (q.a l) x +
      ∑ j, m.nu j • gradient (q.e j) x = 0)

def kkt_iff_gradient_at : Prop :=
  ∀ (q : ConvexProgram X I A J) (m : Multipliers I A J) (x : X),
    x ∈ interior (commonDomain q) →
    DifferentiableAt ℝ (fun y => (q.f y).untopD 0) x →
    (∀ i, DifferentiableAt ℝ (fun y => (q.g i y).untopD 0) x) →
    (∀ l, DifferentiableAt ℝ (q.a l) x) →
    (∀ j, DifferentiableAt ℝ (q.e j) x) →
    (KKTConditions q m x ↔
      x ∈ feasibleSet q ∧ admissible m ∧
      gradient (fun y => (q.f y).untopD 0) x +
      ∑ i, m.lam i • gradient (fun y => (q.g i y).untopD 0) x +
      ∑ l, m.mu l • gradient (q.a l) x +
      ∑ j, m.nu j • gradient (q.e j) x = 0 ∧ complementarity q m x)
end Gradient

/-- Fully quantified independent theorem types. -/
def kkt_sufficient : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
    {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J],
    kkt_sufficient_at (X := X) (I := I) (A := A) (J := J)

def lagrangian_minimizer_iff_subgradient : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
    {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J] [TopologicalSpace X],
    lagrangian_minimizer_iff_subgradient_at (X := X) (I := I) (A := A) (J := J)

def kkt_iff_subgradient : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
    {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J] [TopologicalSpace X],
    kkt_iff_subgradient_at (X := X) (I := I) (A := A) (J := J)

def lagrangian_minimizer_iff_derivative : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J],
    lagrangian_minimizer_iff_derivative_at (X := X) (I := I) (A := A) (J := J)

def lagrangian_minimizer_iff_gradient : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X]
    {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J],
    lagrangian_minimizer_iff_gradient_at (X := X) (I := I) (A := A) (J := J)

def kkt_iff_gradient : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X]
    {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J],
    kkt_iff_gradient_at (X := X) (I := I) (A := A) (J := J)

end VariationalNotes.Ch04.KKTSpecs
