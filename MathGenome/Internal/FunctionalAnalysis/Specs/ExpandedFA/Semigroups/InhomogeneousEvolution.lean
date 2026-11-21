import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.ClassicalEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent specification for the inhomogeneous part of
`fa2:p3:evolution`, paper.tex 14815–14845. The horizon may be zero.
All finite-interval derivatives are within the closed interval, including
one-sided derivatives at both endpoints. The generator domain and its sum
graph norm are the shared exact-domain objects, not an ambient-norm substitute.
Forcing terms in L¹ are represented by arbitrary integrable representatives;
endpoint values have no influence on the mild solution. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace ExpandedFA.Semigroups.InhomogeneousEvolutionSpec
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X

abbrev A (S : C0Semigroup 𝕜 X) := C0SemigroupSpec.generatorValue S

/-- The variation-of-constants formula. Only its restriction to [0,τ] is used. -/
def solution (S : C0Semigroup 𝕜 X) (x : X) (f : ℝ → X) (t : ℝ) : X :=
  S.operators t.toNNReal x +
    ∫ s in (0 : ℝ)..t, S.operators (t - s).toNNReal (f s)

/-- Exactly sup_{0 ≤ s ≤ τ} ‖S(s)‖, not a chosen larger exponential bound. -/
def intervalBound (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) : ℝ :=
  sSup ((fun s : ℝ≥0 => ‖S.operators s‖) '' Icc 0 τ)

/-- The supremum norm on the finite interval (used only for bounded curves). -/
def supNorm (τ : ℝ≥0) (u : ℝ → X) : ℝ :=
  sSup ((fun t : ℝ => ‖u t‖) '' Icc 0 (τ : ℝ))

/-- The exact classical class: C¹ in X, values in D(A), the equation at every
point including endpoints, and continuity in the actual sum graph norm. -/
def IsClassicalSolution (S : C0Semigroup 𝕜 X) (τ : ℝ≥0)
    (x : X) (f u : ℝ → X) : Prop :=
  u 0 = x ∧ ∃ hu : ∀ t : Icc (0 : ℝ) (τ : ℝ), u t ∈ (A S).domain,
    ContDiffOn ℝ 1 u (Icc 0 (τ : ℝ)) ∧
    (∀ t : Icc (0 : ℝ) (τ : ℝ),
      HasDerivWithinAt u (A S ⟨u t, hu t⟩ + f t) (Icc 0 (τ : ℝ)) t) ∧
    @Continuous (Icc (0 : ℝ) (τ : ℝ)) (Unbounded.GraphDomain (A S))
      inferInstance inferInstance (fun t => ⟨u t, hu t⟩)

def ClassicalExistence : Prop :=
  ∀ (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) (x : (A S).domain) (f : ℝ → X),
    ContDiffOn ℝ 1 f (Icc 0 (τ : ℝ)) →
    IsClassicalSolution S τ x f (solution S x f)

def ClassicalUniqueness : Prop :=
  ∀ (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) (x : X) (f u v : ℝ → X),
    IsClassicalSolution S τ x f u → IsClassicalSolution S τ x f v →
    EqOn u v (Icc 0 (τ : ℝ))

/-- Mild existence, the standard supremum bound, and the quantitative uniform
Lipschitz estimate for dependence on the initial value and L¹ forcing.
The last estimate in particular makes the formula independent of the choice
of a representative of the forcing, and implies continuous dependence in
supremum norm, without requiring separability of X. -/
def MildWellPosedness : Prop :=
  ∀ (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) (x : X) (f : ℝ → X),
    IntegrableOn f (Icc 0 (τ : ℝ)) →
    (∀ t ∈ Icc (0 : ℝ) (τ : ℝ),
      IntervalIntegrable (fun s => S.operators (t - s).toNNReal (f s)) volume 0 t) ∧
    ContinuousOn (solution S x f) (Icc 0 (τ : ℝ)) ∧
    solution S x f 0 = x ∧
    supNorm τ (solution S x f) ≤
      intervalBound S τ * (‖x‖ + ∫ s in (0 : ℝ)..(τ : ℝ), ‖f s‖) ∧
    (∀ (y : X) (g : ℝ → X), IntegrableOn g (Icc 0 (τ : ℝ)) →
      supNorm τ (fun t => solution S x f t - solution S y g t) ≤
        intervalBound S τ *
          (‖x - y‖ + ∫ s in (0 : ℝ)..(τ : ℝ), ‖f s - g s‖))

set_option linter.checkUnivs false

def ClassicalExistenceExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  ClassicalExistence (𝕜 := 𝕜) (X := X)
def ClassicalUniquenessExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  ClassicalUniqueness (𝕜 := 𝕜) (X := X)
def MildWellPosednessExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  MildWellPosedness (𝕜 := 𝕜) (X := X)
end ExpandedFA.Semigroups.InhomogeneousEvolutionSpec
