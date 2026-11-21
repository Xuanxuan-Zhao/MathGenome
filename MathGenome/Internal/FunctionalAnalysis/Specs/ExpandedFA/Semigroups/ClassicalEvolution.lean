import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.SemigroupGrowthAndGenerator
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Homogeneous part of `fa2:p3:evolution`, paper.tex 14810–14815.
Time derivatives are taken within the closed nonnegative half-line. The
canonical partial-map powers retain their exact domains; the graph norm on
D(A^j) is ‖x‖ + ‖A^j x‖, including j = 0. -/
noncomputable section
open Set
open scoped NNReal
namespace ExpandedFA.Semigroups.ClassicalEvolutionSpec
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

abbrev A (T : C0Semigroup 𝕜 X) := C0SemigroupSpec.generatorValue T
abbrev power (T : C0Semigroup 𝕜 X) (j : ℕ) :=
  Unbounded.OperatorDomainsSpec.powerValue (A T) j

local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance (T : C0Semigroup 𝕜 X) (j : ℕ) :
    NormedSpace ℝ (Unbounded.GraphDomain (power T j)) :=
  NormedSpace.restrictScalars ℝ 𝕜 _

/-- C¹ solution in the ambient space, taking values in the exact generator domain.
No restrictions are imposed on the chosen real-time extension at negative times. -/
def IsClassicalSolution (T : C0Semigroup 𝕜 X) (x : X) (u : ℝ → X) : Prop :=
  u 0 = x ∧ ∃ hu : ∀ t : Ici (0 : ℝ), u t ∈ (A T).domain,
    ContDiffOn ℝ 1 u (Ici 0) ∧
    ∀ t : Ici (0 : ℝ), HasDerivWithinAt u (A T ⟨u t, hu t⟩) (Ici 0) t

def ClassicalExistence : Prop := ∀ (T : C0Semigroup 𝕜 X) (x : (A T).domain),
  IsClassicalSolution T x (fun t : ℝ => T.operators t.toNNReal x)

def ClassicalUniqueness : Prop := ∀ (T : C0Semigroup 𝕜 X) (x : (A T).domain)
  (u : ℝ → X), IsClassicalSolution T x u →
    ∀ t : ℝ, 0 ≤ t → u t = T.operators t.toNNReal x

/-- An actual graph-valued lift of the orbit is C^(k-j) on the closed half-line.
In particular its derivatives at zero are right derivatives, not derivatives of
the arbitrary negative-time extension. -/
def HigherGraphRegularity : Prop := ∀ (T : C0Semigroup 𝕜 X) (k j : ℕ), j ≤ k →
  ∀ x : (power T k).domain,
    ∃ u : ℝ → Unbounded.GraphDomain (power T j),
      (∀ t : ℝ, 0 ≤ t →
        (Unbounded.GraphDomain.toDomain _ (u t) : X) = T.operators t.toNNReal x) ∧
      ContDiffOn ℝ (k - j) u (Ici 0)

set_option linter.checkUnivs false

def ClassicalExistenceExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  ClassicalExistence (𝕜 := 𝕜) (X := X)
def ClassicalUniquenessExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  ClassicalUniqueness (𝕜 := 𝕜) (X := X)
def HigherGraphRegularityExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  HigherGraphRegularity (𝕜 := 𝕜) (X := X)
end ExpandedFA.Semigroups.ClassicalEvolutionSpec
