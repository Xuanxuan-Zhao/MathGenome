import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.ChernoffProductFormula

/-! Implicit Euler and the first-order Trotter formula, paper.tex,
fa2:p3:product-formula. The scalar field is real or complex and X is Banach.
The sum below is the partial linear map on precisely D(A) ∩ D(B).
Its closability and generation by its closure are explicit hypotheses.
All convergence includes t = 0 and is strong, uniformly on [0,b]. -/
noncomputable section
open Filter Topology Set
open scoped NNReal
namespace ExpandedFA.Semigroups.EulerTrotterSpec
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- (I-hA)⁻¹ for positive h, with the identity step at zero.
The inverse identities in `EulerInverse` establish this interpretation on
A's exact domain, rather than treating an unbounded operator as bounded. -/
def implicitStep (A : Unbounded.Operator 𝕜 X X) (h : ℝ≥0) : X →L[𝕜] X :=
  if h = 0 then ContinuousLinearMap.id 𝕜 X else
    algebraMap ℝ 𝕜 ((h : ℝ)⁻¹) •
      Unbounded.OperatorDomainsSpec.resolventValue (algebraMap ℝ 𝕜 ((h : ℝ)⁻¹)) A

/-- The bounded step is a two-sided inverse of I-hA on the original domain. -/
def EulerInverse : Prop := ∀ (T : C0Semigroup 𝕜 X),
  (∀ t, ‖T.operators t‖ ≤ 1) → ∀ (h : ℝ≥0), 0 < h →
    (∀ y, implicitStep (C0SemigroupSpec.generatorValue T) h y ∈
      (C0SemigroupSpec.generatorValue T).domain) ∧
    (∀ y (hy : implicitStep (C0SemigroupSpec.generatorValue T) h y ∈
        (C0SemigroupSpec.generatorValue T).domain),
      implicitStep (C0SemigroupSpec.generatorValue T) h y -
        algebraMap ℝ 𝕜 (h : ℝ) • C0SemigroupSpec.generatorValue T
          ⟨implicitStep (C0SemigroupSpec.generatorValue T) h y, hy⟩ = y) ∧
    ∀ x : (C0SemigroupSpec.generatorValue T).domain,
      implicitStep (C0SemigroupSpec.generatorValue T) h
        ((x : X) - algebraMap ℝ 𝕜 (h : ℝ) • C0SemigroupSpec.generatorValue T x) = x

/-- T(t)x = lim (I-tA/n)⁻ⁿx, with uniformity on bounded time intervals. -/
def EulerFormula : Prop := ∀ (T : C0Semigroup 𝕜 X),
  (∀ t, ‖T.operators t‖ ≤ 1) →
    ChernoffSpec.ProductConvergence T (implicitStep (C0SemigroupSpec.generatorValue T))

/-- Trotter's product, including the essential closure-generation assumption. -/
def TrotterFormula : Prop := ∀ (TA TB TC : C0Semigroup 𝕜 X),
  (∀ t, ‖TA.operators t‖ ≤ 1) → (∀ t, ‖TB.operators t‖ ≤ 1) →
  (∀ t, ‖TC.operators t‖ ≤ 1) →
  (C0SemigroupSpec.generatorValue TA + C0SemigroupSpec.generatorValue TB).IsClosable →
  (C0SemigroupSpec.generatorValue TA + C0SemigroupSpec.generatorValue TB).closure =
    C0SemigroupSpec.generatorValue TC →
  ChernoffSpec.ProductConvergence TC (fun h => TA.operators h * TB.operators h)

def EulerInverseExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  EulerInverse (𝕜 := 𝕜) (X := X)
def EulerFormulaExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  EulerFormula (𝕜 := 𝕜) (X := X)
def TrotterFormulaExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  TrotterFormula (𝕜 := 𝕜) (X := X)
end ExpandedFA.Semigroups.EulerTrotterSpec
