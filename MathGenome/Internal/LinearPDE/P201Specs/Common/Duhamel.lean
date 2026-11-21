import MathGenome.Internal.LinearPDE.P201Specs.Common.IntegratedMild

/-! Independent statements for paper.tex, Theorem `thm:pde-duhamel`
(lines 519–575 in the adopted source).

The formula, generator, integrated predicate and mild predicate are the shared
objects of `IntegratedMild`. The classical predicate below is the exact
MathGenome predicate: C¹ on the closed time interval, values in the full
generator domain, the equation including one-sided endpoint derivatives, and
continuity into the domain with its sum graph norm. No condition is imposed on
the chosen extensions outside the time interval.

The converse is stated for arbitrary L¹ forcing whenever a classical solution
exists; it does not require C¹ forcing. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal

namespace P201.Common.Duhamel.Expected
open ExpandedFA ExpandedFA.Semigroups
open P201.Common.IntegratedMild
universe u v

/-- Existence and uniqueness in the continuous integrated class, the Duhamel
formula, and equivalence with the mild predicate, for unrestricted L¹ data. -/
def IntegratedDuhamel : Prop := IntegratedMild.Expected.IntegratedWellPosedness.{u, v}

/-- The original sufficient hypotheses for classical regularity of the same
formula, including continuity in the complete sum graph norm. -/
def ClassicalDuhamel : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X],
    letI : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
    ∀
    (S : C0Semigroup 𝕜 X) (T : ℝ≥0), 0 < (T : ℝ) →
    ∀ (x₀ : (Generator S).domain) (f : ℝ → X),
      ContDiffOn ℝ 1 f (Icc 0 (T : ℝ)) →
      InhomogeneousEvolutionSpec.IsClassicalSolution S T x₀ f
        (mildSolution S x₀ f)

/-- Every classical solution for the given L¹ data satisfies the integrated
equation and the same variation-of-constants formula on the entire slab. -/
def ClassicalConverse : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (S : C0Semigroup 𝕜 X) (T : ℝ≥0), 0 < (T : ℝ) →
    ∀ (x₀ : X) (f : ℝ → X), IntegrableOn f (Icc 0 (T : ℝ)) →
    ∀ u : ℝ → X, InhomogeneousEvolutionSpec.IsClassicalSolution S T x₀ f u →
      IsIntegratedSolution S T x₀ f u ∧ IsMildSolution S T x₀ f u

end P201.Common.Duhamel.Expected
