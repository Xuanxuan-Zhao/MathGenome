import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.MintySignCounterexamples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Geometry.MintyCompactDomain

namespace ExpandedFA.Geometry.MintySignCounterexamples
open Set
open scoped BigOperators
open Specs.ExpandedFA.Geometry.MintySignCounterexamples
universe u v

@[simp] lemma identityDual_apply (v x : ℝ) : identityDual v x = v * x := rfl

/-- The real identity is monotone under the continuous-dual identification. -/
theorem identity_monotone : IdentityMonotone := by
  intro x y
  change 0 ≤ x * (x-y) - y * (x-y)
  nlinarith [sq_nonneg (x-y)]

/-- The endpoint tests force u ≥ 1 and u ≤ -1 simultaneously. -/
theorem reversed_sign_counterexample : ReversedSignCounterexample := by
  rintro ⟨u, hu⟩
  have hp := hu 1 (by constructor <;> norm_num)
  have hn := hu (-1) (by constructor <;> norm_num)
  simp only [identityDual_apply] at hp hn
  linarith

/-- Direct evaluation of the source quadratic with weights (1,-1). -/
theorem signed_quadratic_counterexample : SignedQuadraticCounterexample := by
  norm_num [SignedQuadraticCounterexample, Fin.sum_univ_two,
    signedWeights, twoPoints]

/-- Symmetrizing the finite payoff gives the valid probability-weight sign. -/
theorem probability_quadratic_nonpositive : ProbabilityQuadraticNonpositive.{u, v} := by
  intro X _ _ D A hA ι _ v s hs _
  apply MintyCompactDomain.matrixPayoff_diagonal_nonpos
    (fun i j => A (v j) ((v i : X) - v j)) ?_ s hs
  intro i j
  have h := hA (v i) (v j)
  simp only [sub_apply, map_sub] at h ⊢
  linarith

/-- Corrected weak Minty inequality, retaining the arbitrary-domain and
empty-intersection cases of the accepted existence theorem. -/
theorem corrected_weak_minty_exists : CorrectedWeakMintyExistence.{u} := by
  exact MintyCompactDomain.weak_minty_exists

end ExpandedFA.Geometry.MintySignCounterexamples
