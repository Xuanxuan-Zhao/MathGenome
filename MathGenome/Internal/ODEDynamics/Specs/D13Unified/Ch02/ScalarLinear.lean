import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Independent specification of paper.tex, Theorem d13:02:linear.
Time is real for both real and complex states. Coefficients and curves use
ambient representatives, with continuity and derivatives required only on the
recorded actual interval. No regularity off that interval is assumed.
`NormedSpace.exp` specializes to `Real.exp` and `Complex.exp` by the library
identities `Real.exp_eq_exp_ℝ` and `Complex.exp_eq_exp_ℂ`.
-/
noncomputable section
open Set MeasureTheory

namespace D13Unified.ScalarLinear
variable {𝕂 : Type*} [RCLike 𝕂]

/-- The oriented primitive based at the specified initial time. -/
def primitive (a : ℝ → 𝕂) (s t : ℝ) : 𝕂 := ∫ r in s..t, a r

/-- The variation-of-constants curve; only its values on `I` matter. -/
def variation (a b : ℝ → 𝕂) (s : ℝ) (ξ : 𝕂) (t : ℝ) : 𝕂 :=
  NormedSpace.exp (primitive a s t) *
    (ξ + ∫ r in s..t, NormedSpace.exp (-primitive a s r) * b r)

/-- Scalar specialization of the common endpoint-aware differential IVP
convention. On an open interval this is equivalent to the C¹ convention;
on a closed interval the within derivatives are one-sided at its endpoints.
This direct form accommodates coefficients defined only on `I`, which need
not admit an extension to an open neighborhood of an included endpoint. -/
def IsIVP (I : TimeInterval) (a b : ℝ → 𝕂) (s : ℝ) (ξ : 𝕂)
    (x : ℝ → 𝕂) : Prop :=
  ContinuousOn x I.carrier ∧ s ∈ I.carrier ∧ x s = ξ ∧
    ∀ t ∈ I.carrier, HasDerivWithinAt x (a t * x t + b t) I.carrier t
end D13Unified.ScalarLinear

namespace Specs.D13Unified.Ch02.ScalarLinear
open _root_.D13Unified _root_.D13Unified.ScalarLinear

/-- Necessity and sufficiency, with existence and uniqueness on the whole
original interval, for either real or complex coefficients. Equality is only
on the actual interval, not between arbitrary ambient representatives. -/
def variationOfConstantsExpected : Prop :=
  ∀ {𝕂 : Type} [RCLike 𝕂] (I : TimeInterval) (a b : ℝ → 𝕂)
    (s : ℝ) (ξ : 𝕂),
    ContinuousOn a I.carrier → ContinuousOn b I.carrier → s ∈ I.carrier →
    IsIVP I a b s ξ (variation a b s ξ) ∧
      ∀ x : ℝ → 𝕂, IsIVP I a b s ξ x ↔ EqOn x (variation a b s ξ) I.carrier

/-- Explicit bridge to C¹ regularity and ordinary derivatives on open
intervals, as in the source's classical solution convention. -/
def classicalExpected : Prop :=
  ∀ {𝕂 : Type} [RCLike 𝕂] (I : OpenTimeInterval) (a b : ℝ → 𝕂)
    (s : ℝ) (ξ : 𝕂),
    ContinuousOn a I.carrier → ContinuousOn b I.carrier → s ∈ I.carrier →
    ∀ x : ℝ → 𝕂,
      (ContDiffOn ℝ 1 x I.carrier ∧ x s = ξ ∧
        ∀ t ∈ I.carrier, HasDerivAt x (a t * x t + b t) t) ↔
      EqOn x (variation a b s ξ) I.carrier

/-- Compatibility with the shared ODE predicate whenever its evaluation
agrees with the scalar equation along the given graph. -/
def sharedIVPExpected : Prop :=
  ∀ {𝕂 : Type} [RCLike 𝕂] (F : ODE 𝕂) (I : TimeInterval)
    (a b x : ℝ → 𝕂) (s : ℝ) (ξ : 𝕂),
    (∀ t ∈ I.carrier, (t, x t) ∈ F.domain) →
    (∀ t ∈ I.carrier, F.eval t (x t) = a t * x t + b t) →
    (Specs.D13Unified.Ch01.SolutionConcepts.ivpOnValue F I x s ξ ↔ IsIVP I a b s ξ x)
end Specs.D13Unified.Ch02.ScalarLinear
