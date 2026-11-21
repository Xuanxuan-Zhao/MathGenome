import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.OrderLimit
import Mathlib.Topology.Instances.EReal.Lemmas

/-! Conjugate limits in `fa2:p1:asplund-convex-iteration` (paper.tex
6838–6885). No completeness or continuity assumption is imposed. All
conjugates use the continuous real dual and the shared EReal supremum.
The finite-domain condition is explicit only for the decreasing limit. -/
namespace ExpandedFA.Asplund.ConjugateLimits.Spec

open Iteration.Spec OrderLimit.Spec Filter
open scoped Topology

/-- Nonnegative extended values, reverse primal order, and decreasing ψ conjugates. -/
def ConjugateOrder : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), InitialDataValue E φ₀ ψ₀ → ∀ f : E →L[ℝ] ℝ,
    (∀ n, 0 ≤ conjugateValue E (phiValue E φ₀ ψ₀ n) f ∧
      conjugateValue E (phiValue E φ₀ ψ₀ n) f ≤
        conjugateValue E (thetaValue E φ₀ ψ₀) f ∧
      conjugateValue E (thetaValue E φ₀ ψ₀) f ≤
        conjugateValue E (psiValue E φ₀ ψ₀ n) f) ∧
    Antitone (fun n => conjugateValue E (psiValue E φ₀ ψ₀ n) f)

/-- Increasing convergence, including an infinite limit. -/
def PhiConjugateLimit : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), InitialDataValue E φ₀ ψ₀ → ∀ f : E →L[ℝ] ℝ,
    Monotone (fun n => conjugateValue E (phiValue E φ₀ ψ₀ n) f) ∧
    (⨆ n, conjugateValue E (phiValue E φ₀ ψ₀ n) f) =
      conjugateValue E (thetaValue E φ₀ ψ₀) f ∧
    Tendsto (fun n => conjugateValue E (phiValue E φ₀ ψ₀ n) f) atTop
      (𝓝 (conjugateValue E (thetaValue E φ₀ ψ₀) f))

/-- The arithmetic recurrence on nonnegative extended conjugates; no attainment
or continuity is assumed. Multiplication by the finite scalar 1/2 includes +∞. -/
def PsiConjugateRecurrence : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), InitialDataValue E φ₀ ψ₀ → ∀ n (f : E →L[ℝ] ℝ),
    conjugateValue E (psiValue E φ₀ ψ₀ (n + 1)) f =
      ((1 / 2 : ℝ) : EReal) * (conjugateValue E (phiValue E φ₀ ψ₀ n) f +
        conjugateValue E (psiValue E φ₀ ψ₀ n) f)

/-- Decreasing convergence at every point of the initial conjugate's finite domain. -/
def PsiConjugateLimit : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), InitialDataValue E φ₀ ψ₀ → ∀ (f : E →L[ℝ] ℝ),
    conjugateValue E ψ₀ f < ⊤ →
    Antitone (fun n => conjugateValue E (psiValue E φ₀ ψ₀ n) f) ∧
    (⨅ n, conjugateValue E (psiValue E φ₀ ψ₀ n) f) =
      conjugateValue E (thetaValue E φ₀ ψ₀) f ∧
    Tendsto (fun n => conjugateValue E (psiValue E φ₀ ψ₀ n) f) atTop
      (𝓝 (conjugateValue E (thetaValue E φ₀ ψ₀) f))

/-- In particular the convergence holds throughout the dual if the initial
conjugate has full finite domain. -/
def PsiConjugateLimitFullDomain : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), InitialDataValue E φ₀ ψ₀ →
    (∀ f : E →L[ℝ] ℝ, conjugateValue E ψ₀ f < ⊤) →
    ∀ f : E →L[ℝ] ℝ,
    Tendsto (fun n => conjugateValue E (psiValue E φ₀ ψ₀ n) f) atTop
      (𝓝 (conjugateValue E (thetaValue E φ₀ ψ₀) f))

end ExpandedFA.Asplund.ConjugateLimits.Spec
