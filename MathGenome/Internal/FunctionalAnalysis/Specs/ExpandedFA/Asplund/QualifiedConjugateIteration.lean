import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.ConjugateLimits

/-! The full arithmetic/infimal-convolution theorem, including its qualified
conjugate formula. The shared real-valued iterates encode finiteness; the
conjugates take values in EReal and use the continuous real dual.
Completeness is never assumed. Continuity is required only in the last clauses.
Source: paper.tex, fa2:p1:asplund-convex-iteration, 6829–6911. -/
namespace ExpandedFA.Asplund.QualifiedConjugateIteration.Spec

universe u

open Iteration.Spec OrderLimit.Spec Filter
open scoped Topology

def PrimalConclusions : Prop :=
  OrderLimit.Spec.IteratesProperties.{u} ∧ OrderLimit.Spec.OrderChain.{u} ∧
    OrderLimit.Spec.CommonLimit.{u}

def UnqualifiedConjugateConclusions : Prop :=
  ConjugateLimits.Spec.PhiConjugateLimit.{u} ∧
    ConjugateLimits.Spec.PsiConjugateRecurrence.{u} ∧
    ConjugateLimits.Spec.PsiConjugateLimit.{u} ∧
    ConjugateLimits.Spec.PsiConjugateLimitFullDomain.{u}

def IteratesContinuousAt : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), InitialDataValue E φ₀ ψ₀ →
    ∀ x₀, ContinuousAt φ₀ x₀ → ∀ n,
      ContinuousAt (phiValue E φ₀ ψ₀ n) x₀ ∧
        ContinuousAt (psiValue E φ₀ ψ₀ n) x₀

def QualifiedConjugateFormula : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), InitialDataValue E φ₀ ψ₀ →
    ∀ x₀, ContinuousAt φ₀ x₀ → ∀ n (f : E →L[ℝ] ℝ),
      conjugateValue E (phiValue E φ₀ ψ₀ (n + 1)) f =
        ((1 / 2 : ℝ) : EReal) * (⨅ g : E →L[ℝ] ℝ,
          conjugateValue E (phiValue E φ₀ ψ₀ n) (f + g) +
          conjugateValue E (psiValue E φ₀ ψ₀ n) (f - g))

/-- A minimizing continuous-dual splitting is required only at finite values. -/
def QualifiedConjugateAttainment : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), InitialDataValue E φ₀ ψ₀ →
    ∀ x₀, ContinuousAt φ₀ x₀ → ∀ n (f : E →L[ℝ] ℝ),
      conjugateValue E (phiValue E φ₀ ψ₀ (n + 1)) f < ⊤ →
      ∃ g : E →L[ℝ] ℝ,
        (⨅ k : E →L[ℝ] ℝ,
          conjugateValue E (phiValue E φ₀ ψ₀ n) (f + k) +
          conjugateValue E (psiValue E φ₀ ψ₀ n) (f - k)) =
        conjugateValue E (phiValue E φ₀ ψ₀ n) (f + g) +
          conjugateValue E (psiValue E φ₀ ψ₀ n) (f - g)

end ExpandedFA.Asplund.QualifiedConjugateIteration.Spec
