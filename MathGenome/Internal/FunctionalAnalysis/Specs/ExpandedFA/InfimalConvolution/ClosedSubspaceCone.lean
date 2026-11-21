import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.BanachFullConeExactness

/-! Independent specification of `fa2:p1:infconv-banach-closed-cone`,
paper.tex:7257–7353. The cone is the literal nonnegative scaling union of
finite-domain differences. The subspace has its inherited norm. -/
namespace ExpandedFA.InfimalConvolution.ClosedSubspaceCone.Spec

open ExpandedFA.P1 ExtendedConvexFunctions
open Definitions.Spec

/-- A real Banach space is supplied by the theorem quantifiers. No reflexivity
or continuity at a common point is included in these hypotheses. -/
def Hypotheses (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : ExtendedFunction E) (L : Submodule ℝ E) : Prop :=
  ExtendedConvexFunctions.Spec.ProperValue E φ ∧
  ExtendedConvexFunctions.Spec.ProperValue E ψ ∧
  ExtendedConvexFunctions.Spec.ExtendedConvexValue E φ ∧
  ExtendedConvexFunctions.Spec.ExtendedConvexValue E ψ ∧
  ExtendedConvexFunctions.Spec.LowerSemicontinuousValue E φ ∧
  ExtendedConvexFunctions.Spec.LowerSemicontinuousValue E ψ ∧
  (FiniteDomainValue E φ ∩ FiniteDomainValue E ψ).Nonempty ∧
  IsClosed (L : Set E) ∧ DomainDifferenceConeValue E φ ψ = (L : Set E)

/-- The identity includes infinite values; there is no primal attainment claim. -/
def ExactConjugateFormula : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (L : Submodule ℝ E), Hypotheses E φ ψ L →
    ∀ f : E →L[ℝ] ℝ, InfimalConvolutionValue E φ ψ f =
      C06Conjugates.Spec.ConvexConjugateValue E (fun x => φ x + ψ x) f

def FiniteValueAttainment : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (L : Submodule ℝ E), Hypotheses E φ ψ L →
    ∀ (f : E →L[ℝ] ℝ) (r : ℝ),
      C06Conjugates.Spec.ConvexConjugateValue E (fun x => φ x + ψ x) f = (r : EReal) →
      ∃ g : E →L[ℝ] ℝ, ConjugateSplitCostValue E φ ψ f g = (r : EReal)

def ExactDomainSum : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (L : Submodule ℝ E), Hypotheses E φ ψ L →
    ∀ f : E →L[ℝ] ℝ,
      C06Conjugates.Spec.ConvexConjugateValue E (fun x => φ x + ψ x) f < ⊤ ↔
      ∃ a b : E →L[ℝ] ℝ, f = a + b ∧
        C06Conjugates.Spec.ConvexConjugateValue E φ a < ⊤ ∧
        C06Conjugates.Spec.ConvexConjugateValue E ψ b < ⊤

def PrimalDualIdentity : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (L : Submodule ℝ E), Hypotheses E φ ψ L →
    let p := ⨅ x : E, C06Conjugates.Spec.ExtendedRealValueValue (φ x + ψ x)
    p ≠ ⊤ ∧
    p = ⨆ g : E →L[ℝ] ℝ,
      -C06Conjugates.Spec.ConvexConjugateValue E φ (-g) -
        C06Conjugates.Spec.ConvexConjugateValue E ψ g ∧
    (∀ r : ℝ, p = (r : EReal) → ∃ g : E →L[ℝ] ℝ,
      -C06Conjugates.Spec.ConvexConjugateValue E φ (-g) -
        C06Conjugates.Spec.ConvexConjugateValue E ψ g = (r : EReal))

/-- Only restrictions of the ambient split functionals are bounded. -/
def BoundedRestrictedSplits : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (L : Submodule ℝ E), Hypotheses E φ ψ L →
    ∀ (B : Set (E →L[ℝ] ℝ)), Bornology.IsBounded B → ∀ α : ℝ,
      Bornology.IsBounded {k : L →L[ℝ] ℝ | ∃ (f g : E →L[ℝ] ℝ),
        f ∈ B ∧ ConjugateSplitCostValue E φ ψ f g ≤ (α : EReal) ∧
        k = g.comp L.subtypeL}

/-- Each split admits an ambient representative with the same restriction and
cost, uniformly bounded over bounded total functionals and a fixed cost level. -/
def BoundedRepresentatives : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (L : Submodule ℝ E), Hypotheses E φ ψ L →
    ∀ (B : Set (E →L[ℝ] ℝ)), Bornology.IsBounded B → ∀ α : ℝ,
      ∃ C : ℝ, ∀ (f g : E →L[ℝ] ℝ), f ∈ B →
        ConjugateSplitCostValue E φ ψ f g ≤ (α : EReal) →
        ∃ G : E →L[ℝ] ℝ, G.comp L.subtypeL = g.comp L.subtypeL ∧
          ConjugateSplitCostValue E φ ψ f G = ConjugateSplitCostValue E φ ψ f g ∧
          ‖G‖ ≤ C

universe u
/-- In the full-space case all ambient splits are bounded. -/
def FullConeUniformBounds : Prop := UniformSplitBounds.Spec.BoundedSplitSublevels.{u}

end ExpandedFA.InfimalConvolution.ClosedSubspaceCone.Spec
