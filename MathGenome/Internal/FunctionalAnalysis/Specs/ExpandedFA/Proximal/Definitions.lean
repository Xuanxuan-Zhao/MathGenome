import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.Definitions
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
Independent definitions for paper.tex:8443–8459, `fa2:p2:hilbert-prox-definition`.
Primal values are the shared `WithTop ℝ`; infima and conjugates use `EReal`.
The real inner product represents continuous real-linear functionals.

The total choice defining the proximal map has no certificate argument.
`ProximalMapSelection` and `ProximalMapOfUniqueMinimizer` give its exact
obligation when a minimizer exists. The analytic existence/uniqueness theorem
for proper convex norm-lsc functions and μ > 0 is allocated separately to
`mid_prox_existence`, which depends on this definitions interface.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Proximal.Spec

open ExpandedFA.P1.ExtendedConvexFunctions

universe u

def ProximalObjectiveType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ExtendedFunction H → ℝ → H → H → WithTop ℝ

/-- The energy in the displayed definition, before taking its infimum. -/
def ProximalObjectiveValue : ProximalObjectiveType.{u} :=
  fun _ _ _ φ μ f v => φ v + ((‖f - v‖ ^ 2 / (2 * μ) : ℝ) : WithTop ℝ)

def MoreauEnvelopeType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ExtendedFunction H → ℝ → H → EReal

/-- A genuine extended-real infimum, allowing −∞ before existence is proved. -/
def MoreauEnvelopeValue : MoreauEnvelopeType.{u} :=
  fun H _ _ φ μ f =>
    ⨅ v, P1.C06Conjugates.Spec.ExtendedRealValueValue
      (ProximalObjectiveValue H φ μ f v)

def IsProximalMinimizerType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ExtendedFunction H → ℝ → H → H → Prop

/-- A finite-energy global minimizer; all competitors, also those of infinite
energy, are included. For proper φ the guard follows from minimality. -/
def IsProximalMinimizerValue : IsProximalMinimizerType.{u} :=
  fun H _ _ φ μ f u =>
    u ∈ P1.ExtendedConvexFunctions.Spec.finiteDomainValue H φ ∧
      ∀ v, ProximalObjectiveValue H φ μ f u ≤ ProximalObjectiveValue H φ μ f v

def ProximalMapType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ExtendedFunction H → ℝ → H → H

/-- Total choice, with the selection obligation below. No existence or
uniqueness hypothesis is smuggled into an input structure or axiom. Values
outside the source's well-posed setting have no asserted analytic properties. -/
def ProximalMapValue : ProximalMapType.{u} :=
  fun H _ _ φ μ f => Classical.epsilon (IsProximalMinimizerValue H φ μ f)

def HilbertSubdifferentialType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ExtendedFunction H → H → Set H

/-- The finite-domain guard agrees with the canonical Banach subdifferential. -/
def HilbertSubdifferentialValue : HilbertSubdifferentialType.{u} :=
  fun H _ _ φ u =>
    {w | u ∈ P1.ExtendedConvexFunctions.Spec.finiteDomainValue H φ ∧
      ∀ v, φ u + (⟪w, v - u⟫_ℝ : WithTop ℝ) ≤ φ v}

def HilbertConjugateType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ExtendedFunction H → H → EReal

/-- At an infinite primal value the corresponding term is −∞, exactly as in
the canonical Banach conjugate; no properness of the conjugate is assumed. -/
def HilbertConjugateValue : HilbertConjugateType.{u} :=
  fun _ _ _ φ w =>
    ⨆ v, (⟪w, v⟫_ℝ : EReal) - P1.C06Conjugates.Spec.ExtendedRealValueValue (φ v)

def ObjectiveFiniteIff : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H) (μ : ℝ) (f u : H),
    ProximalObjectiveValue H φ μ f u ≠ ⊤ ↔
      u ∈ P1.ExtendedConvexFunctions.Spec.finiteDomainValue H φ

/-- For every proper input this predicate is exactly ordinary global
minimality of the displayed objective, without an extra domain assumption. -/
def MinimizerIffOfProper : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H), P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    ∀ (μ : ℝ) (f u : H), IsProximalMinimizerValue H φ μ f u ↔
      ∀ v, ProximalObjectiveValue H φ μ f u ≤ ProximalObjectiveValue H φ μ f v

def EnvelopeFormula : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H) (μ : ℝ) (f : H),
    MoreauEnvelopeValue H φ μ f =
      ⨅ v, P1.C06Conjugates.Spec.ExtendedRealValueValue (φ v) +
        ((‖f - v‖ ^ 2 / (2 * μ) : ℝ) : EReal)

def EnvelopeIsGLB : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H) (μ : ℝ) (f : H),
    IsGLB (Set.range fun v => P1.C06Conjugates.Spec.ExtendedRealValueValue
      (ProximalObjectiveValue H φ μ f v)) (MoreauEnvelopeValue H φ μ f)

/-- The choice obligation requires existence of a minimizer, rather than
assuming the conclusion from the source's properness/convexity/lsc hypotheses. -/
def ProximalMapSelection : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H) (μ : ℝ) (f : H),
    (∃ u, IsProximalMinimizerValue H φ μ f u) →
      IsProximalMinimizerValue H φ μ f (ProximalMapValue H φ μ f)

def ProximalMapOfUniqueMinimizer : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H) (μ : ℝ) (f : H),
    (∃! u, IsProximalMinimizerValue H φ μ f u) → ∀ u,
      IsProximalMinimizerValue H φ μ f u ↔ u = ProximalMapValue H φ μ f

def EnvelopeAtMinimizer : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H) (μ : ℝ) (f u : H),
    IsProximalMinimizerValue H φ μ f u →
      MoreauEnvelopeValue H φ μ f =
        P1.C06Conjugates.Spec.ExtendedRealValueValue (ProximalObjectiveValue H φ μ f u)

def EnvelopeFiniteOfMinimizer : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H) (μ : ℝ) (f : H),
    (∃ u, IsProximalMinimizerValue H φ μ f u) →
      ∃ r : ℝ, MoreauEnvelopeValue H φ μ f = (r : EReal)

def HilbertSubdifferentialAtFiniteValue : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H) (u : H) (r : ℝ), φ u = (r : WithTop ℝ) →
    HilbertSubdifferentialValue H φ u =
      {w | ∀ v, ((r + ⟪w, v - u⟫_ℝ : ℝ) : WithTop ℝ) ≤ φ v}

def HilbertSubdifferentialAtInfinity : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H) (u : H), φ u = ⊤ →
    HilbertSubdifferentialValue H φ u = ∅

def SubdifferentialRieszPreimage : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H) (u : H),
    HilbertSubdifferentialValue H φ u =
      (InnerProductSpace.toDual ℝ H) ⁻¹' BanachConvex.Spec.SubdifferentialValue H φ u

/-- Every canonical Banach subgradient is represented, with no dimension or
separability assumption. The image also covers the empty subdifferential. -/
def SubdifferentialRieszImage : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H) (u : H),
    BanachConvex.Spec.SubdifferentialValue H φ u =
      (InnerProductSpace.toDual ℝ H) '' HilbertSubdifferentialValue H φ u

def ConjugateRieszIdentification : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H) (w : H),
    HilbertConjugateValue H φ w = P1.C06Conjugates.Spec.ConvexConjugateValue H φ
      (InnerProductSpace.toDual ℝ H w)

def HilbertConjugateIsLUB : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H) (w : H),
    IsLUB (Set.range fun v => (⟪w, v⟫_ℝ : EReal) -
      P1.C06Conjugates.Spec.ExtendedRealValueValue (φ v)) (HilbertConjugateValue H φ w)

def HilbertConjugateNeverBottom : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H), P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    ∀ w : H, HilbertConjugateValue H φ w ≠ ⊥

end ExpandedFA.Proximal.Spec
