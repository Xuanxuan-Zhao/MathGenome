import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.BetaSemigroup
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Scalar Abel inversion, paper.tex, fa2:p5:abel, with its authorized
positive-length and singleton endpoint conventions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ExpandedFA.PartV.AbelInversion.Spec
open ExpandedFA.PartV.FractionalIntegrals.Spec

/-- A C¹ datum on the closed interval, with its continuous one-sided derivative.
Outside the interval neither function is constrained or used. -/
def C1On {𝕜 : Type} [RCLike 𝕜] (T : ℝ) (g g' : ℝ → 𝕜) : Prop :=
  ContinuousOn g (Icc 0 T) ∧ ContinuousOn g' (Icc 0 T) ∧
    ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt g (g' t) (Icc 0 T) t

/-- Identification with the usual C¹ regularity and the actual within derivative
on a nondegenerate interval. -/
def C1Identification : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ), 0 < T → ∀ (g g' : ℝ → 𝕜),
    C1On T g g' ↔ ContDiffOn ℝ 1 g (Icc 0 T) ∧
      EqOn g' (derivWithin g (Icc 0 T)) (Icc 0 T)

/-- The canonical representative; the asserted inversion formula is for t>0.
The integral and real-power conventions also assign its value at zero. -/
def abelRepresentative {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (g g' : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  (t ^ (-α) / Real.Gamma (1-α)) • g 0 + fractionalValue (1-α) g' t

/-- Absolute existence and pointwise reconstruction on the punctured interval,
and classification of all integrable solutions up to equality a.e. -/
def ScalarInversion : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → α < 1 → 0 < T → ∀ (g g' : ℝ → 𝕜), C1On T g g' →
    Integrable (abelRepresentative α g g') (intervalMeasure T) ∧
    (∀ t ∈ Ioc (0 : ℝ) T,
      IntegrableOn (fun s => (t-s) ^ (α-1) • abelRepresentative α g g' s) (Ioc 0 t) ∧
      fractionalValue α (abelRepresentative α g g') t = g t) ∧
    (∀ (u : ℝ → 𝕜), Integrable u (intervalMeasure T) →
      (fractionalValue α u =ᵐ[intervalMeasure T] g ↔
        u =ᵐ[intervalMeasure T] abelRepresentative α g g'))

/-- Existence and uniqueness in the actual L¹ quotient. -/
def UniqueL1Class : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → α < 1 → 0 < T → ∀ (g g' : ℝ → 𝕜), C1On T g g' →
    ∃! u : Lp 𝕜 1 (intervalMeasure T), fractionalValue α u =ᵐ[intervalMeasure T] g

/-- The a.e. equation and the punctured pointwise equation are equivalent
for all integrable representatives. -/
def EquationEquivalence : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → α < 1 → 0 < T → ∀ (g g' : ℝ → 𝕜), C1On T g g' →
    ∀ (u : ℝ → 𝕜), Integrable u (intervalMeasure T) →
      (fractionalValue α u =ᵐ[intervalMeasure T] g ↔
        ∀ t ∈ Ioc (0 : ℝ) T, fractionalValue α u t = g t)

/-- A continuous extension of the punctured representative exists exactly
when g(0)=0. Every such extension has value zero at zero. In that case the
canonical zero value itself gives a continuous solution on the closed interval. -/
def EndpointExtension : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → α < 1 → 0 < T → ∀ (g g' : ℝ → 𝕜), C1On T g g' →
    ((∃ v : ℝ → 𝕜, ContinuousOn v (Icc 0 T) ∧
        EqOn v (abelRepresentative α g g') (Ioc 0 T)) ↔ g 0 = 0) ∧
    (∀ v : ℝ → 𝕜, ContinuousOn v (Icc 0 T) →
      EqOn v (abelRepresentative α g g') (Ioc 0 T) → v 0 = 0) ∧
    (g 0 = 0 → ContinuousOn (abelRepresentative α g g') (Icc 0 T) ∧
      abelRepresentative α g g' 0 = 0 ∧
      fractionalValue α (abelRepresentative α g g') 0 = g 0) ∧
    (g 0 ≠ 0 → fractionalValue α (abelRepresentative α g g') 0 = 0)

/-- At zero length all L¹ elements coincide; the punctured equation is
vacuous. Imposing it at zero on continuous singleton paths is equivalent to
g(0)=0, with no condition on the unknown's scalar value. -/
def ZeroInterval : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (g : ℝ → 𝕜),
    (∀ u : Lp 𝕜 1 (intervalMeasure 0), u = 0) ∧
    (∀ u : ℝ → 𝕜, ∀ t ∈ Ioc (0 : ℝ) 0, fractionalValue α u t = g t) ∧
    (∀ u : C(Icc (0 : ℝ) 0, 𝕜),
      (∀ t : Icc (0 : ℝ) 0,
        fractionalValue α (continuousExtension (le_refl 0) u) t = g t) ↔ g 0 = 0) ∧
    ((∃ u : C(Icc (0 : ℝ) 0, 𝕜), ∀ t : Icc (0 : ℝ) 0,
        fractionalValue α (continuousExtension (le_refl 0) u) t = g t) ↔ g 0 = 0)

end ExpandedFA.PartV.AbelInversion.Spec
