import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsExistence
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! K03.15.rs_density, paper.tex:3726–3741. The derivative `g` is the
continuous closed-interval extension, with within derivatives at the endpoints.
Both integrals are the existing proper Darboux and refinement Stieltjes objects.
The singleton interval and arbitrary closed-cell tags are included. -/
namespace Specs.SingleVariableAnalysis.Ch15.RsDensity
open _root_.SingleVariableAnalysis.Riemann

/-- The uniform modulus of the real derivative on the specified interval.
Only nonnegative radii are used in the statements below. -/
noncomputable def derivativeModulus (a b : ℝ) (g : ℝ → ℝ) (δ : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ Set.Icc a b, ∃ y ∈ Set.Icc a b,
    |x - y| ≤ δ ∧ r = ‖g x - g y‖}

/-- Explicit right limit zero of the derivative modulus. -/
def modulusVanishes : Prop := ∀ (a b : ℝ), a ≤ b → ∀ g : ℝ → ℝ,
  ContinuousOn g (Set.Icc a b) →
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ r : ℝ, 0 ≤ r → r < δ → 0 ≤ derivativeModulus a b g r ∧
      derivativeModulus a b g r < ε

/-- The exact comparison estimate, uniform in every partition and its tags.
The normed real vector space generality includes both source scalar choices. -/
def meshComparison : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ), a ≤ b → ∀ (f : ℝ → E) (α g : ℝ → ℝ),
    ContinuousOn f (Set.Icc a b) →
    (∀ x ∈ Set.Icc a b, HasDerivWithinAt α (g x) (Set.Icc a b) x) →
    ContinuousOn g (Set.Icc a b) →
    ∀ (P : PartitionData a b)
      (t : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P),
    ‖RsSums.sumValue P t f α -
      Specs.SingleVariableAnalysis.Ch08.Partitions.sumValue P t (fun x => g x • f x)‖ ≤
      RsExistence.supNorm a b f *
        derivativeModulus a b g (Specs.SingleVariableAnalysis.Ch08.Partitions.meshValue P) *
        (b - a)

/-- Existence of both integrals, the density identity, and the direct mesh limit. -/
def realDensity : Prop := ∀ (a b : ℝ), a ≤ b → ∀ (f α g : ℝ → ℝ),
  ContinuousOn f (Set.Icc a b) →
  (∀ x ∈ Set.Icc a b, HasDerivWithinAt α (g x) (Set.Icc a b) x) →
  ContinuousOn g (Set.Icc a b) →
  ∃ h : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue
      (fun x => f x * g x) a b,
    RsSums.integralValue a b f α
      (Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue _ h) ∧
    RsExistence.meshLimit a b f α
      (Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue _ h)

def complexDensity : Prop := ∀ (a b : ℝ), a ≤ b →
  ∀ (f : ℝ → ℂ) (α g : ℝ → ℝ),
  ContinuousOn f (Set.Icc a b) →
  (∀ x ∈ Set.Icc a b, HasDerivWithinAt α (g x) (Set.Icc a b) x) →
  ContinuousOn g (Set.Icc a b) →
  ∃ h : Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegrableValue
      (fun x => f x * (g x : ℂ)) a b,
    RsSums.integralValue a b f α
      (Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue _ h) ∧
    RsExistence.meshLimit a b f α
      (Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue _ h)

end Specs.SingleVariableAnalysis.Ch15.RsDensity
