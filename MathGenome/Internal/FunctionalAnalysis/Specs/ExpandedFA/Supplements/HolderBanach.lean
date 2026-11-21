import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.DifferentiableCompleteness
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.HolderCompleteness
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! The full proposition at paper.tex:5802–5818, using the canonical interval
and bounded metric-space objects. Multiplication is specified by its values,
and inclusion preserves every function value. None of these Props is assumed. -/
namespace ExpandedFA.Supplements.HolderBanachSpec
open HolderSpacesSpec
universe u v

/-- All three completeness assertions, in the previously specified norms. -/
def Completeness : Prop :=
  DifferentiableCompletenessSpec.CmComplete.{u} ∧
  HolderCompletenessSpec.CmHolderComplete.{u} ∧ HolderCompletenessSpec.BoundedHolderComplete.{v, u}

/-- Continuous pointwise multiplication on C^m, real or complex. -/
def CmMultiplication : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) (a b : ℝ) (hab : a < b),
    ∃ P : Cm 𝕜 m hab →L[𝕜] Cm 𝕜 m hab →L[𝕜] Cm 𝕜 m hab,
      ∀ f g x, P f g x = f x * g x

/-- Continuous pointwise multiplication on C^{m,α}, including α=1 and m=0. -/
def CmHolderMultiplication : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) (a b : ℝ) (hab : a < b) (α : HolderExponent),
    ∃ P : CmHolder 𝕜 m hab α →L[𝕜] CmHolder 𝕜 m hab α →L[𝕜] CmHolder 𝕜 m hab α,
      ∀ f g x, P f g x = f x * g x

/-- Continuous multiplication for bounded Hölder functions on any metric space. -/
def BoundedHolderMultiplication : Prop :=
  ∀ (X 𝕜 : Type*) [MetricSpace X] [RCLike 𝕜] (α : HolderExponent),
    ∃ P : BoundedHolder X 𝕜 α →L[𝕜]
      BoundedHolder X 𝕜 α →L[𝕜] BoundedHolder X 𝕜 α,
      ∀ f g x, P f g x = f x * g x

/-- Exponent minimum, with no extension or endpoint regularity assumption. -/
def MixedHolderProduct : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (a b : ℝ) (hab : a < b) (α β : HolderExponent)
    (f : CmHolder 𝕜 0 hab α) (g : CmHolder 𝕜 0 hab β),
    ∃ h : CmHolder 𝕜 0 hab
      ⟨min α.val β.val, lt_min α.property.1 β.property.1,
        (min_le_left _ _).trans α.property.2⟩,
      ∀ x, h x = f x * g x

/-- The continuous inclusion for the manuscript's strict total-regularity inequality. -/
def ContinuousInclusion : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (m n : ℕ) (a b : ℝ) (hab : a < b)
    (α β : HolderExponent),
    (m : ℝ) + (α.val : ℝ) < (n : ℝ) + (β.val : ℝ) →
    ∃ J : CmHolder 𝕜 n hab β →L[𝕜] CmHolder 𝕜 m hab α,
      ∀ f x, J f x = f x

/-- The complete original obligation, with all conclusions retained. -/
def HolderBanach : Prop := Completeness.{u, v} ∧ CmMultiplication.{u} ∧ CmHolderMultiplication.{u} ∧
  BoundedHolderMultiplication.{v, u} ∧ MixedHolderProduct.{u} ∧ ContinuousInclusion.{u}

end ExpandedFA.Supplements.HolderBanachSpec
