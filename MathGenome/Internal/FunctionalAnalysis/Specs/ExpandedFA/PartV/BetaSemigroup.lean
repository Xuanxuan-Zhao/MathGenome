import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FractionalIntegrals

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ExpandedFA.PartV.BetaSemigroup.Spec
open ExpandedFA.PartV.FractionalIntegrals.Spec

/-- The full Beta convolution formula, including absolute integrability. -/
def BetaConvolution : Prop := ∀ (α β v t : ℝ), 0 < α → 0 < β → v < t →
  IntegrableOn (fun s => (t-s) ^ (α-1) * (s-v) ^ (β-1)) (Ioc v t) ∧
  (∫ s in Ioc v t, (t-s) ^ (α-1) * (s-v) ^ (β-1)) =
    (Real.Gamma α * Real.Gamma β / Real.Gamma (α+β)) * (t-v) ^ (α+β-1)

/-- Absolute Fubini for the zero-extended input and the two truncated kernels.
This is the entire triangular integrand after the translation used in convolution. -/
def AbsoluteFubini : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α β T : ℝ), 0 < α → 0 < β → 0 ≤ T →
    ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ (f : ℝ → 𝕜), MemLp f p (intervalMeasure T) →
    ∀ᵐ t ∂intervalMeasure T,
      Integrable (fun z : ℝ × ℝ =>
        powerKernel α T z.2 • (powerKernel β T (z.1-z.2) •
          (Ioc 0 T).indicator f (t-z.1))) (volume.prod volume)

/-- The normalized law for all representatives, hence on every Lp quotient. -/
def RepresentativeSemigroup : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α β T : ℝ), 0 < α → 0 < β → 0 ≤ T →
    ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ (f : ℝ → 𝕜), MemLp f p (intervalMeasure T) →
    fractionalValue α (fractionalValue β f) =ᵐ[intervalMeasure T]
      fractionalValue (α+β) f

/-- All bounded realizations with the defining integral have the semigroup law. -/
def ContinuousSemigroup : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α β T : ℝ) (_hα : 0 < α) (_hβ : 0 < β) (hT : 0 ≤ T)
    (A B C : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜)),
    (∀ f t, A f t = fractionalValue α (continuousExtension hT f) t) →
    (∀ f t, B f t = fractionalValue β (continuousExtension hT f) t) →
    (∀ f t, C f t = fractionalValue (α+β) (continuousExtension hT f) t) →
    A.comp B = C

def LpSemigroup : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α β T : ℝ) (_hα : 0 < α) (_hβ : 0 < β) (_hT : 0 ≤ T)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A B C : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T)),
    (∀ f : Lp 𝕜 p (intervalMeasure T),
      (A f : ℝ → 𝕜) =ᵐ[intervalMeasure T] fractionalValue α f) →
    (∀ f : Lp 𝕜 p (intervalMeasure T),
      (B f : ℝ → 𝕜) =ᵐ[intervalMeasure T] fractionalValue β f) →
    (∀ f : Lp 𝕜 p (intervalMeasure T),
      (C f : ℝ → 𝕜) =ᵐ[intervalMeasure T] fractionalValue (α+β) f) →
    A.comp B = C

/-- Existence and the law together, with no assumed realization. -/
def ContinuousSemigroupRealization : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α β T : ℝ), 0 < α → 0 < β → ∀ hT : 0 ≤ T,
    ∃ A B C : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜),
      (∀ f t, A f t = fractionalValue α (continuousExtension hT f) t) ∧
      (∀ f t, B f t = fractionalValue β (continuousExtension hT f) t) ∧
      (∀ f t, C f t = fractionalValue (α+β) (continuousExtension hT f) t) ∧
      A.comp B = C

def LpSemigroupRealization : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α β T : ℝ), 0 < α → 0 < β → 0 ≤ T →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ A B C : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T),
      (∀ f : Lp 𝕜 p (intervalMeasure T),
        (A f : ℝ → 𝕜) =ᵐ[intervalMeasure T] fractionalValue α f) ∧
      (∀ f : Lp 𝕜 p (intervalMeasure T),
        (B f : ℝ → 𝕜) =ᵐ[intervalMeasure T] fractionalValue β f) ∧
      (∀ f : Lp 𝕜 p (intervalMeasure T),
        (C f : ℝ → 𝕜) =ᵐ[intervalMeasure T] fractionalValue (α+β) f) ∧
      A.comp B = C
end ExpandedFA.PartV.BetaSemigroup.Spec
