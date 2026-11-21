import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FractionalIntegrals
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Independent statements for `fa2:p5:holder-repair`, paper.tex:22107–22151.
The counterexample is allocated separately. All functions are scalar valued over
ℝ or ℂ. Hölder regularity is on the entire closed interval, including zero.
A smooth amplitude is C¹ on an open neighborhood of the closed triangle.
-/
noncomputable section
open MeasureTheory Set
namespace ExpandedFA.PartV.FractionalHolder.Spec
open ExpandedFA.PartV.FractionalIntegrals.Spec

/-- The usual finite Hölder seminorm condition, with a real exponent. -/
def HolderOnInterval {𝕜 : Type} [RCLike 𝕜] (β T : ℝ) (f : ℝ → 𝕜) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T,
    ‖f x - f y‖ ≤ C * |x-y| ^ β

def closedTriangle (T : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 ≤ T}

/-- No global extension of k's C¹ regularity is assumed. -/
def SmoothAmplitude {𝕜 : Type} [RCLike 𝕜] (T : ℝ) (k : ℝ × ℝ → 𝕜) : Prop :=
  ∃ U : Set (ℝ × ℝ), IsOpen U ∧ closedTriangle T ⊆ U ∧ ContDiffOn ℝ 1 k U

/-- Unnormalized power integral with scalar amplitude. -/
def amplitudeValue {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (k : ℝ × ℝ → 𝕜)
    (f : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  ∫ s in Ioc 0 t, (t-s) ^ (α-1) • (k (t,s) * f s)

/-- The explicit remainder after subtracting the diagonal amplitude. -/
def remainderValue {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (k : ℝ × ℝ → 𝕜)
    (f : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  ∫ s in Ioc 0 t, (t-s) ^ (α-1) • ((k (t,s) - k (t,t)) * f s)

/-- Constant amplitude gain with the original zero boundary condition. -/
def FractionalGain : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α β T : ℝ), 0 < α → α < 1 → 0 < β → β < 1 → α + β < 1 → 0 ≤ T →
    ∀ f : ℝ → 𝕜, HolderOnInterval β T f → f 0 = 0 →
      HolderOnInterval (α+β) T (fractionalValue α f) ∧ fractionalValue α f 0 = 0

/-- The C¹ remainder construction; continuity of the datum already suffices.
The equality uses the normalized upstream Jα and the original Gamma factor. -/
def AmplitudeRemainder : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → α < 1 → 0 ≤ T →
    ∀ (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜), SmoothAmplitude T k →
    ContinuousOn f (Icc (0 : ℝ) T) →
      (∀ t ∈ Icc (0 : ℝ) T,
        IntegrableOn (fun s => (t-s) ^ (α-1) • (k (t,s) * f s)) (Ioc 0 t) ∧
        IntegrableOn (fun s => (t-s) ^ (α-1) • ((k (t,s)-k (t,t)) * f s)) (Ioc 0 t) ∧
        amplitudeValue α k f t =
          k (t,t) * (Real.Gamma α • fractionalValue α f t) + remainderValue α k f t) ∧
      ContDiffOn ℝ 1 (remainderValue α k f) (Icc (0 : ℝ) T) ∧
      remainderValue α k f 0 = 0

/-- Hölder gain for the original unnormalized amplitude operator. -/
def AmplitudeGain : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α β T : ℝ), 0 < α → α < 1 → 0 < β → β < 1 → α+β < 1 → 0 ≤ T →
    ∀ (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜), SmoothAmplitude T k →
      HolderOnInterval β T f → f 0 = 0 →
      HolderOnInterval (α+β) T (amplitudeValue α k f) ∧ amplitudeValue α k f 0 = 0

/-- Continuous differentiability of the explicit remainder. -/
def RemainderDifferentiability : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → α < 1 → 0 ≤ T →
    ∀ (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜), SmoothAmplitude T k →
      ContinuousOn f (Icc (0 : ℝ) T) →
      ContDiffOn ℝ 1 (remainderValue α k f) (Icc (0 : ℝ) T)

/-- Absolute integrability and the exact amplitude decomposition. -/
def AmplitudeDecomposition : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → ∀ (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜),
    SmoothAmplitude T k → ContinuousOn f (Icc (0 : ℝ) T) →
    ∀ t ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun s => (t-s) ^ (α-1) • (k (t,s) * f s)) (Ioc 0 t) ∧
      IntegrableOn (fun s => (t-s) ^ (α-1) • ((k (t,s)-k (t,t)) * f s)) (Ioc 0 t) ∧
      amplitudeValue α k f t =
        k (t,t) * (Real.Gamma α • fractionalValue α f t) + remainderValue α k f t

def EndpointBound : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α β T : ℝ), 0 < α → 0 < β → ∀ f : ℝ → 𝕜,
    HolderOnInterval β T f → f 0 = 0 →
    ∃ C ≥ 0, ∀ t ∈ Icc (0 : ℝ) T,
      ‖fractionalValue α f t‖ ≤ C * t ^ (α+β)

def RemainderAssembly : Prop := RemainderDifferentiability → AmplitudeRemainder

def GainAssembly : Prop := FractionalGain → AmplitudeRemainder → AmplitudeGain

end ExpandedFA.PartV.FractionalHolder.Spec
