import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.AbelInversion
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FirstKindSmooth

/-! General-amplitude clause of `fa2:p5:abel` in the adopted paper.
The unknown is a continuous scalar function on the original closed interval.
All differentiability is in real parameters, for either real or complex scalars.
-/
noncomputable section
open Set MeasureTheory
namespace ExpandedFA.PartV.AbelAmplitude
open FractionalIntegrals.Spec

/-- The unnormalized singular integral with its actual two-variable amplitude. -/
def amplitudeValue {𝕜 : Type} [RCLike 𝕜] (α : ℝ)
    (k : ℝ × ℝ → 𝕜) (u : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  ∫ s in Ioc 0 t, (t-s) ^ (α-1) • (k (t,s) * u s)

/-- The equation is imposed also at the initial point. Clamping only supplies
representatives outside the interval, where values are never used. -/
def AmplitudeEquation {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (α : ℝ) (k : ℝ × ℝ → 𝕜) (g u : C(Icc (0 : ℝ) T, 𝕜)) : Prop :=
  ∀ t : Icc (0 : ℝ) T,
    amplitudeValue α k (continuousExtension hT u) t = g t

/-- Integrable Beta weight, with the source normalization kept explicit. -/
def betaWeight (α r : ℝ) : ℝ := (1-r) ^ (-α) * r ^ (α-1)

/-- The kernel after applying the complementary fractional integral.
This is defined by the source's actual rescaling, with no invariance assumption. -/
def transformedKernel {𝕜 : Type} [RCLike 𝕜] (α : ℝ)
    (k : ℝ × ℝ → 𝕜) (p : ℝ × ℝ) : 𝕜 :=
  (Real.Gamma (1-α))⁻¹ •
    ∫ r in Ioc (0 : ℝ) 1, betaWeight α r • k (p.2+(p.1-p.2)*r,p.2)

namespace Spec

/-- Full positive-length theorem for every C¹ amplitude on an open
neighborhood of the closed triangle and every native C¹ compatible datum. -/
def C1Solvability : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hsub : volterraTriangle 0 T ⊆ U)
    (k : ℝ × ℝ → 𝕜) (hk : ContDiffOn ℝ 1 k U)
    (hne : ∀ t : Icc (0 : ℝ) T, k (t,t) ≠ 0)
    (g : C(Icc (0 : ℝ) T, 𝕜)),
    ContDiffOn ℝ 1 (continuousExtension hT.le g) (Icc 0 T) →
    g ⟨0, le_rfl, hT.le⟩ = 0 →
    ∃! u, AmplitudeEquation hT.le α k g u

/-- On a singleton every continuous function solves exactly when the datum
vanishes. There are at least two solutions whenever one exists. -/
def SingletonClassification : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (α : ℝ) (k : ℝ × ℝ → 𝕜) (g : C(Icc (0 : ℝ) 0, 𝕜)),
    (∀ u, AmplitudeEquation (le_refl 0) α k g u ↔ g ⟨0, by simp⟩ = 0) ∧
    ((∃ u, AmplitudeEquation (le_refl 0) α k g u) ↔ g ⟨0, by simp⟩ = 0) ∧
    (g ⟨0, by simp⟩ = 0 → ¬ ∃! u, AmplitudeEquation (le_refl 0) α k g u)

/-- Analytic regularity of the source's transformed kernel, obtained from
native ambient C¹ regularity, including its exact diagonal coefficient. -/
def KernelRegularity : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (α T : ℝ), 0 < α → α < 1 → 0 ≤ T →
    ∀ (U : Set (ℝ × ℝ)), IsOpen U → volterraTriangle 0 T ⊆ U →
    ∀ (k : ℝ × ℝ → 𝕜), ContDiffOn ℝ 1 k U →
    (∃ W : Set (ℝ × ℝ), IsOpen W ∧ volterraTriangle 0 T ⊆ W ∧
      ContDiffOn ℝ 1 (transformedKernel α k) W) ∧
    (∀ t : Icc (0 : ℝ) T,
      transformedKernel α k (t,t) = Real.Gamma α • k (t,t))

/-- Absolute existence, continuity of the original singular integral, and the
complementary fractional-integral identity. These are conclusions for every
continuous amplitude and input, rather than certificates assumed by solvability. -/
def CompositionIdentity : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (α T : ℝ), 0 < α → α < 1 → ∀ (hT : 0 ≤ T)
    (k : ℝ × ℝ → 𝕜), ContinuousOn k (volterraTriangle 0 T) →
    ∀ u : C(Icc (0 : ℝ) T, 𝕜),
    ContinuousOn (amplitudeValue α k (continuousExtension hT u)) (Icc 0 T) ∧
    (∀ t ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun s => (t-s) ^ (α-1) •
        (k (t,s) * continuousExtension hT u s)) (Ioc 0 t)) ∧
    (∀ t ∈ Icc (0 : ℝ) T,
      fractionalValue (1-α) (amplitudeValue α k (continuousExtension hT u)) t =
        ∫ s in Ioc 0 t, transformedKernel α k (t,s) * continuousExtension hT u s)

/-- Assembly interface: the analytic bridge implies the unchanged original theorem.
This is a helper obligation; C1Solvability itself has no certificate premise. -/
def SolvabilityFromComposition : Prop := CompositionIdentity → C1Solvability

end Spec
end ExpandedFA.PartV.AbelAmplitude
