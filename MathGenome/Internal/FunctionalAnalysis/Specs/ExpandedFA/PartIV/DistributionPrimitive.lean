import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The real line is represented by `ℝ` itself. These are the same native LF
compact test functions and scalar-linear continuous duals used upstream,
here on the paper's literal domain `ℝ`. `OrdConnected` includes every bounded
or unbounded interval. No endpoint condition is imposed. -/
open Set TopologicalSpace MeasureTheory
open scoped Distributions

namespace ExpandedFA.PartIV.DistributionPrimitive

abbrev LineTests (𝕜 : Type) [RCLike 𝕜] (Ω : Opens ℝ) := TestFunction Ω 𝕜 ⊤
abbrev LineDistribution (𝕜 : Type) [RCLike 𝕜] (Ω : Opens ℝ) :=
  LineTests 𝕜 Ω →L[𝕜] 𝕜

/-- The scalar-linear transpose derivative, with its distributional minus sign. -/
noncomputable def lineDerivative {𝕜 : Type} [RCLike 𝕜] {Ω : Opens ℝ}
    (u : LineDistribution 𝕜 Ω) : LineDistribution 𝕜 Ω :=
  -u.comp (TestFunction.lineDerivCLM 𝕜 (1 : ℝ))

/-- Equality with the ordinary constant distribution, given by its integral
pairing rather than an unspecified element of the kernel. -/
def IsConstant {𝕜 : Type} [RCLike 𝕜] {Ω : Opens ℝ}
    (u : LineDistribution 𝕜 Ω) : Prop :=
  ∃ c : 𝕜, ∀ φ : LineTests 𝕜 Ω, u φ = c * ∫ x : ℝ, φ x

end ExpandedFA.PartIV.DistributionPrimitive

namespace Specs.ExpandedFA.PartIV.DistributionPrimitive
open _root_.ExpandedFA.PartIV.DistributionPrimitive

def intervalExistenceType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens ℝ),
  (Ω : Set ℝ).Nonempty → OrdConnected (Ω : Set ℝ) →
  ∀ u : LineDistribution 𝕜 Ω, ∃ v : LineDistribution 𝕜 Ω, lineDerivative v = u

def kernelType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens ℝ),
  (Ω : Set ℝ).Nonempty → OrdConnected (Ω : Set ℝ) →
  ∀ u : LineDistribution 𝕜 Ω, lineDerivative u = 0 ↔ IsConstant u

def uniquenessType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens ℝ),
  (Ω : Set ℝ).Nonempty → OrdConnected (Ω : Set ℝ) →
  ∀ u v w : LineDistribution 𝕜 Ω,
    lineDerivative v = u → lineDerivative w = u → IsConstant (v - w)

def lineExistenceType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : LineDistribution 𝕜 (⊤ : Opens ℝ)),
  ∃ v : LineDistribution 𝕜 (⊤ : Opens ℝ), lineDerivative v = u

end Specs.ExpandedFA.PartIV.DistributionPrimitive
