import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.CompactDefectStabilization
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions

/-! Spectral stage of Riesz--Schauder, paper.tex:10328–10383.
Compactness and bounded inverses are taken in the actual normed space.
No completeness or nontriviality assumption is imposed. Statements over
RCLike fields in particular include the required complex case. -/
namespace ExpandedFA.Fredholm.CompactNonzeroSpectrumSpec
open Filter
open scoped Topology
universe u v

variable {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕂 E]

/-- The full generalized eigenspace is one finite-dimensional power kernel.
The explicit union avoids confusing geometric with algebraic multiplicity. -/
def GeneralizedConclusion (K : E →L[𝕂] E) (μ : 𝕂) : Prop :=
  let A : E →ₗ[𝕂] E := μ • LinearMap.id - K.toLinearMap
  ∃ p : ℕ, 1 ≤ p ∧ FiniteDimensional 𝕂 (LinearMap.ker (A ^ p)) ∧
    (∀ m : ℕ, p ≤ m → LinearMap.ker (A ^ m) = LinearMap.ker (A ^ p)) ∧
    {x : E | ∃ m : ℕ, 1 ≤ m ∧ x ∈ LinearMap.ker (A ^ m)} =
      (LinearMap.ker (A ^ p) : Set E)

def NonzeroSpectrumEigenvalue : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    ∀ μ : 𝕂, μ ≠ 0 →
      (μ ∈ spectrum 𝕂 K ↔ ∃ x : E, x ≠ 0 ∧ K x = μ • x)

def GeneralizedEigenspaceStabilizes : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    ∀ μ : 𝕂, μ ≠ 0 → GeneralizedConclusion K μ

def FiniteAwayFromZero : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    ∀ ε : ℝ, 0 < ε → {μ : 𝕂 | μ ∈ spectrum 𝕂 K ∧ ε ≤ ‖μ‖}.Finite

def FiniteEigenvaluesAwayFromZero : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    ∀ ε : ℝ, 0 < ε →
      {μ : 𝕂 | (∃ x : E, x ≠ 0 ∧ K x = μ • x) ∧ ε ≤ ‖μ‖}.Finite

def AccumulationOnlyZero : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    ∀ μ : 𝕂, AccPt μ (𝓟 (spectrum 𝕂 K)) → μ = 0

/-- Complete conclusion, including bounded-operator spectrum, algebraic
multiplicity, finiteness outside every disk, and the accumulation assertion. -/
def SpectralConclusion (K : E →L[𝕂] E) : Prop :=
  (∀ μ : 𝕂, μ ≠ 0 →
    (μ ∈ spectrum 𝕂 K ↔ ∃ x : E, x ≠ 0 ∧ K x = μ • x)) ∧
  (∀ μ : 𝕂, μ ≠ 0 → GeneralizedConclusion K μ) ∧
  (∀ ε : ℝ, 0 < ε → {μ : 𝕂 | μ ∈ spectrum 𝕂 K ∧ ε ≤ ‖μ‖}.Finite) ∧
  (∀ ε : ℝ, 0 < ε →
    {μ : 𝕂 | (∃ x : E, x ≠ 0 ∧ K x = μ • x) ∧ ε ≤ ‖μ‖}.Finite) ∧
  (∀ μ : 𝕂, AccPt μ (𝓟 (spectrum 𝕂 K)) → μ = 0)

def BoundedCompactSpectralTheorem : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap → SpectralConclusion K

/-- Compact algebraic linear maps are automatically bounded, so the
source's compactness hypothesis needs no separate continuity assumption. -/
def LinearCompactSpectralTheorem : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →ₗ[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K →
    ∃ Kb : E →L[𝕂] E, Kb.toLinearMap = K ∧ SpectralConclusion Kb

end ExpandedFA.Fredholm.CompactNonzeroSpectrumSpec
