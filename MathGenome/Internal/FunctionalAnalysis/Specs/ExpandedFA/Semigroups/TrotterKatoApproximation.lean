import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.LaplaceResolvent
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Strong resolvent approximation, paper.tex 14878–14926.
Generators are the canonical exact-domain derivative generators of the supplied
C₀ semigroups. Thus neither bounded generators nor common domains are assumed.
The single scalar field is any real or complex scalar field, and X is Banach.
-/
noncomputable section
open Filter Topology Set

namespace ExpandedFA.Semigroups.TrotterKatoSpec
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

def StrongResolventConvergence (S : ℕ → C0Semigroup 𝕜 X) (T : C0Semigroup 𝕜 X)
    (r : ℝ) : Prop :=
  ∀ x : X, Tendsto (fun n => Unbounded.OperatorDomainsSpec.resolventValue
    (algebraMap ℝ 𝕜 r) (C0SemigroupSpec.generatorValue (S n)) x) atTop
    (𝓝 (Unbounded.OperatorDomainsSpec.resolventValue
      (algebraMap ℝ 𝕜 r) (C0SemigroupSpec.generatorValue T) x))

def LocallyUniformStrongConvergence (S : ℕ → C0Semigroup 𝕜 X)
    (T : C0Semigroup 𝕜 X) : Prop :=
  ∀ (x : X) (b : ℝ), 0 ≤ b → TendstoUniformlyOn
    (fun n (t : ℝ) => (S n).operators t.toNNReal x)
    (fun t : ℝ => T.operators t.toNNReal x) atTop (Icc 0 b)

def CommonGrowthEquivalence : Prop :=
  ∀ (S : ℕ → C0Semigroup 𝕜 X) (T : C0Semigroup 𝕜 X) (M ω : ℝ),
    C0SemigroupSpec.exponentialBoundValue T M ω →
    C0SemigroupSpec.commonExponentialBoundValue S M ω →
    ∀ r : ℝ, ω < r →
      (StrongResolventConvergence S T r ↔ LocallyUniformStrongConvergence S T)

def OneEveryResolvent : Prop :=
  ∀ (S : ℕ → C0Semigroup 𝕜 X) (T : C0Semigroup 𝕜 X) (M ω : ℝ),
    C0SemigroupSpec.exponentialBoundValue T M ω →
    C0SemigroupSpec.commonExponentialBoundValue S M ω →
    ((∃ r : ℝ, ω < r ∧ StrongResolventConvergence S T r) ↔
      LocallyUniformStrongConvergence S T) ∧
    (LocallyUniformStrongConvergence S T ↔
      ∀ r : ℝ, ω < r → StrongResolventConvergence S T r)

def ContractionEquivalence : Prop :=
  ∀ (S : ℕ → C0Semigroup 𝕜 X) (T : C0Semigroup 𝕜 X),
    (∀ t, ‖T.operators t‖ ≤ 1) → (∀ n t, ‖(S n).operators t‖ ≤ 1) →
    ((∃ r : ℝ, 0 < r ∧ StrongResolventConvergence S T r) ↔
      LocallyUniformStrongConvergence S T) ∧
    (LocallyUniformStrongConvergence S T ↔
      ∀ r : ℝ, 0 < r → StrongResolventConvergence S T r)

def CommonGrowthEquivalenceExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  CommonGrowthEquivalence (𝕜 := 𝕜) (X := X)
def OneEveryResolventExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  OneEveryResolvent (𝕜 := 𝕜) (X := X)
def ContractionEquivalenceExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  ContractionEquivalence (𝕜 := 𝕜) (X := X)
end ExpandedFA.Semigroups.TrotterKatoSpec
