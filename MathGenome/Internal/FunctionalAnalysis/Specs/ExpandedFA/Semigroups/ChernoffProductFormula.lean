import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Chernoff's product formula, paper.tex, fa2:p3:product-formula.
Only contractivity, the value at zero, and right consistency on a graph core
are required of the step family. In particular the family need not be
continuous in operator norm, or differentiable on the full generator domain.
The generator below has its canonical exact derivative domain.
-/
noncomputable section
open Filter Topology Set
open scoped NNReal

namespace ExpandedFA.Semigroups.ChernoffSpec
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Right consistency is imposed only on the specified core. -/
def CoreConsistency (T : C0Semigroup 𝕜 X) (F : ℝ≥0 → X →L[𝕜] X)
    (D : Submodule 𝕜 X) (hD : D ≤ (C0SemigroupSpec.generatorValue T).domain) : Prop :=
  ∀ x : D, Tendsto (fun h : ℝ =>
    (algebraMap ℝ 𝕜 h)⁻¹ • (F h.toNNReal (x : X) - (x : X)))
    (𝓝[>] 0) (𝓝 (C0SemigroupSpec.generatorValue T ⟨x, hD x.2⟩))

/-- Powers use composition of bounded linear endomorphisms. The n=0 term is
irrelevant to the limit; time zero is included in every uniform interval. -/
def ProductConvergence (T : C0Semigroup 𝕜 X) (F : ℝ≥0 → X →L[𝕜] X) : Prop :=
  ∀ (x : X) (b : ℝ), 0 ≤ b → TendstoUniformlyOn
    (fun n : ℕ => fun t : ℝ => (F (t / n).toNNReal ^ n) x)
    (fun t : ℝ => T.operators t.toNNReal x) atTop (Icc 0 b)

def ChernoffFormula : Prop :=
  ∀ (T : C0Semigroup 𝕜 X) (F : ℝ≥0 → X →L[𝕜] X)
    (D : Submodule 𝕜 X),
    (∀ t, ‖T.operators t‖ ≤ 1) → (∀ h, ‖F h‖ ≤ 1) →
    F 0 = ContinuousLinearMap.id 𝕜 X →
    ∀ hcore : Unbounded.OperatorDomainsSpec.coreValue (C0SemigroupSpec.generatorValue T) D,
    CoreConsistency T F D hcore.1 → ProductConvergence T F

def ChernoffFormulaExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  ChernoffFormula (𝕜 := 𝕜) (X := X)
end ExpandedFA.Semigroups.ChernoffSpec
