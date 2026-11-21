import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Unconditional

/-! Theorem `fa2:p1:no-czero-wuc`, paper.tex 4233–4239.
The scalar field, the supremum norm on c₀, and the finite-subset net of
norm sums are the original upstream objects. An isomorphic subspace means
a linear subspace with its inherited norm and a continuous linear equivalence.
No complementedness, separability, or nonzero-space hypothesis is imposed. -/
noncomputable section
universe u v
namespace ExpandedFA.P1.NoCzeroWuc.Spec

open C01SequenceSpaces C15Unconditional.Spec

def ContainsC0 (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∃ S : Submodule 𝕜 E, Nonempty (SequenceC0 𝕜 ≃L[𝕜] S)

/-- Absolute scalar summability is required for every continuous scalar-linear
functional; the real norm is absolute value or complex modulus. -/
def WeaklyUnconditionallyCauchy {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : ℕ → E) : Prop :=
  ∀ f : E →L[𝕜] 𝕜, Summable (fun n => ‖f (x n)‖)

def NoC0IffWucUnconditional : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    ¬ContainsC0 𝕜 E ↔ ∀ x : ℕ → E,
      WeaklyUnconditionallyCauchy (𝕜 := 𝕜) x → UnconditionallyConvergentValue x

end ExpandedFA.P1.NoCzeroWuc.Spec
