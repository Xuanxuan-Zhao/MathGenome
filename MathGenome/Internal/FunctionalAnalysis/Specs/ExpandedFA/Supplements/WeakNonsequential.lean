import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Sequences

/-! The set in `fa2:p1:weak-nonsequential` (paper.tex 6028–6045).
The index zero is included only to describe a flag starting at the zero space;
the union itself uses exactly the positive indices from the source. All norms
and all continuous linear functionals refer to the original normed space.
-/
namespace ExpandedFA.Supplements.WeakNonsequential

universe u v
open scoped Topology
noncomputable section

variable (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

abbrev weakTopology : TopologicalSpace E :=
  P1.C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)

/-- A nested flag with the stated dimensions, including its harmless zero term. -/
def SphereChain (V : ℕ → Submodule 𝕜 E) : Prop :=
  Monotone V ∧ ∀ n, FiniteDimensional 𝕜 (V n) ∧ Module.finrank 𝕜 (V n) = n

/-- The actual union of the radius-n spheres inside E_n, for n ≥ 1. -/
def sphereUnion (V : ℕ → Submodule 𝕜 E) : Set E :=
  {x | ∃ n : ℕ, 0 < n ∧ x ∈ V n ∧ ‖x‖ = (n : ℝ)}

namespace Spec

def ChainExistence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ¬ FiniteDimensional 𝕜 E → ∃ V, SphereChain 𝕜 E V

def SphereUnionProperties : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (V : ℕ → Submodule 𝕜 E),
    SphereChain 𝕜 E V →
      @IsSeqClosed E (weakTopology 𝕜 E) (sphereUnion 𝕜 E V) ∧
      (0 : E) ∈ @closure E (weakTopology 𝕜 E) (sphereUnion 𝕜 E V) ∧
      (0 : E) ∉ sphereUnion 𝕜 E V ∧
      ¬ @IsClosed E (weakTopology 𝕜 E) (sphereUnion 𝕜 E V)

def MainResult : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ¬ FiniteDimensional 𝕜 E →
    ∃ V : ℕ → Submodule 𝕜 E, SphereChain 𝕜 E V ∧
      @IsSeqClosed E (weakTopology 𝕜 E) (sphereUnion 𝕜 E V) ∧
      (0 : E) ∈ @closure E (weakTopology 𝕜 E) (sphereUnion 𝕜 E V) ∧
      (0 : E) ∉ sphereUnion 𝕜 E V ∧
      ¬ @IsClosed E (weakTopology 𝕜 E) (sphereUnion 𝕜 E V)

end Spec
end
end ExpandedFA.Supplements.WeakNonsequential
