import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Topology.Sequences

/-! Independent statements of paper.tex:2010–2015. Bilinearity is over the
original real or complex scalar field. Separate continuity imposes no
operator-space topology and no local convexity. The TVSs are Hausdorff, as
specified in the chapter's conventions. -/

open Filter TopologicalSpace
open scoped Topology

namespace ExpandedFA.P1.SeparateBilinearSpec

/-- Every convergent sequence of pairs has the expected image limit. -/
def SequentialJointContinuity : Prop :=
  ∀ {𝕜 E F G : Type*} [RCLike 𝕜]
    [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
    [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [ContinuousSMul 𝕜 G]
    [T2Space E] [T2Space F] [T2Space G],
    FSpace 𝕜 E → ∀ B : E →ₗ[𝕜] F →ₗ[𝕜] G,
      (∀ y, Continuous (fun x => B x y)) →
      (∀ x, Continuous (B x)) →
      SeqContinuous (fun p : E × F => B p.1 p.2)

/-- Metrizability of the second factor upgrades sequential continuity to
continuity for the product of the given topologies. -/
def JointContinuity : Prop :=
  ∀ {𝕜 E F G : Type*} [RCLike 𝕜]
    [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
    [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [ContinuousSMul 𝕜 G]
    [T2Space E] [T2Space F] [T2Space G] [MetrizableSpace F],
    FSpace 𝕜 E → ∀ B : E →ₗ[𝕜] F →ₗ[𝕜] G,
      (∀ y, Continuous (fun x => B x y)) →
      (∀ x, Continuous (B x)) →
      Continuous (fun p : E × F => B p.1 p.2)

end ExpandedFA.P1.SeparateBilinearSpec
