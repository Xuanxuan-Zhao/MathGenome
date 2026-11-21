import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import Mathlib.Topology.Metrizable.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Independent statements for paper.tex, fa2:p1:c13:whole-dual (2663–2681).
The continuous linear dual is formed using the original norm topology on E.
Its entire carrier, with σ(E′,E), is used; no bounded subset is substituted.
First countability at zero means countable generation of its neighborhood filter.
-/
namespace ExpandedFA.P1.WholeDualNotFirstCountable.Spec

universe u v
open scoped Topology

noncomputable def NotFirstCountableAtZero : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (_hInfinite : ¬ FiniteDimensional 𝕜 E),
    ¬ (@nhds (E →L[𝕜] 𝕜)
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) 0).IsCountablyGenerated

noncomputable def NotMetrizable : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (_hInfinite : ¬ FiniteDimensional 𝕜 E),
    ¬ @TopologicalSpace.MetrizableSpace (E →L[𝕜] 𝕜)
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)

end ExpandedFA.P1.WholeDualNotFirstCountable.Spec
