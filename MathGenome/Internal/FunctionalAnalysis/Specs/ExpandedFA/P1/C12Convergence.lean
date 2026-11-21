import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators

/-!
Independent specifications for Proposition `fa2:p1:c12:convergence`, paper.tex
2325–2334. The weak topology uses the norm-continuous linear dual, fixed
before changing any topology. The weak-star topology on that dual tests
against the original space. All assertions hold over both ℝ and ℂ, without
completeness or nontriviality assumptions.

Convergence is stated along an arbitrary filter, hence in particular for
every net on a directed index set along its `atTop` filter. There is no
countability or boundedness restriction on the net. Norm convergence uses
the original norm topology, including the operator norm on the dual.
-/

namespace ExpandedFA.P1.C12Convergence.Spec

universe u v w z
open Filter
open scoped Topology
noncomputable section

/-- Evaluation by every member of E′ characterizes σ(E,E′) convergence. -/
def WeakConvergence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (A : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (l : Filter A) (xₐ : A → E) (x : E),
    Tendsto xₐ l
      (@nhds E
        (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) x) ↔
      ∀ f : E →L[𝕜] 𝕜, Tendsto (fun a => f (xₐ a)) l (𝓝 (f x))

/-- Evaluation at every x ∈ E characterizes σ(E′,E) convergence. -/
def WeakStarConvergence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (A : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (l : Filter A) (fₐ : A → (E →L[𝕜] 𝕜)) (f : E →L[𝕜] 𝕜),
    Tendsto fₐ l
      (@nhds (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) f) ↔
      ∀ x : E, Tendsto (fun a => fₐ a x) l (𝓝 (f x))

def NormImpliesWeak : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (A : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (l : Filter A) (xₐ : A → E) (x : E),
    Tendsto xₐ l (𝓝 x) →
      Tendsto xₐ l
        (@nhds E
          (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) x)

def NormImpliesWeakStar : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (A : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (l : Filter A) (fₐ : A → (E →L[𝕜] 𝕜)) (f : E →L[𝕜] 𝕜),
    Tendsto fₐ l (𝓝 f) → Tendsto fₐ l
      (@nhds (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) f)

/-- T is continuous from σ(E,E′) to σ(F,F′). -/
def WeakContinuity : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    @Continuous E F
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      (C12DualPairSpec.DualPairTopologyValue 𝕜 F (F →L[𝕜] 𝕜) (topDualPairing 𝕜 F)) T

/-- The original Banach transpose T′f=f∘T is continuous from σ(F′,F)
to σ(E′,E); both are the specified evaluation pairings. -/
def TransposeWeakStarContinuity : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    @Continuous (F →L[𝕜] 𝕜) (E →L[𝕜] 𝕜)
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 F)
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      (C04Annihilators.Spec.BanachTransposeValue 𝕜 E F T)

end
end ExpandedFA.P1.C12Convergence.Spec
