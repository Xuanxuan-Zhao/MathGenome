import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24CompactMap
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic

/-! Independent statements of paper.tex:5657–5670. Time has the induced
topology and metric on the closed interval [0,1]. Relative compactness is
always in the original Banach space. -/

namespace ExpandedFA.P1.LeraySchauder.Spec

universe u

def CompactImageFixedPoint : Prop := C24CompactMap.Spec.BanachCompactMap.{u}

def CompactHomotopyContinuation : Prop :=
  ∀ (𝕜 : Type) (E : Type u) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E]
    (F : E × Set.Icc (0 : ℝ) 1 → E), Continuous F →
    (∀ B : Set (E × Set.Icc (0 : ℝ) 1), Bornology.IsBounded B →
      IsCompact (closure (F '' B))) →
    (∀ x, F (x, ⟨0, by constructor <;> norm_num⟩) = 0) →
    (∃ R : ℝ, 0 < R ∧ ∀ x t, F (x, t) = x → ‖x‖ < R) →
    ∃ x, F (x, ⟨1, by constructor <;> norm_num⟩) = x

def BoundedSolutionSetFixedPoint : Prop :=
  ∀ (𝕜 : Type) (E : Type u) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ (T : E → E), Continuous T →
    (∀ B : Set E, Bornology.IsBounded B → IsCompact (closure (T '' B))) →
    Bornology.IsBounded {x : E | ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
      x = t • T x} → ∃ x, T x = x

end ExpandedFA.P1.LeraySchauder.Spec
