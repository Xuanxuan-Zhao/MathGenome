import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Complex.Basic

/-! Independent statements of paper.tex, Theorem fa2:p1:c24:schauder (lines 5070–5074).
Compactness and continuity use the original norm topology and induced subtype
topology. Convexity is over the reals, also in the complex case. -/
namespace ExpandedFA.P1.C24Schauder.Spec

universe u

def Schauder : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E), C.Nonempty → IsCompact C → Convex ℝ C →
      ∀ T : C → C, Continuous T → ∃ x : C, T x = x

def SchauderComplex : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    ∀ (C : Set E), C.Nonempty → IsCompact C → Convex ℝ C →
      ∀ T : C → C, Continuous T → ∃ x : C, T x = x

end ExpandedFA.P1.C24Schauder.Spec
