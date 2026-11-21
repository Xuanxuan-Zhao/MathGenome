import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Convexity
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Independent specification of the local Lipschitz and continuity part of
K03.05.convex_onesided, paper.tex:949–953. The real-valued codomain expresses
finiteness. Intervals are order-connected real sets, and openness is an explicit
hypothesis where used. The first statement records the exact exterior-secant
constant; the second supplies exterior points for every compact interior segment,
including a singleton. No continuity or boundedness of the function is assumed.
-/

namespace Specs.SingleVariableAnalysis.Ch05.ConvexLocalLipschitz

open Set
open Specs.SingleVariableAnalysis.Ch05.Convexity

/-- The fixed exterior slopes bound the Lipschitz constant on `[a,b]`.
This estimate itself only requires an interval containing the four points. -/
def exteriorSecantLipschitz : Prop :=
  ∀ (I : Set ℝ), I.OrdConnected → ∀ (f : ℝ → ℝ), convexFunctionOnValue I f →
    ∀ (u a b v : ℝ), u ∈ I → a ∈ I → b ∈ I → v ∈ I →
      u < a → a ≤ b → b < v →
      LipschitzOnWith
        (Real.toNNReal (max (|(f a - f u) / (a - u)|) (|(f v - f b) / (v - b)|)))
        f (Icc a b)

/-- Every closed bounded segment inside an open interval has exterior points in
that interval and the precise Lipschitz bound from the manuscript. -/
def compactInteriorSegmentLipschitz : Prop :=
  ∀ (I : Set ℝ), IsOpen I → I.OrdConnected →
    ∀ (f : ℝ → ℝ), convexFunctionOnValue I f →
      ∀ (a b : ℝ), a ≤ b → a ∈ I → b ∈ I →
        ∃ u ∈ I, ∃ v ∈ I, u < a ∧ b < v ∧
          LipschitzOnWith
            (Real.toNNReal
              (max (|(f a - f u) / (a - u)|) (|(f v - f b) / (v - b)|)))
            f (Icc a b)

/-- Continuity on the whole open interval, without nonemptiness assumptions. -/
def continuousOnOpenInterval : Prop :=
  ∀ (I : Set ℝ), IsOpen I → I.OrdConnected →
    ∀ (f : ℝ → ℝ), convexFunctionOnValue I f → ContinuousOn f I

end Specs.SingleVariableAnalysis.Ch05.ConvexLocalLipschitz
