import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.Algebraic.Defs

/-!
Independent statements of `thm:pi-transcendental`, paper.tex:7784–7820.
Both conclusions are over Q and concern the actual real constants. The square
root is `Real.sqrt`, hence the nonnegative square root. There are no additional
algebraicity, exponential-transcendence, or finiteness hypotheses.
-/

namespace Specs.D07.Appendix.PiTranscendental

def PiIsTranscendental : Prop := Transcendental ℚ Real.pi

def SqrtPiTranscendental : Prop := Transcendental ℚ (Real.sqrt Real.pi)

end Specs.D07.Appendix.PiTranscendental
