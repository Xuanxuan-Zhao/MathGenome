import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ExpConstruction
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.SinCos

/-!
Independent specification for K03.07.euler, paper.tex:1793–1809.
E, S and C are the upstream factorial-series functions. The parameter t is
real in both the imaginary-input identities and the derivative. Conjugation
applies to every complex input, without any domain restriction.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.Euler

open Ch07.ExpConstruction Ch07.SinCos

def imaginaryInput : Prop := ∀ t : ℝ,
  seriesExpValue (Complex.I * (t : ℂ)) =
    (realSeriesCosValue t : ℂ) + Complex.I * (realSeriesSinValue t : ℂ)

def imaginaryModulus : Prop := ∀ t : ℝ,
  ‖seriesExpValue (Complex.I * (t : ℂ))‖ = 1

def conjugation : Prop := ∀ z : ℂ,
  starRingEnd ℂ (seriesExpValue z) = seriesExpValue (starRingEnd ℂ z)

def realParameterDerivative : Prop := ∀ z : ℂ, ∀ t : ℝ,
  HasDerivAt (fun s : ℝ => seriesExpValue ((s : ℂ) * z))
    (z * seriesExpValue ((t : ℂ) * z)) t

end Specs.SingleVariableAnalysis.Ch07.Euler
