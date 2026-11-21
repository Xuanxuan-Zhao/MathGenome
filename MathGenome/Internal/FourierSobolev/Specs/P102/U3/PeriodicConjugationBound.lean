import MathGenome.Internal.FourierSobolev.Specs.P102.U3.PeriodicConjugationData
import MathGenome.Internal.FourierSobolev.Specs.P102.U2.CZLp

/-! Independent full statement for the cancelled-integral Lp bound in
paper.tex:1199–1200. The shared physical formula is used without assuming its
Fourier-multiplier identification. The exponent interface is already supplied
by the bound child's real-line Hilbert prerequisite, not by the kernel child.
The parent imports this module and reuses `CancelledBound` without redefining it.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace P102.Periodic.Conjugation
open P102.Periodic.Expected

/-- A finite constant uniform over all polynomial coefficient vectors. -/
def CancelledBound (T : ℝ) [Fact (0 < T)] (p : P102.U2.CZLpData.Exponent) : Prop :=
  ∃ C : ℝ≥0, ∀ c : ℤ →₀ ℂ,
    eLpNorm (cancelledValue T (synthesis T c)) p.val (haar T) ≤
      (C : ℝ≥0∞) * eLpNorm (synthesis T c) p.val (haar T)

namespace Expected

def CancelledBoundStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (p : P102.U2.CZLpData.Exponent), CancelledBound T p

end Expected
end P102.Periodic.Conjugation
