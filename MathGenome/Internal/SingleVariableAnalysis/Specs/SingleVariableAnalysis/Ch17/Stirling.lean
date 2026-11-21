import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.StirlingLogError
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Real.Sqrt

/-! Independent statements for K03.17.stirling, paper.tex:4510–4541.
The exact formula concerns every positive integer. The remainder is a fixed
real sequence, defined from the manuscript's logarithmic sequence, rather than
an assumed error certificate. All asymptotics use natural indices at infinity.
The separate ratio limit and positivity retain the manuscript's nonvanishing
convention for asymptotic equivalence. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.Stirling
open Filter
open scoped Topology

def mainTerm (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n

def remainder (n : ℕ) : ℝ :=
  StirlingLogError.logSequence n - Real.log (Real.sqrt (2 * Real.pi))

def sequenceType : Type := ℕ → ℝ

def normalization : Prop := ∀ c : ℝ,
  Tendsto StirlingLogError.logSequence atTop (𝓝 c) →
    Real.exp c = Real.sqrt (2 * Real.pi)

def logarithmicLimit : Prop :=
  Tendsto StirlingLogError.logSequence atTop (𝓝 (Real.log (Real.sqrt (2 * Real.pi))))

def logarithmicError : Prop :=
  Asymptotics.IsBigO atTop remainder (fun n : ℕ => (n : ℝ)⁻¹)

def positiveMainTerm : Prop := ∀ n : ℕ, 1 ≤ n → 0 < mainTerm n

def exactFormula : Prop := ∀ n : ℕ, 1 ≤ n →
  (n.factorial : ℝ) = mainTerm n * Real.exp (remainder n)

def ratioLimit : Prop :=
  Tendsto (fun n : ℕ => (n.factorial : ℝ) / mainTerm n) atTop (𝓝 1)

def equivalence : Prop :=
  Asymptotics.IsEquivalent atTop (fun n : ℕ => (n.factorial : ℝ)) mainTerm

/-- The ratio equals 1 plus this O(1/n) error. -/
def relativeError : Prop :=
  Asymptotics.IsBigO atTop (fun n : ℕ => (n.factorial : ℝ) / mainTerm n - 1)
    (fun n : ℕ => (n : ℝ)⁻¹)

end Specs.SingleVariableAnalysis.Ch17.Stirling
