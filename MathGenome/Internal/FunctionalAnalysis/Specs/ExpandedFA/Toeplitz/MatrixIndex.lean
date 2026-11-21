import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.MatrixLoopHomotopy
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.MeasurableSymbolCounterexample
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions

/-! The matrix Toeplitz theorem, in every positive finite dimension. Matrix
loops use the multiplicative circle; entries are transported to the canonical
additive circle by its positively oriented homeomorphism. -/
noncomputable section
namespace ExpandedFA.Toeplitz.MatrixIndex.Spec
open ExpandedFA.Toeplitz.Definitions.Spec
open ExpandedFA.Toeplitz.MatrixLoops
open ExpandedFA.Fredholm.DefinitionsSpec

/-- Entry functions of a continuous invertible loop, on the shared torus. -/
def entries (n : ℕ) (Φ : C(_root_.Circle, MatrixGroup n)) :
    Matrix (Fin (n+1)) (Fin (n+1)) C(Definitions.Spec.Circle, ℂ) :=
  fun i j => ⟨fun t => (Φ (AddCircle.homeomorphCircle' t)).val i j,
    (Units.continuous_val.comp (Φ.continuous.comp
      AddCircle.homeomorphCircle'.continuous)).matrix_elem i j⟩

def operator (n : ℕ) (Φ : C(_root_.Circle, MatrixGroup n)) :=
  matrixToeplitz (continuousMatrixSymbol (entries n Φ))

/-- The full Fredholm and minus determinant winding assertion. The parameter
`n` denotes dimension `n+1`, including dimension one. -/
def MatrixIndex : Prop := ∀ (n : ℕ) (Φ : C(_root_.Circle, MatrixGroup n)),
  ∃ h : IsFredholmValue (operator n Φ),
    fredholmIndexValue (operator n Φ) h =
      -MatrixLoops.winding ((determinant n).comp Φ)

/-- The explicit singular inner symbol, including its actual infinite cokernel. -/
def DiscontinuousCounterexample : Prop :=
  MeasurableSymbolCounterexample.Spec.Counterexample

end ExpandedFA.Toeplitz.MatrixIndex.Spec
