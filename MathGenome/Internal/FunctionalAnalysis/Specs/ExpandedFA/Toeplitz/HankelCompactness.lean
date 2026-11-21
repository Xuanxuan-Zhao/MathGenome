import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions

/-! Compactness for continuous circle symbols, on the canonical Hardy space.
The matrix product is ordinary row-by-column multiplication in its original order.
There is no assertion of compactness for arbitrary measurable symbols. -/
noncomputable section
namespace ExpandedFA.Toeplitz.HankelCompactness.Spec
open ExpandedFA.Toeplitz.Definitions.Spec

def ToeplitzNorm : Prop := ∀ φ : ScalarSymbol, ‖toeplitz φ‖ ≤ ‖φ‖

def ContinuousToeplitzNorm : Prop := ∀ φ : C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ),
  ‖toeplitz (continuousSymbol φ)‖ ≤ ‖φ‖

def HankelCompact : Prop := ∀ φ : C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ),
  IsCompactOperator (hankel (continuousSymbol φ))

def ProductDefectFormula : Prop := ∀ φ ψ : C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ),
  (toeplitz (continuousSymbol φ)).comp (toeplitz (continuousSymbol ψ)) -
    toeplitz (continuousSymbol (φ * ψ)) =
  -(boundaryAnalysis.comp ((multiplication (continuousSymbol φ)).comp
    (hankel (continuousSymbol ψ))))

def ProductDefectCompact : Prop := ∀ φ ψ : C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ),
  IsCompactOperator ((toeplitz (continuousSymbol φ)).comp
    (toeplitz (continuousSymbol ψ)) - toeplitz (continuousSymbol (φ * ψ)))

/-- The norm on each matrix fiber is its operator norm on Euclidean space,
not the maximum or sum of its entry norms. -/
abbrev MatrixFiber (d : ℕ) := PiLp 2 (fun _ : Fin d => ℂ)

def pointwiseMatrix {d : ℕ} (Φ : Matrix (Fin d) (Fin d)
    C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ))
    (t : ExpandedFA.Toeplitz.Definitions.Spec.Circle) : MatrixFiber d →L[ℂ] MatrixFiber d :=
  operatorMatrix d (fun i j => ContinuousLinearMap.mul ℂ ℂ (Φ i j t))

def matrixSymbolNorm {d : ℕ} (Φ : Matrix (Fin d) (Fin d)
    C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ)) : ℝ :=
  ⨆ t, ‖pointwiseMatrix Φ t‖

def MatrixToeplitzNorm : Prop := ∀ (d : ℕ)
    (Φ : Matrix (Fin d) (Fin d) C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ)),
  ‖matrixToeplitz (continuousMatrixSymbol Φ)‖ ≤ matrixSymbolNorm Φ

def MatrixHankelCompact : Prop := ∀ (d : ℕ)
    (Φ : Matrix (Fin d) (Fin d) C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ)),
  IsCompactOperator (matrixHankel (continuousMatrixSymbol Φ))

def MatrixProductDefectCompact : Prop := ∀ (d : ℕ)
    (Φ Ψ : Matrix (Fin d) (Fin d) C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ)),
  IsCompactOperator ((matrixToeplitz (continuousMatrixSymbol Φ)).comp
    (matrixToeplitz (continuousMatrixSymbol Ψ)) -
      matrixToeplitz (continuousMatrixSymbol (Φ * Ψ)))

end ExpandedFA.Toeplitz.HankelCompactness.Spec
