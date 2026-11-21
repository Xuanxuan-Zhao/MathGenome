import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions

/-! Full independent obligations for the winding stage of
`fa2:p2:toeplitz` (paper.tex:10763–10785). The later Coburn alternative
and the separate dimensions for arbitrary symbols have their own goal.
Here the dimensions are required only for the integer Fourier symbols.
The Hardy model, nonvanishing loops and winding are the shared upstream objects. -/
noncomputable section
open scoped Real

namespace ExpandedFA.Toeplitz.ScalarIndex.Spec
open ExpandedFA.Toeplitz.Definitions.Spec
open ExpandedFA.Fredholm.DefinitionsSpec

def FredholmSymbols : Prop := ∀ φ : NonvanishingLoop,
  IsFredholmValue (toeplitz (continuousSymbol φ.val))

def ScalarIndex : Prop := ∀ φ : NonvanishingLoop,
  ∃ h : IsFredholmValue (toeplitz (continuousSymbol φ.val)),
    fredholmIndexValue (toeplitz (continuousSymbol φ.val)) h = -winding φ

/-- Includes the identity operator at n=0. -/
def PositiveShift : Prop := ∀ n : ℕ,
  let T := toeplitz (continuousSymbol (fourier (T := 2 * Real.pi) (n : ℤ)))
  ∃ h : IsFredholmValue T,
    Module.finrank ℂ T.ker = 0 ∧ Module.finrank ℂ (H2 ⧸ T.range) = n ∧
      fredholmIndexValue T h = -(n : ℤ)

/-- Includes the identity operator at n=0. -/
def NegativeShift : Prop := ∀ n : ℕ,
  let T := toeplitz (continuousSymbol (fourier (T := 2 * Real.pi) (-(n : ℤ))))
  ∃ h : IsFredholmValue T,
    Module.finrank ℂ T.ker = n ∧ Module.finrank ℂ (H2 ⧸ T.range) = 0 ∧
      fredholmIndexValue T h = (n : ℤ)

/-- Operator-norm continuous homotopies of continuous symbols, all nowhere zero.
There is no differentiability hypothesis on either parameter. -/
def HomotopyIndex : Prop := ∀ (p : unitInterval → C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ)), Continuous p →
  (∀ s t, p s t ≠ 0) →
  ∀ (h₀ : IsFredholmValue (toeplitz (continuousSymbol (p 0))))
    (h₁ : IsFredholmValue (toeplitz (continuousSymbol (p 1)))),
    fredholmIndexValue (toeplitz (continuousSymbol (p 0))) h₀ =
      fredholmIndexValue (toeplitz (continuousSymbol (p 1))) h₁

end ExpandedFA.Toeplitz.ScalarIndex.Spec
