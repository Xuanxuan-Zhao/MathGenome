import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.ScalarIndex
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.HankelCompactness

/-! Full scalar Toeplitz theorem, paper.tex:10763–10800.
The kernels and cokernels are those of the actual Hardy compression.
Dimensions are natural numbers, with integer maxima converted by `toNat`. -/
noncomputable section
namespace ExpandedFA.Toeplitz.ScalarNullityDeficiency.Spec
open ExpandedFA.Toeplitz.Definitions.Spec
open ExpandedFA.Fredholm.DefinitionsSpec

/-- Coburn's alternative for every nowhere zero continuous scalar symbol. -/
def CoburnAlternative : Prop := ∀ φ : NonvanishingLoop,
  (toeplitz (continuousSymbol φ.val)).ker = ⊥ ∨
    (toeplitz (continuousSymbol φ.val)).adjoint.ker = ⊥

def NullityDeficiency : Prop := ∀ φ : NonvanishingLoop,
  Module.finrank ℂ (toeplitz (continuousSymbol φ.val)).ker =
      (max 0 (-winding φ)).toNat ∧
    Module.finrank ℂ (H2 ⧸ (toeplitz (continuousSymbol φ.val)).range) =
      (max 0 (winding φ)).toNat

/-- Compactness holds for all continuous symbols, including those with zeros. -/
def ScalarToeplitzTheorem : Prop :=
  (∀ φ : C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ), IsCompactOperator (hankel (continuousSymbol φ))) ∧
  ∀ φ : NonvanishingLoop,
    ∃ h : IsFredholmValue (toeplitz (continuousSymbol φ.val)),
      fredholmIndexValue (toeplitz (continuousSymbol φ.val)) h = -winding φ ∧
      Module.finrank ℂ (toeplitz (continuousSymbol φ.val)).ker =
        (max 0 (-winding φ)).toNat ∧
      Module.finrank ℂ (H2 ⧸ (toeplitz (continuousSymbol φ.val)).range) =
        (max 0 (winding φ)).toNat

end ExpandedFA.Toeplitz.ScalarNullityDeficiency.Spec
