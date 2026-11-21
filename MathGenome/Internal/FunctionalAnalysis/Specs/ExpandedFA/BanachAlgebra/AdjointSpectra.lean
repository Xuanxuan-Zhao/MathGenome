import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.ShiftSpectra
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint

/-! Independent statements for `fa2:p2:shifts`, paper.tex 10006–10040.
The shift clauses use the shared literal shifts on the canonical scalar ℓᵖ,
for every finite extended-real p ≥ 1 (including p = 1). The transpose is
precomposition on the continuous scalar-linear dual. The Hilbert adjoint
uses the conjugate-first inner product. Complex conjugation below is the
image of the spectrum, not its topological closure. Zero spaces are included.
-/
namespace ExpandedFA.BanachAlgebra.AdjointSpectra.Spec

universe u

/-- Forward spectrum: the closed unit disk, for every 1 ≤ p < ∞. -/
def ForwardSpectrum : Prop := ShiftSpectra.Spec.ForwardSpectrum

def ForwardPointSpectrum : Prop := ShiftSpectra.Spec.ForwardPointSpectrum

def ForwardApproximateSpectrum : Prop := ShiftSpectra.Spec.ForwardApproximateSpectrum

def BackwardSpectrum : Prop := ShiftSpectra.Spec.BackwardSpectrum

def BackwardPointSpectrum : Prop := ShiftSpectra.Spec.BackwardPointSpectrum

/-- Invertibility is reflected as well as preserved by the Banach transpose. -/
def TransposeInvertibility : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X),
    IsUnit (P1.C04Annihilators.Spec.BanachTransposeValue ℂ X X T) ↔ IsUnit T

def TransposeSpectrum : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X),
    spectrum ℂ (P1.C04Annihilators.Spec.BanachTransposeValue ℂ X X T) = spectrum ℂ T

/-- The two adjoints are different: the Hilbert identity conjugates scalars. -/
def HilbertAdjointInvertibility : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H),
    IsUnit (Hilbert.Adjoint.Spec.AdjointValue ℂ H H T) ↔ IsUnit T

def HilbertAdjointSpectrum : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H),
    spectrum ℂ (Hilbert.Adjoint.Spec.AdjointValue ℂ H H T) =
      (starRingEnd ℂ) '' spectrum ℂ T

end ExpandedFA.BanachAlgebra.AdjointSpectra.Spec
