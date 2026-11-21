import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.RegularProblem

noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate

namespace Specs.D13Unified.Ch10.Lagrange
open _root_.D13Unified.Ch10.RegularProblem

/-- The boundary form, with the paper's sign and conjugation convention. -/
def boundaryFormValue (P : Problem) (u v : ℝ → ℂ) (x : ℝ) : ℂ :=
  (P.p x : ℂ) * (u x * conj (derivative P v x) - derivative P u x * conj (v x))

def boundaryFormType := Problem → (ℝ → ℂ) → (ℝ → ℂ) → ℝ → ℂ

def lagrangeIdentityType : Prop := ∀ (P : Problem) (u v : ℝ → ℂ),
  ContDiffOn ℝ 2 u (interval P) → ContDiffOn ℝ 2 v (interval P) →
  (∫ x in P.a..P.b, expression P u x * conj (v x) - u x * conj (expression P v x)) =
    boundaryFormValue P u v P.b - boundaryFormValue P u v P.a

def boundaryFormZeroType : Prop := ∀ (P : Problem) (B : BoundaryCoefficients)
  (u v : ℝ → ℂ), SatisfiesBoundary P B u → SatisfiesBoundary P B v →
  boundaryFormValue P u v P.a = 0 ∧ boundaryFormValue P u v P.b = 0

def eigenvalueRealType : Prop := ∀ (P : Problem) (B : BoundaryCoefficients)
  (lam : ℂ) (u : ℝ → ℂ), IsClassicalEigenfunction P B lam u → lam.im = 0

def eigenfunctionsOrthogonalType : Prop := ∀ (P : Problem) (B : BoundaryCoefficients)
  (lam mu : ℂ) (u v : ℝ → ℂ), IsClassicalEigenfunction P B lam u →
  IsClassicalEigenfunction P B mu v → lam ≠ mu →
  ∀ (hu : MemLp u 2 (weightedMeasure P)) (hv : MemLp v 2 (weightedMeasure P)),
  paperInner P (toHilbert P u hu) (toHilbert P v hv) = 0

end Specs.D13Unified.Ch10.Lagrange
