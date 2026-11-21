import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Weyl.RegularWeylRepresentation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Independent statements for the strong Gaussian integral and its corner
identity, paper.tex:16352–16410. Phase space has its existing product Lebesgue
measure. The sum of coordinate squares below is the Euclidean square length;
the norm on the existing Pi coordinate type is a different norm.
No operator-valued measurability or separability of the Hilbert space is assumed.
-/

noncomputable section
open MeasureTheory
universe u

namespace ExpandedFA.Weyl.GaussianCornerSpec
open RegularWeylRepresentationSpec

def phaseSquare {d : ℕ} (z : PhaseSpace d) : ℝ :=
  (∑ j, (z.1 j) ^ 2) + ∑ j, (z.2 j) ^ 2

def gaussianWeight {d : ℕ} (z : PhaseSpace d) : ℝ :=
  Real.exp (-phaseSquare z / 4)

def gaussianNormalization (d : ℕ) : ℝ := (2 * Real.pi) ^ (-(d : ℤ))

def gaussianVectorIntegral {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : RegularRepresentation d H) (x : H) : H :=
  gaussianNormalization d • ∫ z : PhaseSpace d, gaussianWeight z • R.W z x

def GaussianWeightIntegrable : Prop :=
  ∀ d : ℕ, Integrable (gaussianWeight (d := d))

def GaussianOrbitIntegrable : Prop :=
  ∀ {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : RegularRepresentation d H) (x : H),
    Integrable (fun z : PhaseSpace d => gaussianWeight z • R.W z x)

def GaussianIntegralBound : Prop :=
  ∀ {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : RegularRepresentation d H) (x : H),
    ‖gaussianVectorIntegral R x‖ ≤
      |gaussianNormalization d| * (∫ z : PhaseSpace d, gaussianWeight z) * ‖x‖

/-- This establishes that the strong vector integral defines a bounded,
complex-linear operator, without an operator-valued Bochner integral. -/
def GaussianOperatorExists : Prop :=
  ∀ {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : RegularRepresentation d H),
    ∃ P : H →L[ℂ] H, ∀ x, P x = gaussianVectorIntegral R x

def GaussianSelfAdjoint : Prop :=
  ∀ {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : RegularRepresentation d H)
    (P : H →L[ℂ] H), (∀ x, P x = gaussianVectorIntegral R x) → P.adjoint = P

/-- The entire assigned result, with the original integral normalization and
the same representation in every conclusion. -/
def GaussianCorner : Prop :=
  ∀ {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : RegularRepresentation d H),
    ∃ P : H →L[ℂ] H,
      (∀ x, P x = gaussianVectorIntegral R x) ∧
      P.adjoint = P ∧ P.comp P = P ∧
      (∀ w : PhaseSpace d,
        (P.comp (R.W w).toContinuousLinearEquiv.toContinuousLinearMap).comp P =
          (gaussianWeight w : ℂ) • P) ∧ P ≠ 0

end ExpandedFA.Weyl.GaussianCornerSpec
