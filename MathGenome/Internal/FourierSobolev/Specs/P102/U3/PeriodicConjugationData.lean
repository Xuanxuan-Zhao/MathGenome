import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation
import Mathlib.Analysis.Complex.Trigonometric

/-! Shared definitions for paper.tex:47–56, 1186–1200.

This module imports only the independent periodic foundation and library
definitions. In particular, it imports neither the periodic-conjugation parent
nor any Calderón–Zygmund statement. All three conjugation proof modules use
these same objects. `PolynomialPrincipalValues` is a proposition to be proved
by the kernel child, not a supplied certificate.

The coordinate integrals use real Lebesgue measure. Thus the probability-Haar
factor `1 / T` is included in `coordinateKernel` exactly once. Integrals are
totalized; their absolute existence is asserted separately in the proposition.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace P102.Periodic.Conjugation

open P102.Periodic.Expected

/-- The source sign convention includes the zero multiplier at frequency zero. -/
def symbol (n : ℤ) : ℂ := -Complex.I * (n.sign : ℂ)

/-- Finite Fourier synthesis after multiplication by `-i sign(n)`. -/
def polynomialAction (T : ℝ) : (ℤ →₀ ℂ) →ₗ[ℂ] C(Circle T, ℂ) :=
  Finsupp.linearCombination ℂ (fun n : ℤ => symbol n • mode T n)

/-- The periodic Hilbert kernel in coordinates against `dt`, rather than `dt/T`. -/
def coordinateKernel (T t : ℝ) : ℂ :=
  (T⁻¹ * Real.cot (Real.pi * t / T) : ℝ)

/-- Ordinary symmetric physical truncation. Every positive radius is allowed,
including radii for which the domain is empty. -/
def truncation (T ε : ℝ) (f : Circle T → ℂ) (x : Circle T) : ℂ :=
  ∫ t in (Ioo (-T / 2) (T / 2) ∩ {t : ℝ | ε < |t|}),
    coordinateKernel T t * f (x - (t : Circle T))

/-- The absolutely integrable cancellation formula on polynomials; absolute
integrability is a conclusion of `PolynomialPrincipalValues`. -/
def cancelledValue (T : ℝ) (f : Circle T → ℂ) (x : Circle T) : ℂ :=
  ∫ t in Ioo (-T / 2) (T / 2),
    coordinateKernel T t * (f (x - (t : Circle T)) - f x)

/-- The complete unconditional polynomial kernel-identification obligation.
It assumes neither an Lp estimate nor an operator or principal-value witness. -/
def PolynomialPrincipalValues (T : ℝ) [Fact (0 < T)] : Prop :=
  ∀ (c : ℤ →₀ ℂ) (x : Circle T),
    (∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun t : ℝ => coordinateKernel T t * synthesis T c (x - (t : Circle T)))
        (Ioo (-T / 2) (T / 2) ∩ {t : ℝ | ε < |t|}) volume) ∧
    IntegrableOn (fun t : ℝ => coordinateKernel T t *
      (synthesis T c (x - (t : Circle T)) - synthesis T c x))
      (Ioo (-T / 2) (T / 2)) volume ∧
    cancelledValue T (synthesis T c) x = polynomialAction T c x ∧
    Tendsto (fun ε : ℝ => truncation T ε (synthesis T c) x) (𝓝[>] 0)
      (𝓝 (polynomialAction T c x))

namespace Expected

/-- Routine defining formulas for the shared interface. This proposition does
not assert `PolynomialPrincipalValues`; that remains the kernel child's task. -/
def DataFormulas : Prop :=
  (∀ n : ℤ, symbol n = -Complex.I * (n.sign : ℂ)) ∧
  (∀ (T : ℝ) (c : ℤ →₀ ℂ) (x : Circle T),
    polynomialAction T c x = c.sum (fun n a => a * symbol n * mode T n x)) ∧
  (∀ T t : ℝ, coordinateKernel T t = ((1 / T) * Real.cot (Real.pi * t / T) : ℝ)) ∧
  (∀ (T ε : ℝ) (f : Circle T → ℂ) (x : Circle T),
    truncation T ε f x = ∫ t in (Ioo (-T / 2) (T / 2) ∩ {t : ℝ | ε < |t|}),
      coordinateKernel T t * f (x - (t : Circle T))) ∧
  (∀ (T : ℝ) (f : Circle T → ℂ) (x : Circle T),
    cancelledValue T f x = ∫ t in Ioo (-T / 2) (T / 2),
      coordinateKernel T t * (f (x - (t : Circle T)) - f x))

end Expected
end P102.Periodic.Conjugation
