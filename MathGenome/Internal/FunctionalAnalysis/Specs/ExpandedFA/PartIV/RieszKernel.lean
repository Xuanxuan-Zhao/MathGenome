import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Independent statements for the Riesz-kernel clause of
`paper.tex`, fa2:p4:homogeneous-fourier, 19394–19438.
The kernels have their native real-power value at zero; the statements concern
Lebesgue integrals, so this choice is immaterial when 0 < a < d. In dimension
zero the parameter range is empty. Pairings are complex-linear, without conjugation.
-/

open MeasureTheory Set

noncomputable section
namespace ExpandedFA.PartIV.RieszKernel
open ExpandedFA.Fourier

def powerKernel {d : ℕ} (a : ℝ) (x : Euclidean d) : ℂ := (‖x‖ ^ (-a) : ℝ)

def rieszConstant (d : ℕ) (a : ℝ) : ℝ :=
  Real.pi ^ (a - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - a) / 2) /
    Real.Gamma (a / 2)

def gaussian {d : ℕ} (t : ℝ) (x : Euclidean d) : ℂ :=
  (Real.exp (-Real.pi * t * ‖x‖ ^ 2) : ℝ)

end ExpandedFA.PartIV.RieszKernel

namespace Specs.ExpandedFA.PartIV.RieszKernel
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.PartIV.RieszKernel

def constantPositiveType : Prop := ∀ (d : ℕ) (a : ℝ), 0 < a → a < d →
  0 < rieszConstant d a

def gaussianSuperpositionType : Prop := ∀ (d : ℕ) (a : ℝ), 0 < a →
  ∀ x : Euclidean d, x ≠ 0 →
    IntegrableOn (fun t : ℝ => t ^ (a / 2 - 1) *
      Real.exp (-Real.pi * t * ‖x‖ ^ 2)) (Ioi 0) ∧
    powerKernel a x = ((Real.pi ^ (a / 2) / Real.Gamma (a / 2) : ℝ) : ℂ) *
      ∫ t in Ioi (0 : ℝ), ((t ^ (a / 2 - 1) : ℝ) : ℂ) * gaussian t x

/-- Absolute integrability on the actual product measure justifies Fubini;
this is not an assumption attached to the Fourier identity. -/
def superpositionIntegrableType : Prop := ∀ (d : ℕ) (a : ℝ), 0 < a → a < d →
  ∀ φ : Schwartz ℂ d,
    Integrable (fun p : ℝ × Euclidean d =>
      ((p.1 ^ (a / 2 - 1) : ℝ) : ℂ) * gaussian p.1 p.2 * φ p.2)
      ((volume.restrict (Ioi 0)).prod volume)

/-- Both regular kernels are realised on the continuous Schwartz dual, with
absolute pairings and the manuscript's exact 2π-normalised Fourier identity. -/
def rieszFourierType : Prop := ∀ (d : ℕ) (a : ℝ), 0 < a → a < d →
  ∃ u v : Tempered ℂ d,
    (∀ φ : Schwartz ℂ d,
      Integrable (fun x => powerKernel a x * φ x) ∧
      u φ = ∫ x, powerKernel a x * φ x) ∧
    (∀ φ : Schwartz ℂ d,
      Integrable (fun x => powerKernel ((d : ℝ) - a) x * φ x) ∧
      v φ = ∫ x, powerKernel ((d : ℝ) - a) x * φ x) ∧
    temperedFourier u = (rieszConstant d a : ℂ) • v

end Specs.ExpandedFA.PartIV.RieszKernel
