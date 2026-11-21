import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Independent full statements for paper.tex, d13:10:spectrum.
The natural index `n` denotes the paper's index `j = n + 1`. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Specs.D13Unified.Ch10.Spectrum
open RegularProblem ClassicalEigenfunctionBridge

/-- Infinitude concerns the actual weighted complex L² quotient. -/
def InfiniteDimension : Prop := ∀ P : Problem, ¬ FiniteDimensional ℂ (hilbertValue P)

/-- The full regular Dirichlet expansion, including exhaustiveness among complex
classical eigenvalues, simplicity, real representatives and both Hilbert sums. -/
def Expansion : Prop := ∀ P : Problem,
  ∃ (lam : ℕ → ℝ) (phi : ℕ → ℝ → ℝ)
    (hphi : ∀ n, MemLp (fun x => (phi n x : ℂ)) 2 (weightedMeasureValue P))
    (B : HilbertBasis ℕ ℂ (hilbertValue P)),
    StrictMono lam ∧ Tendsto lam atTop atTop ∧
    (∀ n, classicalEigenfunctionValue P dirichletValue (lam n : ℂ)
      (fun x => (phi n x : ℂ))) ∧
    (∀ n, B n = toHilbertValue P (fun x => (phi n x : ℂ)) (hphi n)) ∧
    (∀ (z : ℂ) (y : ℝ → ℂ),
      classicalEigenfunctionValue P dirichletValue z y → ∃ n, z = (lam n : ℂ)) ∧
    (∀ n, classicalEigenspace P (lam n : ℂ) =
      (ℂ ∙ B n : Submodule ℂ (hilbertValue P)) ∧
      Module.finrank ℂ (ℂ ∙ B n : Submodule ℂ (hilbertValue P)) = 1) ∧
    (∀ f : hilbertValue P,
      HasSum (fun n => paperInnerValue P f (B n) • B n) f ∧
      HasSum (fun n => ‖paperInnerValue P f (B n)‖ ^ 2) (‖f‖ ^ 2))
end Specs.D13Unified.Ch10.Spectrum
