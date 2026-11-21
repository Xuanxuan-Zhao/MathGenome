import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Independent interface for paper.tex, Theorem d12:01-02 (lines 205–226).
The coordinate partials below are actual one-variable real derivatives of
coordinate slices. No continuity of these partials is part of any hypothesis.
The real matrix uses the ordered basis (1, i), i.e. the standard identification
of the complex plane with the real coordinate plane.
-/
noncomputable section
namespace D12Complex

def partialX (u : ℂ → ℝ) (a : ℂ) : ℝ :=
  deriv (fun t : ℝ => u (a + (t : ℂ))) 0

def partialY (u : ℂ → ℝ) (a : ℂ) : ℝ :=
  deriv (fun t : ℝ => u (a + (t : ℂ) * Complex.I)) 0

def realDifferentialMatrix (f : ℂ → ℂ) (a : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (fderiv ℝ f a).toLinearMap

end D12Complex

namespace Specs.D12Complex.Ch01.RealComplexDifferential
open _root_.D12Complex
open Complex

def partialX_type := (ℂ → ℝ) → ℂ → ℝ
def partialX_value : partialX_type :=
  fun u a => deriv (fun t : ℝ => u (a + (t : ℂ))) 0

def partialY_type := (ℂ → ℝ) → ℂ → ℝ
def partialY_value : partialY_type :=
  fun u a => deriv (fun t : ℝ => u (a + (t : ℂ) * I)) 0

def realDifferentialMatrix_type := (ℂ → ℂ) → ℂ → Matrix (Fin 2) (Fin 2) ℝ
def realDifferentialMatrix_value : realDifferentialMatrix_type :=
  fun f a => LinearMap.toMatrix basisOneI basisOneI (fderiv ℝ f a).toLinearMap

def hasComplexDerivativeAt_iff_real_type : Prop :=
  ∀ (f : ℂ → ℂ) (c a : ℂ), HasComplexDerivativeAt f c a ↔
    HasFDerivAt f (c • (1 : ℂ →L[ℝ] ℂ)) a

def complexDifferentiableAt_iff_real_complexLinear_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), ComplexDifferentiableAt f a ↔
    DifferentiableAt ℝ f a ∧
      ∀ (c z : ℂ), fderiv ℝ f a (c * z) = c * fderiv ℝ f a z

def realDifferential_apply_type : Prop :=
  ∀ (f : ℂ → ℂ) (c a : ℂ), HasComplexDerivativeAt f c a →
    ∀ z : ℂ, fderiv ℝ f a z = c * z

def coordinate_partials_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), DifferentiableAt ℝ f a →
    partialX (fun z => (f z).re) a = (fderiv ℝ f a 1).re ∧
    partialY (fun z => (f z).re) a = (fderiv ℝ f a I).re ∧
    partialX (fun z => (f z).im) a = (fderiv ℝ f a 1).im ∧
    partialY (fun z => (f z).im) a = (fderiv ℝ f a I).im

def complexDifferentiableAt_iff_CR_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), DifferentiableAt ℝ f a →
    (ComplexDifferentiableAt f a ↔
      partialX (fun z => (f z).re) a = partialY (fun z => (f z).im) a ∧
      partialY (fun z => (f z).re) a = -partialX (fun z => (f z).im) a)

def complexDerivative_CR_formulas_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), DifferentiableAt ℝ f a →
    partialX (fun z => (f z).re) a = partialY (fun z => (f z).im) a →
    partialY (fun z => (f z).re) a = -partialX (fun z => (f z).im) a →
    HasComplexDerivativeAt f
      ((partialX (fun z => (f z).re) a : ℂ) + I * partialX (fun z => (f z).im) a) a ∧
    HasComplexDerivativeAt f
      ((partialY (fun z => (f z).im) a : ℂ) - I * partialY (fun z => (f z).re) a) a ∧
    deriv f a = (partialX (fun z => (f z).re) a : ℂ) +
      I * partialX (fun z => (f z).im) a ∧
    deriv f a = (partialY (fun z => (f z).im) a : ℂ) -
      I * partialY (fun z => (f z).re) a

def realDifferential_matrix_type : Prop :=
  ∀ (f : ℂ → ℂ) (c a : ℂ), HasComplexDerivativeAt f c a →
    realDifferentialMatrix f a = !![c.re, -c.im; c.im, c.re]

def realDifferential_det_type : Prop :=
  ∀ (f : ℂ → ℂ) (c a : ℂ), HasComplexDerivativeAt f c a →
    LinearMap.det (fderiv ℝ f a).toLinearMap = ‖c‖ ^ 2 ∧
    (realDifferentialMatrix f a).det = ‖c‖ ^ 2

end Specs.D12Complex.Ch01.RealComplexDifferential
