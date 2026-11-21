import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.CubicHomologicalElimination

/-!
The full local normal-form obligation in paper.tex, lines 3601–3654.
All coefficients and both pullbacks are fixed by the accepted finite
homological construction.  In particular the remainder below is a function
of the original field, not a free witness with assumed Taylor bounds.
-/
namespace Specs.D13Unified.Ch16.CubicNormalForm

open Complex
open scoped ComplexConjugate
open CubicHomologicalElimination

noncomputable def sourceQuadratic (F : ℝ × ℂ → ℂ) : ℝ → Quadratic :=
  familyQuadratic F (sourceForwardCLM F) (sourceInverseCLM F)

noncomputable def sourceCubic (F : ℝ × ℂ → ℂ) : ℝ → Cubic :=
  familyCubic F (sourceForwardCLM F) (sourceInverseCLM F)

noncomputable def quadraticCorrection (F : ℝ × ℂ → ℂ) (μ : ℝ) : Quadratic :=
  quadraticChange (spectralReal F μ) (spectralImag F μ) (sourceQuadratic F μ)

noncomputable def intermediateCubic (F : ℝ × ℂ → ℂ) (μ : ℝ) : Cubic :=
  cubicAfterQuadratic (sourceQuadratic F μ) (sourceCubic F μ) (quadraticCorrection F μ)

noncomputable def cubicCorrection (F : ℝ × ℂ → ℂ) (μ : ℝ) : Cubic :=
  cubicChange (spectralReal F μ) (spectralImag F μ) (intermediateCubic F μ)

/-- The normalization-dependent coefficient, including away from μ = 0. -/
noncomputable def coefficient (F : ℝ × ℂ → ℂ) (μ : ℝ) : ℂ :=
  (intermediateCubic F μ).c21

/-- No hypothesis of nonvanishing is imposed in this lemma. -/
noncomputable def firstLyapunovCoefficient (F : ℝ × ℂ → ℂ) : ℝ :=
  (coefficient F 0).re

noncomputable def firstPullback (F : ℝ × ℂ → ℂ) (μ : ℝ) : ℂ → ℂ :=
  nonlinearPullback
    (fun z => linearNormalizedFamily F (sourceForwardCLM F) (sourceInverseCLM F) (μ, z))
    (fun z => z + (quadraticCorrection F μ).eval z)

noncomputable def transformedField (F : ℝ × ℂ → ℂ) (x : ℝ × ℂ) : ℂ :=
  nonlinearPullback (firstPullback F x.1)
    (fun z => z + (cubicCorrection F x.1).eval z) x.2

noncomputable def normalPolynomial (F : ℝ × ℂ → ℂ) (μ : ℝ) (w : ℂ) : ℂ :=
  eigenvalue (spectralReal F μ) (spectralImag F μ) * w +
    coefficient F μ * w ^ 2 * conj w

noncomputable def remainder (F : ℝ × ℂ → ℂ) (x : ℝ × ℂ) : ℂ :=
  transformedField F x - normalPolynomial F x.1 x.2

/-- Forward map from final normal coordinates to the original real plane. -/
noncomputable def coordinate (F : ℝ × ℂ → ℂ) (μ : ℝ) (w : ℂ) : ℂ :=
  let v := w + (cubicCorrection F μ).eval w
  sourceForwardCLM F μ (v + (quadraticCorrection F μ).eval v)

noncomputable def familyCoordinate (F : ℝ × ℂ → ℂ) (x : ℝ × ℂ) : ℝ × ℂ :=
  (x.1, coordinate F x.1 x.2)

def stateParameterBox (ε ρ : ℝ) : Set (ℝ × ℂ) :=
  {x | |x.1| < ε ∧ ‖x.2‖ < ρ}

noncomputable def spatialDerivative (R : ℝ × ℂ → ℂ) (x : ℝ × ℂ) : ℂ →L[ℝ] ℂ :=
  fderiv ℝ (fun w => R (x.1, w)) x.2

/-- First parameter derivatives are ordinary real derivatives at fixed state.
The fourth bound also controls the parameter derivative of the spatial
derivative.  Differentiability assertions prevent totalized derivatives
from making any of these estimates vacuous. -/
def UniformRemainderBounds (F : ℝ × ℂ → ℂ) (ε ρ C : ℝ) : Prop :=
  ∀ x ∈ stateParameterBox ε ρ,
    ContDiffAt ℝ 2 (remainder F) x ∧
    ContDiffAt ℝ 2 (spatialDerivative (remainder F)) x ∧
    ContDiffAt ℝ 5 (fun w => transformedField F (x.1, w)) x.2 ∧
    DifferentiableAt ℝ (fun μ => remainder F (μ, x.2)) x.1 ∧
    DifferentiableAt ℝ (fun μ => spatialDerivative (remainder F) (μ, x.2)) x.1 ∧
    ‖remainder F x‖ ≤ C * ‖x.2‖ ^ 4 ∧
    ‖spatialDerivative (remainder F) x‖ ≤ C * ‖x.2‖ ^ 3 ∧
    ‖deriv (fun μ => remainder F (μ, x.2)) x.1‖ ≤ C * ‖x.2‖ ^ 4 ∧
    ‖deriv (fun μ => spatialDerivative (remainder F) (μ, x.2)) x.1‖ ≤ C * ‖x.2‖ ^ 3

/-- One coordinate neighborhood for all parameters, with its genuine inverse
and the differential identity carrying the transformed field to the input.
All differentiability is real; no complex holomorphy is being asserted. -/
def CoordinateValidity (F : ℝ × ℂ → ℂ) (ε ρ : ℝ) : Prop :=
  ∃ e : OpenPartialHomeomorph (ℝ × ℂ) (ℝ × ℂ),
    (e : ℝ × ℂ → ℝ × ℂ) = familyCoordinate F ∧
    stateParameterBox ε ρ ⊆ e.source ∧
    (∀ y ∈ e.target, (e.symm y).1 = y.1) ∧
    ∀ x ∈ stateParameterBox ε ρ,
      ContDiffAt ℝ 2 (e : ℝ × ℂ → ℝ × ℂ) x ∧
      ContDiffAt ℝ 2 e.symm (e x) ∧
      (fderiv ℝ (coordinate F x.1) x.2).IsInvertible ∧
      fderiv ℝ (coordinate F x.1) x.2 (transformedField F x) =
        F (x.1, coordinate F x.1 x.2)

/-- Complete conclusion, with the C⁵ hypothesis local in all variables and
the equilibrium hypothesis local in the parameter.  The positive spectral
branch is constructed from the actual derivative, so no regularity of an
arbitrary eigenvalue label is assumed. -/
def NormalForm : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) →
    spectralReal F 0 = 0 ∧ spectralImag F 0 = ω ∧
    ∃ ε > 0, ∃ ρ > 0, ∃ C > 0,
      CoordinateValidity F ε ρ ∧ UniformRemainderBounds F ε ρ C ∧
      ∀ μ : ℝ, |μ| < ε →
        0 < spectralImag F μ ∧
        ContDiffAt ℝ 4 (spectralReal F) μ ∧ ContDiffAt ℝ 4 (spectralImag F) μ ∧
        ContDiffAt ℝ 2 (coefficient F) μ ∧
        (∀ l : ℂ, Module.End.HasEigenvalue (complexifiedLinearization F μ).toLin' l ↔
          l = eigenvalue (spectralReal F μ) (spectralImag F μ) ∨
          l = conj (eigenvalue (spectralReal F μ) (spectralImag F μ))) ∧
        (∀ w : ℂ, transformedField F (μ, w) =
          eigenvalue (spectralReal F μ) (spectralImag F μ) * w +
            coefficient F μ * w ^ 2 * conj w + remainder F (μ, w))

/-- A useful proper subset of the obligation: value estimates at each fixed
parameter.  The constants here may depend on μ, unlike `NormalForm`. -/
def PointwiseValueBounds : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) →
    ∃ ε > 0, ∀ μ : ℝ, |μ| < ε →
      ContDiffAt ℝ 2 (coefficient F) μ ∧
      ∃ ρ > 0, ∃ C > 0, ∀ w : ℂ, ‖w‖ < ρ →
        ‖remainder F (μ, w)‖ ≤ C * ‖w‖ ^ 4

/-- Composing the two finite changes with the spectral basis gives actual
parameter-dependent coordinates for the original plane, at each (μ,0). -/
def CoordinateLocalInverses : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) →
    ∃ ε > 0, ∀ μ : ℝ, |μ| < ε → JointInverseAt 2 (familyCoordinate F) μ

def CommonCoordinateNeighborhood : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) →
    ∃ ε > 0, ∃ ρ > 0, CoordinateValidity F ε ρ

/-- The remaining analytic estimate, stated independently of coordinate
validity.  Both the radius and the constant are common to all small μ. -/
def UniformEstimates : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) →
    ∃ ε > 0, ∃ ρ > 0, ∃ C > 0, UniformRemainderBounds F ε ρ C

end Specs.D13Unified.Ch16.CubicNormalForm
