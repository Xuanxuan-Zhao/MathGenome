import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.CubicNormalForm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Independent interface for the polar part of paper.tex:3667–3677,3694–3695.
The shared names remain in HopfReturnExpansion for the parent's assembly.
All polar quantities use the actual canonical remainder of the original family.
-/
namespace Specs.D13Unified.Ch16.HopfReturnExpansion

open Complex Filter Set
open scoped ComplexConjugate
open CubicHomologicalElimination CubicNormalForm

noncomputable def direction (θ : ℝ) : ℂ := Complex.exp (θ * I)
noncomputable def polarPoint (r θ : ℝ) : ℂ := r * direction θ
noncomputable def polarRemainder (F : ℝ × ℂ → ℂ) (θ r μ : ℝ) : ℂ :=
  conj (direction θ) * remainder F (μ, polarPoint r θ)
noncomputable def radialVelocity (F : ℝ × ℂ → ℂ) (θ r μ : ℝ) : ℝ :=
  spectralReal F μ * r + (coefficient F μ).re * r ^ 3 + (polarRemainder F θ r μ).re
noncomputable def angularVelocity (F : ℝ × ℂ → ℂ) (θ r μ : ℝ) : ℝ :=
  spectralImag F μ + (coefficient F μ).im * r ^ 2 + (polarRemainder F θ r μ).im / r
noncomputable def angularField (F : ℝ × ℂ → ℂ) (θ r μ : ℝ) : ℝ :=
  radialVelocity F θ r μ / angularVelocity F θ r μ
noncomputable def angularLinear (F : ℝ × ℂ → ℂ) (μ : ℝ) : ℝ :=
  spectralReal F μ / spectralImag F μ
noncomputable def angularCubic (F : ℝ × ℂ → ℂ) (μ : ℝ) : ℝ :=
  (coefficient F μ).re / spectralImag F μ -
    spectralReal F μ * (coefficient F μ).im / spectralImag F μ ^ 2
noncomputable def cubicReturnCoefficient (F : ℝ × ℂ → ℂ) (μ : ℝ) : ℝ :=
  angularCubic F μ * Real.exp (2 * Real.pi * angularLinear F μ) *
    ∫ s in (0 : ℝ)..2 * Real.pi, Real.exp (2 * angularLinear F μ * s)

def positiveRay (z : ℂ) : Prop := z.im = 0 ∧ 0 < z.re

/-- Genuine physical first return; no prior periodic orbit is a premise. -/
def FirstAngularTurn (F : ℝ × ℂ → ℂ) (μ r q : ℝ) : Prop :=
  ∃ T > 0, ∃ z : ℝ → ℂ,
    ContinuousOn z (Icc 0 T) ∧
    (∀ t ∈ Icc 0 T, HasDerivWithinAt z (transformedField F (μ, z t)) (Icc 0 T) t) ∧
    z 0 = (r : ℂ) ∧ z T = (q : ℂ) ∧ 0 < q ∧
    ∀ t ∈ Ioo 0 T, ¬ positiveRay (z t)

end Specs.D13Unified.Ch16.HopfReturnExpansion

namespace Specs.D13Unified.Ch16.HopfPolarReduction

open Complex Filter Set
open scoped ComplexConjugate
open CubicHomologicalElimination CubicNormalForm HopfReturnExpansion

/-- θ, signed radius, parameter. This is an open neighborhood of the entire turn. -/
def polarBox (ε ρ : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {x | -1 < x.1 ∧ x.1 < 2 * Real.pi + 1 ∧ |x.2.1| < ρ ∧ |x.2.2| < ε}

/-- Hadamard factor of the actual rotated remainder, defined at signed radius zero. -/
noncomputable def dividedRemainder (F : ℝ × ℂ → ℂ) (x : ℝ × (ℝ × ℝ)) : ℂ :=
  conj (direction x.1) * ∫ t in (0 : ℝ)..1,
    spatialDerivative (remainder F) (x.2.2, polarPoint (t * x.2.1) x.1) (direction x.1)

noncomputable def signedFactor (F : ℝ × ℂ → ℂ) (x : ℝ × (ℝ × ℝ)) : ℝ :=
  (spectralReal F x.2.2 + (coefficient F x.2.2).re * x.2.1 ^ 2 + (dividedRemainder F x).re) /
    (spectralImag F x.2.2 + (coefficient F x.2.2).im * x.2.1 ^ 2 + (dividedRemainder F x).im)

noncomputable def scalarResidual (F : ℝ × ℂ → ℂ)
    (G : ℝ × (ℝ × ℝ) → ℝ) (θ r μ : ℝ) : ℝ :=
  r * G (θ, r, μ) - angularLinear F μ * r - angularCubic F μ * r ^ 3

/-- Smooth signed division and quantitative residual, on the SAME chart. -/
def SignedPolarData (F : ℝ × ℂ → ℂ) (ω ε ρ C : ℝ)
    (G : ℝ × (ℝ × ℝ) → ℝ) : Prop :=
  CoordinateValidity F ε ρ ∧
  UniformRemainderBounds F ε ρ C ∧
  ContDiffOn ℝ 2 G (polarBox ε ρ) ∧
  (∀ μ : ℝ, |μ| < ε →
    ContDiffAt ℝ 2 (angularLinear F) μ ∧ ContDiffAt ℝ 2 (angularCubic F) μ) ∧
  (∀ θ r μ : ℝ, |r| < ρ → |μ| < ε → ω / 2 < angularVelocity F θ r μ) ∧
  ∀ x ∈ polarBox ε ρ,
    G (x.1, 0, x.2.2) = angularLinear F x.2.2 ∧
    angularField F x.1 x.2.1 x.2.2 = x.2.1 * G x ∧
    ω / 2 < angularVelocity F x.1 x.2.1 x.2.2 ∧
    DifferentiableAt ℝ (fun r => scalarResidual F G x.1 r x.2.2) x.2.1 ∧
    DifferentiableAt ℝ (fun μ => scalarResidual F G x.1 x.2.1 μ) x.2.2 ∧
    |scalarResidual F G x.1 x.2.1 x.2.2| ≤ C * |x.2.1| ^ 4 ∧
    |deriv (fun r => scalarResidual F G x.1 r x.2.2) x.2.1| ≤ C * |x.2.1| ^ 3 ∧
    |deriv (fun μ => scalarResidual F G x.1 x.2.1 μ) x.2.2| ≤ C * |x.2.1| ^ 4

noncomputable def physicalClock (F : ℝ × ℂ → ℂ) (μ : ℝ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..θ, 1 / angularVelocity F s (u s) μ

/-- Conditional on a positive full-turn angular solution, construct its
physical clock and a physical-time solution, including endpoint derivatives.
No angular-IVP existence or scalar expansion is assumed as a certificate. -/
def ReconstructionOnChart (F : ℝ × ℂ → ℂ) (ε ρ : ℝ) : Prop :=
  ∀ (μ r : ℝ) (u : ℝ → ℝ), |μ| < ε → 0 < r → u 0 = r →
    ContinuousOn u (Icc 0 (2 * Real.pi)) →
    (∀ θ ∈ Icc 0 (2 * Real.pi),
      HasDerivWithinAt u (angularField F θ (u θ) μ) (Icc 0 (2 * Real.pi)) θ) →
    (∀ θ ∈ Icc 0 (2 * Real.pi), 0 < u θ ∧ u θ < ρ) →
    let clock := physicalClock F μ u
    ∃ T > 0, ∃ z : ℝ → ℂ,
      clock 0 = 0 ∧ clock (2 * Real.pi) = T ∧
      ContinuousOn clock (Icc 0 (2 * Real.pi)) ∧
      StrictMonoOn clock (Icc 0 (2 * Real.pi)) ∧
      Set.BijOn clock (Icc 0 (2 * Real.pi)) (Icc 0 T) ∧
      (∀ θ ∈ Icc 0 (2 * Real.pi),
        HasDerivWithinAt clock (1 / angularVelocity F θ (u θ) μ)
          (Icc 0 (2 * Real.pi)) θ) ∧
      ContinuousOn z (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T,
        HasDerivWithinAt z (transformedField F (μ, z t)) (Icc 0 T) t ∧ ‖z t‖ < ρ) ∧
      (∀ θ ∈ Icc 0 (2 * Real.pi), z (clock θ) = polarPoint (u θ) θ) ∧
      z 0 = (r : ℂ) ∧ z T = (u (2 * Real.pi) : ℂ) ∧
      FirstAngularTurn F μ r (u (2 * Real.pi))

/-- Full original-family obligation, with no crossing or cubic nondegeneracy
hypotheses. The existence of an angular IVP is the independent scalar child's job. -/
def PolarReduction : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) →
    ∃ ε > 0, ∃ ρ > 0, ∃ C > 0, ∃ G : ℝ × (ℝ × ℝ) → ℝ,
      SignedPolarData F ω ε ρ C G ∧ ReconstructionOnChart F ε ρ

/-- Smooth factorization and reconstruction, recorded separately so the remaining
quantitative scalar estimates remain an explicit obligation in `PolarReduction`. -/
def SmoothPolarReduction : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) →
    ∃ ε > 0, ∃ ρ > 0, ∃ C > 0,
      CoordinateValidity F ε ρ ∧ UniformRemainderBounds F ε ρ C ∧
      ContDiffOn ℝ 2 (signedFactor F) (polarBox ε ρ) ∧
      (∀ μ : ℝ, |μ| < ε →
        ContDiffAt ℝ 2 (angularLinear F) μ ∧ ContDiffAt ℝ 2 (angularCubic F) μ) ∧
      (∀ θ r μ : ℝ, |r| < ρ → |μ| < ε → ω / 2 < angularVelocity F θ r μ) ∧
      (∀ x ∈ polarBox ε ρ,
        signedFactor F (x.1, 0, x.2.2) = angularLinear F x.2.2 ∧
        angularField F x.1 x.2.1 x.2.2 = x.2.1 * signedFactor F x ∧
        DifferentiableAt ℝ (fun r => scalarResidual F (signedFactor F) x.1 r x.2.2) x.2.1 ∧
        DifferentiableAt ℝ (fun μ => scalarResidual F (signedFactor F) x.1 x.2.1 μ) x.2.2) ∧
      ReconstructionOnChart F ε ρ

/-- Algebraic decomposition of the actual vector field, for signed nonzero r. -/
def PolarVelocityIdentity : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (θ r μ : ℝ), r ≠ 0 →
    conj (direction θ) * transformedField F (μ, polarPoint r θ) =
      (radialVelocity F θ r μ : ℂ) + I * (r * angularVelocity F θ r μ : ℝ)

/-- A useful independently checkable part of the full analytic obligation. -/
def PolarNeighborhood : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) →
    ∃ ε > 0, ∃ ρ > 0, ∃ C > 0,
      CoordinateValidity F ε ρ ∧ UniformRemainderBounds F ε ρ C ∧
      (∀ μ : ℝ, |μ| < ε →
        ContDiffAt ℝ 2 (angularLinear F) μ ∧ ContDiffAt ℝ 2 (angularCubic F) μ) ∧
      ∀ θ r μ : ℝ, |r| < ρ → |μ| < ε →
        ω / 2 < angularVelocity F θ r μ

end Specs.D13Unified.Ch16.HopfPolarReduction
