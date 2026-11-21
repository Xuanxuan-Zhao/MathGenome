import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.C1Absolute
import Mathlib.Topology.Instances.AddCircle.Defs

/-! K03.19.c1_uniform, paper.tex:4900–4920.
The data are C¹ on the closed interval, with matching values only.
The target is the actual continuous periodic extension, including both seams.
No hypotheses on f outside the reference interval or on its endpoint
first derivatives are imposed. Coefficients retain the proper Darboux integral.
The piecewise C¹ variant is allocated to PiecewiseC1Uniform. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.C1Uniform
open PeriodicSetup Representation
open scoped BigOperators

/-- Repeat the values on [-π,π), using the quotient by the period 2π. -/
def periodicExtensionValue (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  AddCircle.liftIco (2 * Real.pi) (-Real.pi) f (x : AddCircle (2 * Real.pi))

abbrev periodicExtensionType := (ℝ → ℂ) → ℝ → ℂ

/-- Existence, seam agreement, and continuity of the specified extension. -/
def extensionProperties : Prop := ∀ (f : ℝ → ℂ),
  ContinuousOn f (Set.Icc (-Real.pi) Real.pi) →
  f (-Real.pi) = f Real.pi →
  Continuous (periodicExtensionValue f) ∧
  Function.Periodic (periodicExtensionValue f) (2 * Real.pi) ∧
  Set.EqOn (periodicExtensionValue f) f (Set.Icc (-Real.pi) Real.pi)

/-- Absolute summability and uniform convergence, with the sum identified
pointwise on all of ℝ, rather than only up to a.e. equality. -/
def absoluteUniformToExtension : Prop := ∀ (f : ℝ → ℂ),
  ContDiffOn ℝ 1 f (Set.Icc (-Real.pi) Real.pi) →
  f (-Real.pi) = f Real.pi →
  ∃ H : ComplexWeights f,
    Summable (fun n : ℤ => ‖coefficientValue f n (H n)‖) ∧
    Continuous (periodicExtensionValue f) ∧
    Function.Periodic (periodicExtensionValue f) (2 * Real.pi) ∧
    Set.EqOn (periodicExtensionValue f) f (Set.Icc (-Real.pi) Real.pi) ∧
    Ch12.Uniform.complexUniformConvergesValue (partialSumValue f H)
      (periodicExtensionValue f) ∧
    Ch12.Uniform.realUniformConvergesValue
      (fun N x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ‖coefficientValue f n (H n) * modeValue n x‖)
      (fun _ => ∑' n : ℤ, ‖coefficientValue f n (H n)‖) ∧
    (∀ x : ℝ, HasSum (fun n : ℤ => coefficientValue f n (H n) * modeValue n x)
      (periodicExtensionValue f x))

end Specs.SingleVariableAnalysis.Ch19.C1Uniform
