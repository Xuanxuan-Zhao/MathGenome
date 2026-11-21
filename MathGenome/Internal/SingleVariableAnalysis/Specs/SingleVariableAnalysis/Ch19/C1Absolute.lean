import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.CoefficientDecay
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Representation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform

/-! K03.19.c1_uniform. The input is C¹ only on the closed reference interval;
no derivative matching at the seams or regularity outside it is required.
The sum is constructed on all of ℝ. Identification with the periodic extension
of f is allocated downstream to coefficient uniqueness. All coefficient
integrals here are the proper Darboux integrals, with explicit witnesses. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.C1Absolute
open PeriodicSetup Representation
open scoped BigOperators

def absoluteUniform : Prop := ∀ (f : ℝ → ℂ),
  ContDiffOn ℝ 1 f (Set.Icc (-Real.pi) Real.pi) →
  f (-Real.pi) = f Real.pi →
  ∃ H : ComplexWeights f,
    Summable (fun n : ℤ => ‖coefficientValue f n (H n)‖) ∧
    ∃ g : ℝ → ℂ,
      Continuous g ∧ Function.Periodic g (2 * Real.pi) ∧
      Ch12.Uniform.complexUniformConvergesValue (partialSumValue f H) g ∧
      Ch12.Uniform.realUniformConvergesValue
        (fun N x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ‖coefficientValue f n (H n) * modeValue n x‖)
        (fun _ => ∑' n : ℤ, ‖coefficientValue f n (H n)‖) ∧
      (∀ x : ℝ, HasSum (fun n : ℤ => coefficientValue f n (H n) * modeValue n x) (g x)) ∧
      ∃ Hg : ComplexWeights g,
        ∀ n : ℤ, coefficientValue g n (Hg n) = coefficientValue f n (H n)

end Specs.SingleVariableAnalysis.Ch19.C1Absolute
