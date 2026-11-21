import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2KernelCompact
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! Independent objects and full statements for `fa2:p5:volterra-singular-system`,
paper.tex 22771–22794. The power-norm asymptotic is separately allocated to
`app_volterra_power_asymptotic`. Index n here is source index j = n + 1.
The measure is Lebesgue measure restricted to the actual open interval (0,T).
The declarations below assume neither orthogonality nor any operator formula. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace ExpandedFA.PartV.VolterraSingularSystemSpec

abbrev intervalMeasure (T : ℝ) : Measure ℝ := volume.restrict (Ioo 0 T)
abbrev Space (𝕜 : Type) [RCLike 𝕜] (T : ℝ) := Lp 𝕜 2 (intervalMeasure T)

def frequency (T : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1 / 2) * Real.pi / T
def sigma (T : ℝ) (n : ℕ) : ℝ := T / (((n : ℝ) + 1 / 2) * Real.pi)
def cosineFunction (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (n : ℕ) (t : ℝ) : 𝕜 :=
  (Real.sqrt (2 / T) * Real.cos (frequency T n * t) : ℝ)
def sineFunction (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (n : ℕ) (t : ℝ) : 𝕜 :=
  (Real.sqrt (2 / T) * Real.sin (frequency T n * t) : ℝ)

theorem cosine_memLp (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (n : ℕ) :
    MemLp (cosineFunction 𝕜 T n) 2 (intervalMeasure T) := by
  apply MemLp.of_bound (C := |Real.sqrt (2 / T)|)
  · exact (RCLike.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · exact Eventually.of_forall fun t => by
      simp only [cosineFunction, RCLike.norm_ofReal, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem sine_memLp (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (n : ℕ) :
    MemLp (sineFunction 𝕜 T n) 2 (intervalMeasure T) := by
  apply MemLp.of_bound (C := |Real.sqrt (2 / T)|)
  · exact (RCLike.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · exact Eventually.of_forall fun t => by
      simp only [sineFunction, RCLike.norm_ofReal, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

def rightVector (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (n : ℕ) : Space 𝕜 T :=
  (cosine_memLp 𝕜 T n).toLp (cosineFunction 𝕜 T n)
def leftVector (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (n : ℕ) : Space 𝕜 T :=
  (sine_memLp 𝕜 T n).toLp (sineFunction 𝕜 T n)

def kernelFunction (𝕜 : Type) [RCLike 𝕜] (p : ℝ × ℝ) : 𝕜 :=
  if p.2 < p.1 then 1 else 0

theorem kernel_memLp (𝕜 : Type) [RCLike 𝕜] (T : ℝ) :
    MemLp (kernelFunction 𝕜) 2 ((intervalMeasure T).prod (intervalMeasure T)) := by
  apply MemLp.of_bound (C := 1)
  · exact (Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
      measurable_const measurable_const).aestronglyMeasurable
  · exact Eventually.of_forall fun p => by
      dsimp [kernelFunction]
      split_ifs <;> simp

def kernel (𝕜 : Type) [RCLike 𝕜] (T : ℝ) :
    Lp 𝕜 2 ((intervalMeasure T).prod (intervalMeasure T)) :=
  (kernel_memLp 𝕜 T).toLp (kernelFunction 𝕜)

/-- The established canonical L² kernel operator for 1_{s<t}. -/
def operator (𝕜 : Type) [RCLike 𝕜] (T : ℝ) : Space 𝕜 T →L[𝕜] Space 𝕜 T :=
  L2KernelSpec.OperatorValue (intervalMeasure T) (intervalMeasure T) (kernel 𝕜 T)

def IntegralFormula : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T → ∀ u : Space 𝕜 T,
    (operator 𝕜 T u : ℝ → 𝕜) =ᵐ[intervalMeasure T]
      fun t => ∫ s in Ioo 0 t, u s

def AdjointFormula : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T → ∀ u : Space 𝕜 T,
    (ContinuousLinearMap.adjoint (operator 𝕜 T) u : ℝ → 𝕜)
      =ᵐ[intervalMeasure T] fun s => ∫ t in Ioo s T, u t

def Compact : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T →
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (operator 𝕜 T).toLinearMap

def CompleteOrthonormalSystems : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T →
    Orthonormal 𝕜 (rightVector 𝕜 T) ∧ Orthonormal 𝕜 (leftVector 𝕜 T) ∧
    (Submodule.span 𝕜 (range (rightVector 𝕜 T))).topologicalClosure = ⊤ ∧
    (Submodule.span 𝕜 (range (leftVector 𝕜 T))).topologicalClosure = ⊤

def SingularIdentities : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T → ∀ n : ℕ,
    operator 𝕜 T (rightVector 𝕜 T n) = (sigma T n : 𝕜) • leftVector 𝕜 T n ∧
    ContinuousLinearMap.adjoint (operator 𝕜 T) (leftVector 𝕜 T n) =
      (sigma T n : 𝕜) • rightVector 𝕜 T n

def SingularValues : Prop :=
  ∀ (T : ℝ), 0 < T →
    (∀ n : ℕ, 0 < sigma T n) ∧ Antitone (sigma T) ∧
      Tendsto (sigma T) atTop (𝓝 0) ∧ sigma T 0 = 2 * T / Real.pi

def NormFormula : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T → ‖operator 𝕜 T‖ = 2 * T / Real.pi

def SingularExpansions : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T → ∀ u : Space 𝕜 T,
    HasSum (fun n => ((sigma T n : 𝕜) * inner 𝕜 (rightVector 𝕜 T n) u) •
      leftVector 𝕜 T n) (operator 𝕜 T u) ∧
    HasSum (fun n => ((sigma T n : 𝕜) * inner 𝕜 (leftVector 𝕜 T n) u) •
      rightVector 𝕜 T n) (ContinuousLinearMap.adjoint (operator 𝕜 T) u)

def SpectrumFormula : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T → spectrum 𝕜 (operator 𝕜 T) = {0}

/-- Conditional assembly helper, not a substitute for proving completeness. -/
def NormFromCompleteSystems : Prop := CompleteOrthonormalSystems → NormFormula

def ExpansionsFromCompleteSystems : Prop := CompleteOrthonormalSystems → SingularExpansions

end ExpandedFA.PartV.VolterraSingularSystemSpec
