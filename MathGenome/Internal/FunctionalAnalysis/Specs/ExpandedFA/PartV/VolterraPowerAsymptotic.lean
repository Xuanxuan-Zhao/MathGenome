import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.VolterraSingularSystem
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2HilbertSchmidt
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Independent statements for the sharp power asymptotic in
`fa2:p5:volterra-singular-system`, paper.tex 22772–22810.
The integration operator and its interval L² space are exactly the upstream
objects, over either ℝ or ℂ. The limiting quadrant has ordinary product measure.
No convergence or change-of-variables certificate is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace ExpandedFA.PartV.VolterraPowerAsymptoticSpec

/-- The kernel of the (n+1)st power, with n=0 giving integration itself. -/
def powerKernelFunction (𝕜 : Type) [RCLike 𝕜] (n : ℕ) (p : ℝ × ℝ) : 𝕜 :=
  if p.2 < p.1 then (((p.1 - p.2) ^ n / (n.factorial : ℝ) : ℝ) : 𝕜) else 0

def PowerKernelMemLp : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T → ∀ n : ℕ,
    MemLp (powerKernelFunction 𝕜 n) 2
      ((VolterraSingularSystemSpec.intervalMeasure T).prod
        (VolterraSingularSystemSpec.intervalMeasure T))

def PowerKernelFormula : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T → ∀ n : ℕ,
    ∀ hk : MemLp (powerKernelFunction 𝕜 n) 2
      ((VolterraSingularSystemSpec.intervalMeasure T).prod
        (VolterraSingularSystemSpec.intervalMeasure T)),
    VolterraSingularSystemSpec.operator 𝕜 T ^ (n+1) =
      L2KernelSpec.OperatorValue (VolterraSingularSystemSpec.intervalMeasure T)
        (VolterraSingularSystemSpec.intervalMeasure T) (hk.toLp _)

def PowerIntegralFormula : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T → ∀ n : ℕ,
    ∀ u : VolterraSingularSystemSpec.Space 𝕜 T,
    ((VolterraSingularSystemSpec.operator 𝕜 T ^ (n+1)) u : ℝ → 𝕜)
      =ᵐ[VolterraSingularSystemSpec.intervalMeasure T]
      fun t => ∫ s, powerKernelFunction 𝕜 n (t,s) * u s
        ∂VolterraSingularSystemSpec.intervalMeasure T

abbrev halfLineMeasure : Measure ℝ := volume.restrict (Ioi 0)
abbrev quadrantMeasure : Measure (ℝ × ℝ) := halfLineMeasure.prod halfLineMeasure

/-- Zero extension of the rescaled kernel. The strict triangular cutoff also
specifies the correct n = 1 kernel, without the ambiguous notation 0^0.
For n ≥ 2 this agrees everywhere with the positive-part formula on [0,n]². -/
def rescaledKernel (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  if 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 < (n : ℝ) then
    (1 - (p.1 + p.2) / n) ^ (n - 1)
  else 0

def limitingKernel (p : ℝ × ℝ) : ℝ := Real.exp (-p.1 - p.2)

def PositivePartFormula : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p : ℝ × ℝ,
    rescaledKernel n p = ((Icc (0 : ℝ) n) ×ˢ (Icc (0 : ℝ) n)).indicator
      (fun p : ℝ × ℝ => (max (1 - (p.1 + p.2) / n) 0) ^ (n - 1)) p

def PointwiseLimit : Prop :=
  ∀ p : ℝ × ℝ, 0 ≤ p.1 → 0 ≤ p.2 →
    Tendsto (fun n => rescaledKernel n p) atTop (𝓝 (limitingKernel p))

def ExponentialDomination : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p : ℝ × ℝ,
    0 ≤ rescaledKernel n p ∧
      rescaledKernel n p ≤ Real.exp (-(p.1 + p.2) / 2)

def SquaredErrorConvergence : Prop :=
  Tendsto (fun n => ∫ p, (rescaledKernel n p - limitingKernel p) ^ 2
    ∂quadrantMeasure) atTop (𝓝 0)

/-- Integrability is proved, rather than required as an extra hypothesis. -/
def KernelMemLp : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜],
    (∀ n : ℕ, 2 ≤ n → MemLp (fun p => (rescaledKernel n p : 𝕜)) 2 quadrantMeasure) ∧
      MemLp (fun p => (limitingKernel p : 𝕜)) 2 quadrantMeasure

def KernelL2Convergence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜]
    (hq : ∀ n : ℕ, 2 ≤ n → MemLp (fun p => (rescaledKernel n p : 𝕜)) 2 quadrantMeasure)
    (hf : MemLp (fun p => (limitingKernel p : 𝕜)) 2 quadrantMeasure),
    Tendsto (fun n : ℕ => (hq (n + 2) (by omega)).toLp
      (fun p => (rescaledKernel (n + 2) p : 𝕜)))
      atTop (𝓝 (hf.toLp (fun p => (limitingKernel p : 𝕜))))

def KernelOperatorConvergence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜]
    (hq : ∀ n : ℕ, 2 ≤ n → MemLp (fun p => (rescaledKernel n p : 𝕜)) 2 quadrantMeasure)
    (hf : MemLp (fun p => (limitingKernel p : 𝕜)) 2 quadrantMeasure),
    Tendsto (fun n : ℕ => L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure
      ((hq (n + 2) (by omega)).toLp (fun p => (rescaledKernel (n + 2) p : 𝕜))))
      atTop (𝓝 (L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure
        (hf.toLp (fun p => (limitingKernel p : 𝕜)))))

def LimitingOperatorNorm : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜]
    (hf : MemLp (fun p => (limitingKernel p : 𝕜)) 2 quadrantMeasure),
    ‖L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure
      (hf.toLp (fun p => (limitingKernel p : 𝕜)))‖ = 1 / 2

/-- The usual Hilbert–Schmidt norm is sqrt of the finite extended square sum.
Finiteness of every error operator is part of the conclusion. -/
def HilbertSchmidtConvergence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜]
    (hq : ∀ n : ℕ, 2 ≤ n → MemLp (fun p => (rescaledKernel n p : 𝕜)) 2 quadrantMeasure)
    (hf : MemLp (fun p => (limitingKernel p : 𝕜)) 2 quadrantMeasure),
    let A := fun n : ℕ => L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure
      ((hq (n + 2) (by omega)).toLp (fun p => (rescaledKernel (n + 2) p : 𝕜)))
    let B := L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure
      (hf.toLp (fun p => (limitingKernel p : 𝕜)))
    (∀ n, ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue
      (A n - B)) ∧
    Tendsto (fun n => Real.sqrt
      (ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue
        (A n - B)).toReal) atTop (𝓝 0)

/-- The bridge to the original operator. This is a theorem to prove, not a
hypothesis of the sharp asymptotic. It includes arbitrary interval lengths. -/
def RescaledNormIdentity : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T → ∀ n : ℕ, 2 ≤ n →
    ∀ hq : MemLp (fun p => (rescaledKernel n p : 𝕜)) 2 quadrantMeasure,
    ‖L2KernelSpec.OperatorValue halfLineMeasure halfLineMeasure (hq.toLp _)‖ =
      (n.factorial : ℝ) * ‖VolterraSingularSystemSpec.operator 𝕜 T ^ n‖ / T ^ n

/-- The source's sharp constant, for the actual iterated integration operator.
Equivalently, the ratio to T^n/(2 n!) tends to one. -/
def NormalizedPowerNormLimit : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T →
    Tendsto (fun n : ℕ => (n.factorial : ℝ) *
      ‖VolterraSingularSystemSpec.operator 𝕜 T ^ n‖ / T ^ n)
      atTop (𝓝 (1 / 2))

def PowerNormAsymptotic : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T →
    Tendsto (fun n : ℕ => ‖VolterraSingularSystemSpec.operator 𝕜 T ^ n‖ /
      (T ^ n / (2 * (n.factorial : ℝ)))) atTop (𝓝 1)

def NormalizedLimitFromRescaledNormIdentity : Prop :=
  RescaledNormIdentity → NormalizedPowerNormLimit

def AsymptoticFromNormalizedLimit : Prop :=
  NormalizedPowerNormLimit → PowerNormAsymptotic

end ExpandedFA.PartV.VolterraPowerAsymptoticSpec
