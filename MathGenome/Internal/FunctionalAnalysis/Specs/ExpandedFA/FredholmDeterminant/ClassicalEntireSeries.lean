import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalDefinitions
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The convergence stage of `fa2:p2:classical-fredholm`. The coefficient kernels
are defined by Bochner integration in C(Q × Q), independently of convergence
of the Fredholm series. This avoids assuming continuity of a pointwise tsum.
The hypotheses include the empty space and zero measure. The positive Borel
measure version below in particular includes the source's finite Radon measures.
-/

open MeasureTheory Filter
open scoped Topology
universe u

namespace ExpandedFA.FredholmDeterminant.ClassicalEntireSeries.Spec

namespace Data
open ExpandedFA.FredholmDeterminant.ClassicalDefinitions.Spec

/-- For fixed integration nodes the augmented determinant is a continuous kernel. -/
def augmentedKernel {Q : Type u} [TopologicalSpace Q]
    (k : C(Q × Q, ℂ)) (n : ℕ) (t : Fin n → Q) : C(Q × Q, ℂ) where
  toFun p := (AugmentedMatrixValue k n p.1 p.2 t).det
  continuous_toFun := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply k.continuous.comp
    apply Continuous.prodMk
    · have hc : Continuous (fun p : Q × Q => Fin.cons (α := fun _ => Q) p.1 t) :=
        Continuous.finCons (A := fun _ => Q) continuous_fst continuous_const
      exact (continuous_apply i).comp hc
    · have hc : Continuous (fun p : Q × Q => Fin.cons (α := fun _ => Q) p.2 t) :=
        Continuous.finCons (A := fun _ => Q) continuous_snd continuous_const
      exact (continuous_apply j).comp hc

/-- Bochner-integrated coefficient kernel before multiplying by (-z)^n/n!. -/
noncomputable def minorCoefficient {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] (μ : Measure Q) (k : C(Q × Q, ℂ)) (n : ℕ) :
    C(Q × Q, ℂ) :=
  ∫ t, augmentedKernel k n t ∂MeasurePowerValue μ n

noncomputable def minorKernelTerm {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] (μ : Measure Q) (k : C(Q × Q, ℂ)) (z : ℂ) (n : ℕ) :
    C(Q × Q, ℂ) :=
  ((-z) ^ n / (n.factorial : ℂ)) • minorCoefficient μ k n

noncomputable def minorKernel {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] (μ : Measure Q) (k : C(Q × Q, ℂ)) (z : ℂ) :
    C(Q × Q, ℂ) := ∑' n, minorKernelTerm μ k z n

/-- (sqrt n)^n equals n^(n/2), including n=0 with value one. -/
noncomputable def hadamardBound (M : ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt n) ^ n * M ^ n

noncomputable def determinantMajorant (m M R : ℝ) (n : ℕ) : ℝ :=
  R ^ n / (n.factorial : ℝ) * (hadamardBound M n * m ^ n)

noncomputable def minorMajorant (m M R : ℝ) (n : ℕ) : ℝ :=
  R ^ n / (n.factorial : ℝ) * (hadamardBound M (n + 1) * m ^ n)

end Data

open ExpandedFA.FredholmDeterminant.ClassicalDefinitions.Spec Data

/-- The continuous-kernel-valued version of the accepted pointwise minor. -/
def MinorKernelType :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q],
    Measure Q → C(Q × Q, ℂ) → ℂ → C(Q × Q, ℂ)

noncomputable def MinorKernelValue : MinorKernelType.{u} := @Data.minorKernel

def CoefficientIdentification : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (n : ℕ),
    Integrable (augmentedKernel k n) (MeasurePowerValue μ n) ∧
    (∀ x y, minorCoefficient μ k n (x, y) = MinorIntegralValue μ k n x y) ∧
    ∀ z x y, minorKernelTerm μ k z n (x, y) = MinorTermValue μ k x y z n

def PointwiseHadamardBounds : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] (k : C(Q × Q, ℂ))
    (n : ℕ) (t : Fin n → Q),
    ‖(KernelMatrixValue k n t).det‖ ≤ hadamardBound ‖k‖ n ∧
    ∀ x y, ‖(AugmentedMatrixValue k n x y t).det‖ ≤ hadamardBound ‖k‖ (n + 1)

def IntegralHadamardBounds : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (n : ℕ),
    ‖DeterminantIntegralValue μ k n‖ ≤ hadamardBound ‖k‖ n * MeasureMassValue μ ^ n ∧
    ‖minorCoefficient μ k n‖ ≤ hadamardBound ‖k‖ (n + 1) * MeasureMassValue μ ^ n

def MajorantsSummable : Prop :=
  ∀ (m M R : ℝ), 0 ≤ m → 0 ≤ M → 0 ≤ R →
    Summable (determinantMajorant m M R) ∧ Summable (minorMajorant m M R)

def UniformTermBounds : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ))
    (R : ℝ), 0 ≤ R → ∀ (z : ℂ), ‖z‖ ≤ R → ∀ n,
    ‖DeterminantTermValue μ k z n‖ ≤ determinantMajorant (MeasureMassValue μ) ‖k‖ R n ∧
    ‖minorKernelTerm μ k z n‖ ≤ minorMajorant (MeasureMassValue μ) ‖k‖ R n

def AbsoluteConvergence : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ),
    Summable (fun n => ‖DeterminantTermValue μ k z n‖) ∧
    Summable (fun n => ‖minorKernelTerm μ k z n‖)

/-- Closed disks give local uniform convergence on all parameter sets of bounded norm.
The norm in the second clause is the supremum norm over both kernel variables. -/
def UniformConvergenceOnDisks : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ))
    (R : ℝ), 0 ≤ R →
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, DeterminantTermValue μ k z n)
      (FredholmDeterminantValue μ k) atTop (Metric.closedBall 0 R) ∧
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, minorKernelTerm μ k z n)
      (minorKernel μ k) atTop (Metric.closedBall 0 R)

def MinorKernelIdentification : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ) (x y : Q),
    minorKernel μ k z (x, y) = FredholmMinorValue μ k x y z

def EntireFunctions : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)),
    Differentiable ℂ (FredholmDeterminantValue μ k) ∧
    Differentiable ℂ (minorKernel μ k)

def TermwiseDifferentiation : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (z : ℂ),
    HasSum (fun n => deriv (fun w => DeterminantTermValue μ k w n) z)
      (deriv (FredholmDeterminantValue μ k) z) ∧
    HasSum (fun n => deriv (fun w => minorKernelTerm μ k w n) z)
      (deriv (minorKernel μ k) z)

def ValuesAtZero : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q]
    (μ : Measure Q) (k : C(Q × Q, ℂ)),
    FredholmDeterminantValue μ k 0 = 1 ∧ minorKernel μ k 0 = k

end ExpandedFA.FredholmDeterminant.ClassicalEntireSeries.Spec
