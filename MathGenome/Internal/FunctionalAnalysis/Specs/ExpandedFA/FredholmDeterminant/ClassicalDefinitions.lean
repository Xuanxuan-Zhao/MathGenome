import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.ContinuousKernelCompactness
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Instances.Matrix

/-!
The definitions at the start of the classical Fredholm chapter of paper.tex
(lines 10996–11013 in this copy). These are the continuous-kernel series,
without any trace-class assumption. The index set for Qⁿ is `Fin n` and the
augmented matrix uses `Fin.cons` to put x and y before the integration nodes.

We use finite positive Borel measures; this includes every finite positive
Radon measure in the manuscript. No full-support, positive-mass or nonempty-Q
hypothesis is imposed. The scalar series are defined by `tsum`; their convergence
and the continuous-map-valued interpretation of B are subsequent obligations.
-/

open MeasureTheory
universe u
namespace ExpandedFA.FredholmDeterminant.ClassicalDefinitions.Spec

/-- The original bounded operator on C(Q), reused from the shared interface. -/
def KernelOperatorType :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ], C(Q × Q, ℂ) → C(Q, ℂ) →L[ℂ] C(Q, ℂ)

noncomputable def KernelOperatorValue : KernelOperatorType.{u} :=
  fun μ _ k => ExpandedFA.PartV.ContinuousKernel.Spec.KernelOperatorValue μ k

/-- m is real-valued total mass, not an extra parameter or a probability normalization. -/
def MeasureMassType := ∀ {Q : Type u} [MeasurableSpace Q], Measure Q → ℝ
noncomputable def MeasureMassValue : MeasureMassType.{u} := fun μ => μ.real Set.univ

/-- The canonical supremum norm, including the empty-domain case. -/
def KernelBoundType :=
  ∀ {Q : Type u} [TopologicalSpace Q] [CompactSpace Q], C(Q × Q, ℂ) → ℝ
noncomputable def KernelBoundValue : KernelBoundType.{u} := fun k => ‖k‖

/-- The genuine n-fold product measure, also when n = 0 or Q is empty. -/
def MeasurePowerType :=
  ∀ {Q : Type u} [MeasurableSpace Q], Measure Q → (n : ℕ) → Measure (Fin n → Q)
noncomputable def MeasurePowerValue : MeasurePowerType.{u} :=
  fun μ n => Measure.pi (fun _ : Fin n => μ)

def KernelMatrixType :=
  ∀ {Q : Type u} [TopologicalSpace Q], C(Q × Q, ℂ) →
    (n : ℕ) → (Fin n → Q) → Matrix (Fin n) (Fin n) ℂ

def KernelMatrixValue : KernelMatrixType.{u} :=
  fun k _ t i j => k (t i, t j)

def AugmentedMatrixType :=
  ∀ {Q : Type u} [TopologicalSpace Q], C(Q × Q, ℂ) →
    (n : ℕ) → Q → Q → (Fin n → Q) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ

def AugmentedMatrixValue : AugmentedMatrixType.{u} :=
  fun {Q} _ k _n x y t i j => k (Fin.cons (α := fun _ => Q) x t i,
    Fin.cons (α := fun _ => Q) y t j)

def DeterminantIntegralType :=
  ∀ {Q : Type u} [TopologicalSpace Q] [MeasurableSpace Q],
    Measure Q → C(Q × Q, ℂ) → ℕ → ℂ
noncomputable def DeterminantIntegralValue : DeterminantIntegralType.{u} :=
  fun μ k n => ∫ t : Fin n → _, (KernelMatrixValue k n t).det ∂MeasurePowerValue μ n

def MinorIntegralType :=
  ∀ {Q : Type u} [TopologicalSpace Q] [MeasurableSpace Q],
    Measure Q → C(Q × Q, ℂ) → ℕ → Q → Q → ℂ
noncomputable def MinorIntegralValue : MinorIntegralType.{u} :=
  fun μ k n x y =>
    ∫ t : Fin n → _, (AugmentedMatrixValue k n x y t).det ∂MeasurePowerValue μ n

def DeterminantTermType :=
  ∀ {Q : Type u} [TopologicalSpace Q] [MeasurableSpace Q],
    Measure Q → C(Q × Q, ℂ) → ℂ → ℕ → ℂ
noncomputable def DeterminantTermValue : DeterminantTermType.{u} :=
  fun μ k z n => (-z) ^ n / (n.factorial : ℂ) * DeterminantIntegralValue μ k n

def MinorTermType :=
  ∀ {Q : Type u} [TopologicalSpace Q] [MeasurableSpace Q],
    Measure Q → C(Q × Q, ℂ) → Q → Q → ℂ → ℕ → ℂ
noncomputable def MinorTermValue : MinorTermType.{u} :=
  fun μ k x y z n => (-z) ^ n / (n.factorial : ℂ) * MinorIntegralValue μ k n x y

def FredholmDeterminantType :=
  ∀ {Q : Type u} [TopologicalSpace Q] [MeasurableSpace Q],
    Measure Q → C(Q × Q, ℂ) → ℂ → ℂ
noncomputable def FredholmDeterminantValue : FredholmDeterminantType.{u} :=
  fun μ k z => ∑' n : ℕ, DeterminantTermValue μ k z n

def FredholmMinorType :=
  ∀ {Q : Type u} [TopologicalSpace Q] [MeasurableSpace Q],
    Measure Q → C(Q × Q, ℂ) → Q → Q → ℂ → ℂ
noncomputable def FredholmMinorValue : FredholmMinorType.{u} :=
  fun μ k x y z => ∑' n : ℕ, MinorTermValue μ k x y z n

/-- The matrix is exactly the displayed augmented matrix, including all four blocks. -/
def AugmentedMatrixEntries : Prop :=
  ∀ {Q : Type u} [TopologicalSpace Q] (k : C(Q × Q, ℂ))
    (n : ℕ) (x y : Q) (t : Fin n → Q),
    AugmentedMatrixValue k n x y t 0 0 = k (x, y) ∧
    (∀ j : Fin n, AugmentedMatrixValue k n x y t 0 j.succ = k (x, t j)) ∧
    (∀ i : Fin n, AugmentedMatrixValue k n x y t i.succ 0 = k (t i, y)) ∧
    (∀ i j : Fin n, AugmentedMatrixValue k n x y t i.succ j.succ = k (t i, t j))

/-- Q⁰ has mass one, even when μ(Q) = 0 or Q is empty. -/
def ProductMass : Prop :=
  ∀ {Q : Type u} [MeasurableSpace Q] (μ : Measure Q) [IsFiniteMeasure μ] (n : ℕ),
    MeasurePowerValue μ n Set.univ = μ Set.univ ^ n

/-- The conventions at n = 0 are consequences of the ordinary determinant and product measure. -/
def ZerothTerms : Prop :=
  ∀ {Q : Type u} [TopologicalSpace Q] [MeasurableSpace Q] (μ : Measure Q)
    (k : C(Q × Q, ℂ)),
    (∀ t : Fin 0 → Q, (KernelMatrixValue k 0 t).det = 1) ∧
    DeterminantIntegralValue μ k 0 = 1 ∧
    (∀ z, DeterminantTermValue μ k z 0 = 1) ∧
    (∀ (x y : Q) (t : Fin 0 → Q), (AugmentedMatrixValue k 0 x y t).det = k (x, y)) ∧
    (∀ x y, MinorIntegralValue μ k 0 x y = k (x, y)) ∧
    (∀ x y z, MinorTermValue μ k x y z 0 = k (x, y))

/-- The integrals in both definitions are actual integrals of integrable functions. -/
def IntegrableDeterminants : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)) (n : ℕ),
    Integrable (fun t : Fin n → Q => (KernelMatrixValue k n t).det) (MeasurePowerValue μ n) ∧
    ∀ x y, Integrable (fun t : Fin n → Q => (AugmentedMatrixValue k n x y t).det)
      (MeasurePowerValue μ n)

/-- The operator formula, mass and supremum bound refer to the same original data. -/
def DataIdentification : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)),
    (∀ (f : C(Q, ℂ)) x, KernelOperatorValue μ k f x = ∫ y, k (x, y) * f y ∂μ) ∧
    MeasureMassValue μ = (μ Set.univ).toReal ∧ KernelBoundValue k = ‖k‖

end ExpandedFA.FredholmDeterminant.ClassicalDefinitions.Spec
