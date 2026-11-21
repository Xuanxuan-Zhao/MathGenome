import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2Kernel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
Independent statements for the positive part of `fa2:p2:mercer`, paper.tex
11637–11689. The general nonpositive diagonal identity is separately allocated.
Both scalar fields, arbitrary finite Borel measures of full support, empty Q,
zero operators, and finite or empty eigenfunction families are included.
The kernel operator is the shared ordinary-product L² integral operator.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace ComplexConjugate Topology
universe u
namespace ExpandedFA.IntegralOperators.MercerExpansion.Spec

variable {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
  [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]

/-- The ordinary a.e. class of the given continuous kernel. -/
abbrev kernelLp (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜)) :
    Lp 𝕜 2 (μ.prod μ) := ContinuousMap.toLp 2 (μ.prod μ) 𝕜 k

/-- No new choice of kernel operator is introduced. -/
abbrev operator (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜)) :
    Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  ExpandedFA.PartV.L2KernelSpec.OperatorValue μ μ (kernelLp μ k)

def Hermitian (k : C(Q × Q, 𝕜)) : Prop :=
  ∀ x y, k (x,y) = conj (k (y,x))

/-- Quadratic-form positivity, rather than pointwise positivity of k. -/
def Positive (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜)) : Prop :=
  ∀ f : Lp 𝕜 2 μ, 0 ≤ RCLike.re ⟪f, operator μ k f⟫_𝕜

/-- Positivity of every finite kernel matrix, with the same conjugate-first
convention as the integral quadratic form. -/
def KernelPositiveSemidefinite (k : C(Q × Q, 𝕜)) : Prop :=
  ∀ c : Q →₀ 𝕜, 0 ≤ RCLike.re
    (c.sum fun x a => c.sum fun y b => conj a * k (x,y) * b)

/-- Full Mercer data. Orthonormality is in L², not in C(Q).
`vector_expansion` ensures that the indexed eigenvectors exhaust the nonzero
spectral part, with multiplicity. Uniform convergence is over finite subsets;
this handles finite and empty families without adding artificial zero eigenvalues. -/
structure SpectralData (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜)) where
  Index : Type
  countable : Countable Index
  eigenvalue : Index → ℝ
  eigenfunction : Index → C(Q, 𝕜)
  positive : ∀ j, 0 < eigenvalue j
  orthonormal : Orthonormal 𝕜 (fun j => ContinuousMap.toLp 2 μ 𝕜 (eigenfunction j))
  eigen_equation : ∀ j,
    operator μ k (ContinuousMap.toLp 2 μ 𝕜 (eigenfunction j)) =
      (eigenvalue j : 𝕜) • ContinuousMap.toLp 2 μ 𝕜 (eigenfunction j)
  vector_expansion : ∀ f : Lp 𝕜 2 μ,
    HasSum (fun j => ((eigenvalue j : 𝕜) *
      ⟪ContinuousMap.toLp 2 μ 𝕜 (eigenfunction j), f⟫_𝕜) •
        ContinuousMap.toLp 2 μ 𝕜 (eigenfunction j)) (operator μ k f)

/-- The spectral data together with the stronger pointwise kernel conclusions. -/
structure Expansion (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜))
    extends SpectralData μ k where
  pointwise : ∀ x y,
    HasSum (fun j => (eigenvalue j : 𝕜) * eigenfunction j x * conj (eigenfunction j y))
      (k (x,y))
  absolute : ∀ x y,
    Summable (fun j => ‖(eigenvalue j : 𝕜) * eigenfunction j x * conj (eigenfunction j y)‖)
  uniform : TendstoUniformly
    (fun s : Finset Index => fun p : Q × Q =>
      ∑ j ∈ s, (eigenvalue j : 𝕜) * eigenfunction j p.1 * conj (eigenfunction j p.2))
    (fun p => k p) atTop
  absolute_uniform : TendstoUniformly
    (fun s : Finset Index => fun p : Q × Q =>
      ∑ j ∈ s, ‖(eigenvalue j : 𝕜) * eigenfunction j p.1 * conj (eigenfunction j p.2)‖)
    (fun p => ∑' j, ‖(eigenvalue j : 𝕜) * eigenfunction j p.1 * conj (eigenfunction j p.2)‖)
    atTop

/-- The L² spectral family can be chosen with continuous representatives. -/
def ContinuousSpectralData : Prop :=
  ∀ {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
    [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜)),
    Hermitian k → Positive μ k → Nonempty (SpectralData μ k)

/-- Parseval in the kernel Hilbert space supplies the diagonal identity.
Finite-matrix positivity is a premise of this helper only; the unconditional
Mercer theorem still has precisely operator positivity as its hypothesis. -/
def DiagonalOfPositiveKernel : Prop :=
  ∀ {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
    [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (k : C(Q × Q, 𝕜)), Hermitian k → KernelPositiveSemidefinite k →
    ∀ D : SpectralData μ k, ∀ x,
      HasSum (fun j => D.eigenvalue j * ‖D.eigenfunction j x‖ ^ 2)
        (RCLike.re (k (x,x)))

/-- Full support recovers a continuous kernel from its canonical L² operator. -/
def ContinuousKernelFaithfulness : Prop :=
  ∀ {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
    [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure],
    Function.Injective (operator (𝕜 := 𝕜) μ)

/-- Analytic final step: a continuous diagonal sum gives uniform absolute
Cauchy tails for the off-diagonal series. No pointwise Mercer identity is assumed. -/
def DiagonalUniformTails : Prop :=
  ∀ {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q] [CompactSpace Q]
    (ι : Type) (a : ι → ℝ) (e : ι → C(Q, 𝕜)) (d : C(Q, ℝ)),
    (∀ i, 0 ≤ a i) →
    (∀ x, HasSum (fun i => a i * ‖e i x‖ ^ 2) (d x)) →
    TendstoUniformly (fun s : Finset ι => fun x => ∑ i ∈ s, a i * ‖e i x‖ ^ 2) d atTop ∧
    ∀ ε : ℝ, 0 < ε → ∃ s : Finset ι, ∀ t : Finset ι, Disjoint t s →
      ∀ x y, ∑ i ∈ t, ‖(a i : 𝕜) * e i x * conj (e i y)‖ < ε

/-- One continuous summand, with the manuscript's conjugate-first convention. -/
def kernelTerm {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
    (a : ℝ) (e : C(Q, 𝕜)) : C(Q × Q, 𝕜) :=
  ⟨fun p => (a : 𝕜) * e p.1 * conj (e p.2),
    (continuous_const.mul (e.continuous.comp continuous_fst)).mul
      (RCLike.continuous_conj.comp (e.continuous.comp continuous_snd))⟩

def absoluteKernelTerm {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
    (a : ℝ) (e : C(Q, 𝕜)) : C(Q × Q, ℝ) :=
  ⟨fun p => ‖kernelTerm a e p‖, by fun_prop⟩

/-- Summability in C(Q×Q) gives uniform convergence of both the kernel series
and the series of absolute values; it does not assert summability of sup norms. -/
def UniformSeriesOfDiagonal : Prop :=
  ∀ {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q] [CompactSpace Q]
    (ι : Type) (a : ι → ℝ) (e : ι → C(Q, 𝕜)) (d : C(Q, ℝ)),
    (∀ i, 0 ≤ a i) →
    (∀ x, HasSum (fun i => a i * ‖e i x‖ ^ 2) (d x)) →
    Summable (fun i => kernelTerm (a i) (e i)) ∧
    Summable (fun i => absoluteKernelTerm (a i) (e i))

/-- The canonical trace and ideal membership from a summable positive
spectral expansion. This is conditional on summability, not a Mercer axiom. -/
def TraceOfSummableSpectralData : Prop :=
  ∀ {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
    [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜)) (D : SpectralData μ k),
    Summable D.eigenvalue →
    TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (operator μ k) ∧
    TraceIdeals.TraceClassDefinitions.Spec.TraceValue (operator μ k) =
      ((∑' j, D.eigenvalue j : ℝ) : 𝕜)

/-- Integration of the pointwise diagonal identity, using normalization in L². -/
def EigenvalueSumOfDiagonal : Prop :=
  ∀ {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
    [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜)) (D : SpectralData μ k),
    (∀ x, HasSum (fun j => D.eigenvalue j * ‖D.eigenfunction j x‖ ^ 2)
      (RCLike.re (k (x,x)))) →
    HasSum D.eigenvalue (∫ x, RCLike.re (k (x,x)) ∂μ)

/-- Assembly from the diagonal identity; the unconditional theorem below
still requires that identity to be proved from the original hypotheses. -/
def MercerOfDiagonal : Prop :=
  ∀ {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
    [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (k : C(Q × Q, 𝕜)), Hermitian k → ∀ D : SpectralData μ k,
    (∀ x, HasSum (fun j => D.eigenvalue j * ‖D.eigenfunction j x‖ ^ 2)
      (RCLike.re (k (x,x)))) →
    Nonempty (Expansion μ k) ∧
      TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (operator μ k) ∧
      TraceIdeals.TraceClassDefinitions.Spec.TraceValue (operator μ k) = ∫ x, k (x,x) ∂μ

/-- The zero integral operator, including every empty-space case. -/
def ZeroOperatorCase : Prop :=
  ∀ {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
    [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] (k : C(Q × Q, 𝕜)),
    operator μ k = 0 → Nonempty (Expansion μ k) ∧
      TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (operator μ k) ∧
      TraceIdeals.TraceClassDefinitions.Spec.TraceValue (operator μ k) = ∫ x, k (x,x) ∂μ

def Mercer : Prop :=
  ∀ {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
    [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] (k : C(Q × Q, 𝕜)),
    Hermitian k → Positive μ k →
      Nonempty (Expansion μ k) ∧
      TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (operator μ k) ∧
      TraceIdeals.TraceClassDefinitions.Spec.TraceValue (operator μ k) =
        ∫ x, k (x,x) ∂μ

/-- Regularity of every nonzero eigenfunction, without positivity. -/
def ContinuousEigenfunctions : Prop :=
  ∀ {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
    [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜))
    (f : Lp 𝕜 2 μ) (a : 𝕜), a ≠ 0 → operator μ k f = a • f →
    ∃ e : C(Q, 𝕜), ContinuousMap.toLp 2 μ 𝕜 e = f ∧
      ∀ x, ∫ y, k (x,y) * e y ∂μ = a * e x

/-- For a positive operator, every nonzero real eigenvalue is strictly positive. -/
def PositiveEigenvalues : Prop :=
  ∀ {Q : Type u} {𝕜 : Type} [RCLike 𝕜] [MetricSpace Q]
    [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜)), Positive μ k →
    ∀ (f : Lp 𝕜 2 μ) (a : ℝ), f ≠ 0 → a ≠ 0 →
      operator μ k f = (a : 𝕜) • f → 0 < a

end ExpandedFA.IntegralOperators.MercerExpansion.Spec
