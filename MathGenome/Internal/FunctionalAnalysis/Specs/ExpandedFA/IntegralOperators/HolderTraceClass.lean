import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.HolderSingularTail
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.RegularizedEigenvalueProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Independent specifications for fa2:p2:holder-trace-class.
The measures are ordinary Lebesgue measures, without probability rescaling.
Products and sums run over all actual nonzero eigenvalues with algebraic multiplicity.
The finite-subset net formulation includes finite and empty spectra. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.IntegralOperators.HolderTraceClass.Spec
open HolderSingularTail.Spec ContinuousTraceDiagonal.Spec
open TraceIdeals.TraceClassDefinitions.Spec TraceIdeals.Lidskii.Spec
open FredholmDeterminant.ClassicalDefinitions.Spec

/-- The full trace and unregularized determinant conclusion. Absolute product
convergence means summability of the deviations of its factors from one. -/
def SpectralConclusion {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (ν : Measure Q) [IsFiniteMeasure ν]
    (k : C(Q × Q, ℂ)) : Prop :=
  let T := continuousKernelOperator ν k
  TraceValue T = ∫ t, k (t,t) ∂ν ∧
  Summable (fun i : EigenvalueIndex T => ‖eigenvalue T i‖) ∧
  HasSum (eigenvalue T) (∫ t, k (t,t) ∂ν) ∧
  (∀ z : ℂ,
    Summable (fun i : EigenvalueIndex T => ‖(1 - z * eigenvalue T i) - 1‖) ∧
    HasProd (fun i : EigenvalueIndex T => 1 - z * eigenvalue T i)
      (FredholmDeterminantValue ν k z)) ∧
  (∀ R : ℝ, 0 ≤ R → TendstoUniformlyOn
    (fun s : Finset (EigenvalueIndex T) => fun z : ℂ => ∏ i ∈ s, (1 - z * eigenvalue T i))
    (FredholmDeterminantValue ν k) atTop (Metric.closedBall 0 R))

/-- A general assembly theorem, also used for the interval conclusion. -/
def TraceClassSpectral : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (ν : Measure Q) [IsFiniteMeasure ν] (k : C(Q × Q, ℂ)),
    IsTraceClassValue (continuousKernelOperator ν k) → SpectralConclusion ν k

def FirstVariable : Prop :=
  ∀ (k : C(I × I, ℂ)) (α H : ℝ),
    1 / 2 < α → α ≤ 1 → HolderFirst k α H →
    IsTraceClassValue (kernel k) ∧
    TraceNormValue (kernel k) ≤ ‖kernelClass k‖ + H / (1 - (2 : ℝ) ^ (1 / 2 - α)) ∧
    SpectralConclusion μ k

def SecondVariable : Prop :=
  ∀ (k : C(I × I, ℂ)) (α H : ℝ),
    1 / 2 < α → α ≤ 1 → HolderSecond k α H →
    IsTraceClassValue (kernel k) ∧
    TraceNormValue (kernel k) ≤ ‖kernelClass k‖ + H / (1 - (2 : ℝ) ^ (1 / 2 - α)) ∧
    SpectralConclusion μ k

abbrev square : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- C¹ on the closed square uses derivatives within the square, so no
extension to a neighborhood is assumed. -/
def C1Quantitative : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (k : C(I × I, 𝕜)) (f : ℝ × ℝ → 𝕜),
    (∀ p : I × I, f (p.1.val, p.2.val) = k p) → ContDiffOn ℝ 1 f square →
    ∃ H : ℝ, HolderFirst k 1 H ∧ IsTraceClassValue (kernel k) ∧
      TraceNormValue (kernel k) ≤ ‖kernelClass k‖ +
        H / (1 - (2 : ℝ) ^ (1 / 2 - (1 : ℝ)))

def ContinuouslyDifferentiable : Prop :=
  ∀ (k : C(I × I, ℂ)) (f : ℝ × ℝ → ℂ),
    (∀ p : I × I, f (p.1.val, p.2.val) = k p) → ContDiffOn ℝ 1 f square →
    (∃ H : ℝ, HolderFirst k 1 H ∧
      TraceNormValue (kernel k) ≤ ‖kernelClass k‖ + H / (1 - (2 : ℝ) ^ (1 / 2 - (1 : ℝ)))) ∧
    IsTraceClassValue (kernel k) ∧ SpectralConclusion μ k

def Smooth : Prop :=
  ∀ (k : C(I × I, ℂ)) (f : ℝ × ℝ → ℂ),
    (∀ p : I × I, f (p.1.val, p.2.val) = k p) → ContDiffOn ℝ ⊤ f square →
    IsTraceClassValue (kernel k) ∧ SpectralConclusion μ k


abbrev Interval (a b : ℝ) := Set.Icc a b
abbrev intervalMeasure (a b : ℝ) : Measure (Interval a b) :=
  (volume : Measure ℝ).comap Subtype.val

instance interval_finite (a b : ℝ) : IsFiniteMeasure (intervalMeasure a b) := by
  constructor
  change (volume.comap (Subtype.val : Interval a b → ℝ)) Set.univ < ∞
  rw [comap_subtype_coe_apply measurableSet_Icc, Set.image_univ, Subtype.range_coe,
    Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-- Ordinary L² kernel norm on [a,b]². The transformed kernel is L times
k(a+Ls,a+Lt), so its Hölder constant is H L^(α+1). -/
abbrev intervalKernelClass {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}
    (k : C(Interval a b × Interval a b, 𝕜)) :=
  ContinuousMap.toLp (E := 𝕜) (𝕜 := 𝕜) 2 ((intervalMeasure a b).prod (intervalMeasure a b)) k

def IntervalFirstVariable : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (k : C(Interval a b × Interval a b, ℂ)) (α H : ℝ),
    1 / 2 < α → α ≤ 1 →
    (∀ x x' y : Interval a b, ‖k (x,y) - k (x',y)‖ ≤ H * |(x : ℝ) - (x' : ℝ)| ^ α) →
    let T := continuousKernelOperator (intervalMeasure a b) k
    IsTraceClassValue T ∧
    TraceNormValue T ≤ ‖intervalKernelClass k‖ +
      H * (b-a) ^ (α+1) / (1 - (2 : ℝ) ^ (1 / 2 - α)) ∧
    SpectralConclusion (intervalMeasure a b) k

def IntervalSecondVariable : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (k : C(Interval a b × Interval a b, ℂ)) (α H : ℝ),
    1 / 2 < α → α ≤ 1 →
    (∀ x y y' : Interval a b, ‖k (x,y) - k (x,y')‖ ≤ H * |(y : ℝ) - (y' : ℝ)| ^ α) →
    let T := continuousKernelOperator (intervalMeasure a b) k
    IsTraceClassValue T ∧
    TraceNormValue T ≤ ‖intervalKernelClass k‖ +
      H * (b-a) ^ (α+1) / (1 - (2 : ℝ) ^ (1 / 2 - α)) ∧
    SpectralConclusion (intervalMeasure a b) k

/-- Required actual affine transport, not a formal assertion of invariance.
The L² unitary has the square-root Jacobian; neither measure is normalized. -/
def AffineTransport : Prop :=
  ∀ (a b : ℝ), a < b → ∀ k : C(Interval a b × Interval a b, ℂ),
    ∃ φ : C(I, Interval a b),
      (∀ t : I, (φ t : ℝ) = a + (b-a) * (t : ℝ)) ∧
      ∃ q : C(I × I, ℂ),
        (∀ p : I × I, q p = (b-a : ℂ) * k (φ p.1, φ p.2)) ∧
        ∃ U : Lp ℂ 2 (intervalMeasure a b) ≃ₗᵢ[ℂ] L2 ℂ,
          (∀ f, (U f : I → ℂ) =ᵐ[μ] fun t => (Real.sqrt (b-a) : ℂ) * f (φ t)) ∧
          (∀ f, U (continuousKernelOperator (intervalMeasure a b) k f) = kernel q (U f)) ∧
          (IsTraceClassValue (kernel q) ↔
            IsTraceClassValue (continuousKernelOperator (intervalMeasure a b) k)) ∧
          (IsTraceClassValue (kernel q) → TraceNormValue (kernel q) =
            TraceNormValue (continuousKernelOperator (intervalMeasure a b) k)) ∧
          ‖kernelClass q‖ = ‖intervalKernelClass k‖ ∧
          (∀ α H : ℝ, 1 / 2 < α → α ≤ 1 →
            (∀ x x' y : Interval a b, ‖k (x,y) - k (x',y)‖ ≤ H * |(x : ℝ) - (x' : ℝ)| ^ α) →
            HolderFirst q α (H * (b-a) ^ (α+1))) ∧
          (∀ α H : ℝ, 1 / 2 < α → α ≤ 1 →
            (∀ x y y' : Interval a b, ‖k (x,y) - k (x,y')‖ ≤ H * |(y : ℝ) - (y' : ℝ)| ^ α) →
            HolderSecond q α (H * (b-a) ^ (α+1)))

def IntervalContinuouslyDifferentiable : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (k : C(Interval a b × Interval a b, ℂ)) (f : ℝ × ℝ → ℂ),
    (∀ p : Interval a b × Interval a b, f (p.1.val, p.2.val) = k p) →
    ContDiffOn ℝ 1 f (Set.Icc a b ×ˢ Set.Icc a b) →
    IsTraceClassValue (continuousKernelOperator (intervalMeasure a b) k) ∧
    SpectralConclusion (intervalMeasure a b) k

def IntervalSmooth : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (k : C(Interval a b × Interval a b, ℂ)) (f : ℝ × ℝ → ℂ),
    (∀ p : Interval a b × Interval a b, f (p.1.val, p.2.val) = k p) →
    ContDiffOn ℝ ⊤ f (Set.Icc a b ×ˢ Set.Icc a b) →
    IsTraceClassValue (continuousKernelOperator (intervalMeasure a b) k) ∧
    SpectralConclusion (intervalMeasure a b) k

/-- Assembly implications, separate from the unconditional interval statements. -/
def IntervalFirstAssembly : Prop := AffineTransport → IntervalFirstVariable
def IntervalSecondAssembly : Prop := AffineTransport → IntervalSecondVariable
def IntervalC1Assembly : Prop := IntervalFirstVariable → IntervalContinuouslyDifferentiable
def IntervalSmoothAssembly : Prop := IntervalContinuouslyDifferentiable → IntervalSmooth

/-- The actual integral operator on the original real- or complex-valued L²
space. This abbreviates the same canonical kernel assignment as the existing
complex interval statements. It is not restriction of scalars on complex L². -/
abbrev intervalKernelOperator {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}
    (k : C(Interval a b × Interval a b, 𝕜)) :
    Lp 𝕜 2 (intervalMeasure a b) →L[𝕜] Lp 𝕜 2 (intervalMeasure a b) :=
  ExpandedFA.PartV.L2KernelSpec.OperatorValue
    (intervalMeasure a b) (intervalMeasure a b) (intervalKernelClass k)

/-- Scalar-generic sufficient condition on every nondegenerate compact
interval. The underlying L² space uses ordinary Lebesgue measure. -/
def ScalarIntervalFirstVariable : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ), a < b →
    ∀ (k : C(Interval a b × Interval a b, 𝕜)) (α H : ℝ),
    1 / 2 < α → α ≤ 1 →
    (∀ x x' y : Interval a b,
      ‖k (x,y) - k (x',y)‖ ≤ H * |(x : ℝ) - (x' : ℝ)| ^ α) →
    IsTraceClassValue (intervalKernelOperator k) ∧
    TraceNormValue (intervalKernelOperator k) ≤ ‖intervalKernelClass k‖ +
      H * (b-a) ^ (α+1) / (1 - (2 : ℝ) ^ (1 / 2 - α))

/-- The same transported constant for regularity in the second variable. -/
def ScalarIntervalSecondVariable : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ), a < b →
    ∀ (k : C(Interval a b × Interval a b, 𝕜)) (α H : ℝ),
    1 / 2 < α → α ≤ 1 →
    (∀ x y y' : Interval a b,
      ‖k (x,y) - k (x,y')‖ ≤ H * |(y : ℝ) - (y' : ℝ)| ^ α) →
    IsTraceClassValue (intervalKernelOperator k) ∧
    TraceNormValue (intervalKernelOperator k) ≤ ‖intervalKernelClass k‖ +
      H * (b-a) ^ (α+1) / (1 - (2 : ℝ) ^ (1 / 2 - α))

/-- Concrete affine L² transport for either scalar field, with the
square-root Jacobian and the scalar-linear intertwining of actual operators.
The scaled kernel has Hölder constant H (b-a)^(α+1). -/
def ScalarAffineTransport : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ), a < b →
    ∀ k : C(Interval a b × Interval a b, 𝕜),
    ∃ φ : C(I, Interval a b),
      (∀ t : I, (φ t : ℝ) = a + (b-a) * (t : ℝ)) ∧
      ∃ q : C(I × I, 𝕜),
        (∀ p : I × I, q p = (b-a : 𝕜) * k (φ p.1, φ p.2)) ∧
        ∃ U : Lp 𝕜 2 (intervalMeasure a b) ≃ₗᵢ[𝕜] L2 𝕜,
          (∀ f, (U f : I → 𝕜) =ᵐ[μ]
            fun t => (Real.sqrt (b-a) : 𝕜) * f (φ t)) ∧
          (∀ f, U (intervalKernelOperator k f) = kernel q (U f)) ∧
          (IsTraceClassValue (kernel q) ↔ IsTraceClassValue (intervalKernelOperator k)) ∧
          (IsTraceClassValue (kernel q) → TraceNormValue (kernel q) =
            TraceNormValue (intervalKernelOperator k)) ∧
          ‖kernelClass q‖ = ‖intervalKernelClass k‖ ∧
          (∀ α H : ℝ, 1 / 2 < α → α ≤ 1 →
            (∀ x x' y : Interval a b,
              ‖k (x,y) - k (x',y)‖ ≤ H * |(x : ℝ) - (x' : ℝ)| ^ α) →
            HolderFirst q α (H * (b-a) ^ (α+1))) ∧
          (∀ α H : ℝ, 1 / 2 < α → α ≤ 1 →
            (∀ x y y' : Interval a b,
              ‖k (x,y) - k (x,y')‖ ≤ H * |(y : ℝ) - (y' : ℝ)| ^ α) →
            HolderSecond q α (H * (b-a) ^ (α+1)))

/-- C¹ within the closed interval square gives the scalar-generic
trace-class sufficient condition and its quantitative Lipschitz bound. -/
def ScalarIntervalContinuouslyDifferentiable : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ), a < b →
    ∀ (k : C(Interval a b × Interval a b, 𝕜)) (f : ℝ × ℝ → 𝕜),
    (∀ p : Interval a b × Interval a b, f (p.1.val, p.2.val) = k p) →
    ContDiffOn ℝ 1 f (Set.Icc a b ×ˢ Set.Icc a b) →
    ∃ H : ℝ,
      (∀ x x' y : Interval a b,
        ‖k (x,y) - k (x',y)‖ ≤ H * |(x : ℝ) - (x' : ℝ)|) ∧
      IsTraceClassValue (intervalKernelOperator k) ∧
      TraceNormValue (intervalKernelOperator k) ≤ ‖intervalKernelClass k‖ +
        H * (b-a) ^ (2 : ℝ) / (1 - (2 : ℝ) ^ (1 / 2 - (1 : ℝ)))

open scoped ContDiff in
/-- Smooth kernels on a closed interval square are trace class on the
actual L² space for either scalar field. -/
def ScalarIntervalSmooth : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ), a < b →
    ∀ (k : C(Interval a b × Interval a b, 𝕜)) (f : ℝ × ℝ → 𝕜),
    (∀ p : Interval a b × Interval a b, f (p.1.val, p.2.val) = k p) →
    ContDiffOn ℝ ∞ f (Set.Icc a b ×ˢ Set.Icc a b) →
    IsTraceClassValue (intervalKernelOperator k)

/-- The real interval trace identity, applied after the sufficient conditions
above. Its general compact-space premise is allocated to Mercer.RealDiagonalTrace;
this specialization must establish full support of the ordinary interval measure. -/
def RealIntervalDiagonalTrace : Prop :=
  ∀ (a b : ℝ), a < b → ∀ k : C(Interval a b × Interval a b, ℝ),
    IsTraceClassValue (intervalKernelOperator k) →
    TraceValue (intervalKernelOperator k) = ∫ t, k (t,t) ∂(intervalMeasure a b)

/-- Zero-length and empty intervals retain their ordinary zero Lebesgue
measure; these cases require no affine inverse or positivity of b-a. -/
def ScalarDegenerateInterval : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ), b ≤ a →
    ∀ k : C(Interval a b × Interval a b, 𝕜),
    intervalKernelOperator k = 0 ∧
    IsTraceClassValue (intervalKernelOperator k) ∧
    TraceNormValue (intervalKernelOperator k) = 0 ∧
    TraceValue (intervalKernelOperator k) = 0 ∧
    (∫ t, k (t,t) ∂(intervalMeasure a b)) = 0

end ExpandedFA.IntegralOperators.HolderTraceClass.Spec
