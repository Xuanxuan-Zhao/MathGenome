import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.HolderTraceClass
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.RealComplexification
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.RealExteriorDefinitions

/-! Real kernels are applied on genuine real L². Their spectral data are those
of the corresponding operator on genuine complex L², with full algebraic
multiplicity. All interval measures below are ordinary Lebesgue measures. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.IntegralOperators.RealHolderSpectralBridge.Spec
open HolderTraceClass.Spec
open TraceIdeals.TraceClassDefinitions.Spec TraceIdeals.Lidskii.Spec

/-- Scalar inclusion of a continuous real kernel, with the same domain. -/
def complexKernel {a b : ℝ} (k : C(Interval a b × Interval a b, ℝ)) :
    C(Interval a b × Interval a b, ℂ) :=
  ⟨fun p => (k p : ℂ), Complex.continuous_ofReal.comp k.continuous⟩

abbrev realOperator {a b : ℝ} (k : C(Interval a b × Interval a b, ℝ)) :=
  intervalKernelOperator k
abbrev complexOperator {a b : ℝ} (k : C(Interval a b × Interval a b, ℝ)) :=
  intervalKernelOperator (complexKernel k)

/-- The quotient formula and unitary geometry must be established, rather than
assuming a certificate identifying the two complex Hilbert spaces. -/
def L2Complexification : Prop :=
  ∀ a b : ℝ, ∃ J : TraceIdeals.RealComplexification.Space (Lp ℝ 2 (intervalMeasure a b))
      ≃ₗᵢ[ℂ] Lp ℂ 2 (intervalMeasure a b),
    (∀ p, (J p : Interval a b → ℂ) =ᵐ[intervalMeasure a b]
      fun t => (p.1 t : ℂ) + Complex.I * (p.2 t : ℂ)) ∧
    ∀ (k : C(Interval a b × Interval a b, ℝ)) p,
      J (TraceIdeals.RealComplexification.Spec.operator (realOperator k) p) =
        complexOperator k (J p)

def TraceTransport : Prop :=
  ∀ (a b : ℝ) (k : C(Interval a b × Interval a b, ℝ)),
    IsTraceClassValue (realOperator k) →
    IsTraceClassValue (complexOperator k) ∧
    TraceNormValue (complexOperator k) = TraceNormValue (realOperator k) ∧
    TraceValue (complexOperator k) = ((TraceValue (𝕜 := ℝ) (realOperator k) : ℝ) : ℂ)

/-- The real trace, all complexification eigenvalues, and the classical
complex-kernel Fredholm series. Finite and empty spectra use the same nets. -/
def SpectralConclusion {a b : ℝ} (k : C(Interval a b × Interval a b, ℝ)) : Prop :=
  let T := complexOperator k
  let d := ∫ t, k (t,t) ∂(intervalMeasure a b)
  TraceValue (realOperator k) = d ∧
  TraceValue T = (d : ℂ) ∧
  Summable (fun i : EigenvalueIndex T => ‖eigenvalue T i‖) ∧
  HasSum (eigenvalue T) (d : ℂ) ∧
  (∀ z : ℂ,
    FredholmDeterminant.ClassicalDefinitions.Spec.FredholmDeterminantValue
        (intervalMeasure a b) (complexKernel k) z =
      FredholmDeterminant.RealExteriorDefinitions.Spec.ComplexParameterDeterminantValue
        (realOperator k) (-z) ∧
    Summable (fun i : EigenvalueIndex T => ‖(1 - z * eigenvalue T i) - 1‖) ∧
    HasProd (fun i : EigenvalueIndex T => 1 - z * eigenvalue T i)
      (FredholmDeterminant.ClassicalDefinitions.Spec.FredholmDeterminantValue
        (intervalMeasure a b) (complexKernel k) z)) ∧
  (∀ R : ℝ, 0 ≤ R → TendstoUniformlyOn
    (fun s : Finset (EigenvalueIndex T) => fun z : ℂ => ∏ i ∈ s, (1 - z * eigenvalue T i))
    (FredholmDeterminant.ClassicalDefinitions.Spec.FredholmDeterminantValue
      (intervalMeasure a b) (complexKernel k)) atTop (Metric.closedBall 0 R))

def TraceClassSpectral : Prop :=
  ∀ (a b : ℝ) (k : C(Interval a b × Interval a b, ℝ)),
    IsTraceClassValue (realOperator k) → SpectralConclusion k

def FirstVariable : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (k : C(Interval a b × Interval a b, ℝ)) (α H : ℝ),
    1 / 2 < α → α ≤ 1 →
    (∀ x x' y : Interval a b,
      ‖k (x,y) - k (x',y)‖ ≤ H * |(x : ℝ) - (x' : ℝ)| ^ α) →
    IsTraceClassValue (realOperator k) ∧
    TraceNormValue (realOperator k) ≤ ‖intervalKernelClass k‖ +
      H * (b-a) ^ (α+1) / (1 - (2 : ℝ) ^ (1 / 2 - α)) ∧ SpectralConclusion k

def SecondVariable : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (k : C(Interval a b × Interval a b, ℝ)) (α H : ℝ),
    1 / 2 < α → α ≤ 1 →
    (∀ x y y' : Interval a b,
      ‖k (x,y) - k (x,y')‖ ≤ H * |(y : ℝ) - (y' : ℝ)| ^ α) →
    IsTraceClassValue (realOperator k) ∧
    TraceNormValue (realOperator k) ≤ ‖intervalKernelClass k‖ +
      H * (b-a) ^ (α+1) / (1 - (2 : ℝ) ^ (1 / 2 - α)) ∧ SpectralConclusion k

def ContinuouslyDifferentiable : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (k : C(Interval a b × Interval a b, ℝ)) (f : ℝ × ℝ → ℝ),
    (∀ p : Interval a b × Interval a b, f (p.1.val, p.2.val) = k p) →
    ContDiffOn ℝ 1 f (Set.Icc a b ×ˢ Set.Icc a b) →
    (∃ H : ℝ,
      (∀ x x' y : Interval a b,
        ‖k (x,y) - k (x',y)‖ ≤ H * |(x : ℝ) - (x' : ℝ)|) ∧
      TraceNormValue (realOperator k) ≤ ‖intervalKernelClass k‖ +
        H * (b-a) ^ (2 : ℝ) / (1 - (2 : ℝ) ^ (1 / 2 - (1 : ℝ)))) ∧
    IsTraceClassValue (realOperator k) ∧ SpectralConclusion k

open scoped ContDiff in
def Smooth : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (k : C(Interval a b × Interval a b, ℝ)) (f : ℝ × ℝ → ℝ),
    (∀ p : Interval a b × Interval a b, f (p.1.val, p.2.val) = k p) →
    ContDiffOn ℝ ∞ f (Set.Icc a b ×ˢ Set.Icc a b) →
    IsTraceClassValue (realOperator k) ∧ SpectralConclusion k

def DegenerateInterval : Prop :=
  ∀ (a b : ℝ), b ≤ a → ∀ k : C(Interval a b × Interval a b, ℝ),
    realOperator k = 0 ∧ complexOperator k = 0 ∧
    TraceNormValue (realOperator k) = 0 ∧
    TraceValue (realOperator k) = 0 ∧
    (∫ t, k (t,t) ∂(intervalMeasure a b)) = 0 ∧
    IsEmpty (EigenvalueIndex (complexOperator k)) ∧
    spectrum ℂ (complexOperator k) \ {0} = ∅ ∧
    (∀ z : ℂ,
      FredholmDeterminant.ClassicalDefinitions.Spec.FredholmDeterminantValue
        (intervalMeasure a b) (complexKernel k) z = 1 ∧
      FredholmDeterminant.RealExteriorDefinitions.Spec.ComplexParameterDeterminantValue
        (realOperator k) z = 1) ∧ SpectralConclusion k

end ExpandedFA.IntegralOperators.RealHolderSpectralBridge.Spec
