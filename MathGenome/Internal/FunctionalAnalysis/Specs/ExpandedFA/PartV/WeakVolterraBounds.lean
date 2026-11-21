import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FractionalIntegrals
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Independent types for the power-kernel bounds in `fa2:p5:weak-volterra`.
The amplitude is a continuous function on the actual closed triangle, including
its diagonal. Both scalar fields and the zero-length interval are retained.
The logarithmic and resolvent-kernel clauses are allocated to separate goals.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
universe u v
namespace ExpandedFA.PartV.WeakVolterraBounds.Spec
open ExpandedFA.PartV.FractionalIntegrals.Spec

/-- Coordinates are (output time, integration time). -/
def triangle (T : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 ≤ T}

/-- Extension is used only to write integrals on the ambient real line. -/
def amplitudeValue {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (k : C(triangle T, 𝕜)) (t s : ℝ) : 𝕜 := by
  classical
  exact if h : (t,s) ∈ triangle T then k ⟨(t,s),h⟩ else 0

def weakIntegrand {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (α : ℝ)
    (k : C(triangle T, 𝕜)) (f : ℝ → 𝕜) (t s : ℝ) : 𝕜 :=
  (t-s) ^ (α-1) • (amplitudeValue k t s * f s)

/-- Unnormalized power-kernel integral; its value at time zero is zero. -/
def weakValue {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (α : ℝ)
    (k : C(triangle T, 𝕜)) (f : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  ∫ s in Ioc 0 t, weakIntegrand α k f t s

def ZeroTime : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (α : ℝ)
    (k : C(triangle T, 𝕜)) (f : ℝ → 𝕜), weakValue α k f 0 = 0

def RepresentativeIndependence : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (α : ℝ) (k : C(triangle T, 𝕜)) (f g : ℝ → 𝕜),
    f =ᵐ[intervalMeasure T] g → ∀ t ∈ Icc (0 : ℝ) T,
      (IntegrableOn (weakIntegrand α k f t) (Ioc 0 t) ↔
        IntegrableOn (weakIntegrand α k g t) (Ioc 0 t)) ∧
      weakValue α k f t = weakValue α k g t

/-- Exact specialization to the unnormalized, constant-amplitude integral. -/
def ConstantAmplitude : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (α : ℝ) (c : 𝕜) (f : ℝ → 𝕜), ∀ t ∈ Icc (0 : ℝ) T,
    weakValue α (ContinuousMap.const (triangle T) c) f t = c * powerValue α f t

/-- Exact manuscript bound, with n=0 interpreted by ordinary zero powers. -/
def iterateBound (α T M : ℝ) (n : ℕ) : ℝ :=
  M ^ n * Real.Gamma α ^ n * T ^ ((n : ℝ)*α) / Real.Gamma ((n : ℝ)*α+1)

def GammaSummability : Prop := ∀ {α c : ℝ}, 0 < α → 0 ≤ c →
  Summable (fun n : ℕ => c ^ n / Real.Gamma ((n : ℝ)*α+1))

/-- An analytic consequence of the iterate estimate, not an assumed
certificate in either of the integral-operator construction statements. -/
def NeumannFromBound : Prop := ∀ {𝕜 : Type u} [RCLike 𝕜]
    {A : Type v} [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
    {α T M : ℝ}, 0 < α → 0 ≤ T → 0 ≤ M → ∀ V : A,
    (∀ n : ℕ, ‖V ^ n‖ ≤ iterateBound α T M n) → ∀ z : 𝕜,
    Summable (fun n : ℕ => z ^ n • V ^ n) ∧
    (1 - z • V) * (∑' n : ℕ, z ^ n • V ^ n) = 1 ∧
    (∑' n : ℕ, z ^ n • V ^ n) * (1 - z • V) = 1 ∧
    IsUnit (1 - z • V)

/-- Norm-root quasinilpotence, also over real spaces. -/
def QuasinilpotenceFromBound : Prop := ∀ {A : Type v} [NormedRing A]
    {α T M : ℝ}, 0 < α → 0 ≤ T → 0 ≤ M → ∀ V : A,
    (∀ n : ℕ, ‖V ^ n‖ ≤ iterateBound α T M n) →
    Tendsto (fun n : ℕ => ‖V ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)

def SpectralRadiusFromBound : Prop := ∀ {𝕜 : Type u} [RCLike 𝕜]
    {A : Type v} [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
    {α T M : ℝ}, 0 < α → 0 ≤ T → 0 ≤ M → ∀ V : A,
    (∀ n : ℕ, ‖V ^ n‖ ≤ iterateBound α T M n) → spectralRadius 𝕜 V = 0

/-- Operator-norm Neumann series, a specified two-sided inverse, and
quasinilpotence; no nontriviality assumption on the function space is needed. -/
def ResolventProperties {𝕜 : Type} [RCLike 𝕜] {E : Type}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (V : E →L[𝕜] E) : Prop :=
  Tendsto (fun n : ℕ => ‖V ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) ∧
  spectralRadius 𝕜 V = 0 ∧ ∀ z : 𝕜,
    Summable (fun n : ℕ => z ^ n • V ^ n) ∧
    (1 - z • V) * (∑' n : ℕ, z ^ n • V ^ n) = 1 ∧
    (∑' n : ℕ, z ^ n • V ^ n) * (1 - z • V) = 1 ∧
    IsUnit (1 - z • V)

/-- Bounded construction with the original integral, before compactness. -/
def ContinuousConstruction : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → ∀ hT : 0 ≤ T,
    ∀ (k : C(triangle T, 𝕜)) (M : ℝ), 0 ≤ M → (∀ z, ‖k z‖ ≤ M) →
    ∃ V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜),
      (∀ f (t : Icc (0 : ℝ) T),
        IntegrableOn (weakIntegrand α k (continuousExtension hT f) t) (Ioc 0 (t : ℝ)) ∧
        V f t = weakValue α k (continuousExtension hT f) t) ∧
      ‖V‖ ≤ M * T ^ α / α

/-- Full conclusion on continuous functions, with absolute integrability at
every time and the defining formula on the closed interval. -/
def ContinuousTheorem : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → ∀ hT : 0 ≤ T,
    ∀ (k : C(triangle T, 𝕜)) (M : ℝ), 0 ≤ M → (∀ z, ‖k z‖ ≤ M) →
    ∃ V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜),
      (∀ f (t : Icc (0 : ℝ) T),
        IntegrableOn (weakIntegrand α k (continuousExtension hT f) t) (Ioc 0 (t : ℝ)) ∧
        V f t = weakValue α k (continuousExtension hT f) t) ∧
      IsCompactOperator V ∧
      (∀ n : ℕ, ‖V ^ n‖ ≤ iterateBound α T M n) ∧ ResolventProperties V

/-- Full conclusion on each a.e. quotient, including p=1 and p=infinity.
The integral formula and its absolute existence hold for every MemLp
representative, rather than only for a selected representative. -/
def LpTheorem : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → 0 ≤ T →
    ∀ (k : C(triangle T, 𝕜)) (M : ℝ), 0 ≤ M → (∀ z, ‖k z‖ ≤ M) →
    ∀ p : ℝ≥0∞, ∀ [Fact (1 ≤ p)],
    ∃ V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T),
      (∀ (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)),
        (∀ᵐ t ∂intervalMeasure T, IntegrableOn (weakIntegrand α k f t) (Ioc 0 t)) ∧
        (V (hf.toLp f) : ℝ → 𝕜) =ᵐ[intervalMeasure T] weakValue α k f) ∧
      IsCompactOperator V ∧
      (∀ n : ℕ, ‖V ^ n‖ ≤ iterateBound α T M n) ∧ ResolventProperties V

end ExpandedFA.PartV.WeakVolterraBounds.Spec
