import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Independent specification of the construction in paper.tex:18378--18395.
The construction works on any metric measure space using balls of positive
finite measure, hence in particular on Euclidean space with Lebesgue measure.
Scalar functions are identified a.e., as in the upstream L¹ space; consequently
support and the L∞ bound are essential support and essential bounds.
The CZ operator assertion is a separate allocated obligation.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology lp
universe u v

namespace ExpandedFA.Hardy.AtomicHardySpaceSpec

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X)

abbrev L1 := ExpandedFA.FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue 𝕜 1 μ

/-- Original atom conditions. Positive finite ball measure is explicit so that
this definition is meaningful on general metric measure spaces as well. -/
def IsAtomValue (f : L1 (𝕜 := 𝕜) μ) : Prop :=
  (∫ x, f x ∂μ) = 0 ∧ ∃ c : X, ∃ r : ℝ,
    0 < r ∧ μ (Metric.ball c r) ≠ 0 ∧ μ (Metric.ball c r) ≠ ∞ ∧
    ∀ᵐ x ∂μ, (x ∉ Metric.ball c r → f x = 0) ∧
      ‖f x‖ ≤ (μ.real (Metric.ball c r))⁻¹

abbrev AtomValue := {f : L1 (𝕜 := 𝕜) μ // IsAtomValue μ f}

/-- The elementary normalization estimate needed to define the bounded
synthesis map. This is a construction proof, not an assumed certificate. -/
private theorem atom_bound (a : AtomValue (𝕜 := 𝕜) μ) : ‖a.val‖ ≤ 1 := by
  rcases a.property.2 with ⟨c, r, hr, hzero, htop, hb⟩
  let B := Metric.ball c r
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hm : μ.real B ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hzero, htop⟩
  have hi : Integrable (B.indicator (fun _ : X => (μ.real B)⁻¹)) μ :=
    (integrable_indicator_iff hB).mpr (integrableOn_const htop)
  rw [MeasureTheory.L1.norm_eq_integral_norm]
  calc
    (∫ x, ‖a.val x‖ ∂μ) ≤ ∫ x, B.indicator (fun _ : X => (μ.real B)⁻¹) x ∂μ := by
      apply integral_mono_ae (MeasureTheory.L1.integrable_coeFn a.val).norm hi
      filter_upwards [hb] with x hx
      by_cases h : x ∈ B
      · simpa [Set.indicator_of_mem h] using hx.2
      · simp [Set.indicator_of_notMem h, hx.1 h]
    _ = 1 := by rw [integral_indicator_const _ hB]; simp [smul_eq_mul, hm]

abbrev CoefficientsValue : Type (max u v) := ℓ¹(AtomValue (𝕜 := 𝕜) μ, 𝕜)

/-- Turn coefficients into a summable L¹-valued family. -/
def weightedAtoms (c : CoefficientsValue (𝕜 := 𝕜) μ) :
    ℓ¹(AtomValue (𝕜 := 𝕜) μ, L1 (𝕜 := 𝕜) μ) :=
  ⟨fun a => c a • a.val, (lp.memℓp c).mono' (fun a => by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (atom_bound μ a))⟩

private theorem weightedAtoms_bound (c : CoefficientsValue (𝕜 := 𝕜) μ) :
    ‖weightedAtoms μ c‖ ≤ ‖c‖ := by
  simp only [lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal),
    ENNReal.toReal_one, Real.rpow_one, one_div_one]
  apply Summable.tsum_le_tsum
  · intro a
    change ‖c a • a.val‖ ≤ ‖c a‖
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (atom_bound μ a)
  · simpa using (lp.memℓp (weightedAtoms μ c)).summable (by simp)
  · simpa using (lp.memℓp c).summable (by simp)

/-- Synthesis indexed by the entire, possibly uncountable, set of atoms. -/
def SynthesisValue : CoefficientsValue (𝕜 := 𝕜) μ →L[𝕜] L1 (𝕜 := 𝕜) μ :=
  (lp.tsumCLM (α := AtomValue (𝕜 := 𝕜) μ) 𝕜 (L1 (𝕜 := 𝕜) μ)).comp
    (LinearMap.mkContinuous
      ({
        toFun := weightedAtoms μ
        map_add' c d := by apply lp.ext; funext a; exact add_smul _ _ _
        map_smul' k c := by
          apply lp.ext
          funext a
          change (k * c a) • a.val = k • (c a • a.val)
          exact mul_smul _ _ _ } :
        CoefficientsValue (𝕜 := 𝕜) μ →ₗ[𝕜]
          ℓ¹(AtomValue (𝕜 := 𝕜) μ, L1 (𝕜 := 𝕜) μ))
      1 (fun c => by simpa using weightedAtoms_bound μ c))

def KernelValue : Submodule 𝕜 (CoefficientsValue (𝕜 := 𝕜) μ) :=
  (SynthesisValue (𝕜 := 𝕜) μ).ker

/-- Quotient norm, not the norm inherited from L¹. -/
abbrev HardyValue := CoefficientsValue (𝕜 := 𝕜) μ ⧸ KernelValue (𝕜 := 𝕜) μ

instance kernelClosed : IsClosed (KernelValue (𝕜 := 𝕜) μ : Set (CoefficientsValue (𝕜 := 𝕜) μ)) :=
  (SynthesisValue μ).isClosed_ker

def EmbeddingValue : HardyValue (𝕜 := 𝕜) μ →L[𝕜] L1 (𝕜 := 𝕜) μ :=
  (KernelValue μ).liftQL (SynthesisValue μ) le_rfl

/-- Atomic norm on the image, as the infimum of absolute coefficient sums. -/
def AtomicNormValue (f : L1 (𝕜 := 𝕜) μ) : ℝ :=
  sInf {r : ℝ | ∃ c : CoefficientsValue μ,
    SynthesisValue μ c = f ∧ (∑' a, ‖c a‖) = r}


def IsAtomType :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    L1 (𝕜 := 𝕜) μ → Prop

def AtomType :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    Type (max u v)

def CoefficientsType :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    Type (max u v)

def SynthesisType :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    CoefficientsValue (𝕜 := 𝕜) μ →L[𝕜] L1 (𝕜 := 𝕜) μ

def HardyType :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    Type (max u v)

def EmbeddingType :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    HardyValue (𝕜 := 𝕜) μ →L[𝕜] L1 (𝕜 := 𝕜) μ

def AtomicNormType :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    L1 (𝕜 := 𝕜) μ → ℝ

def RawAtomRealization : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    ∀ (f : X → 𝕜), AEStronglyMeasurable f μ → (∫ x, f x ∂μ) = 0 →
    (∃ c : X, ∃ r : ℝ, 0 < r ∧ μ (Metric.ball c r) ≠ 0 ∧
      μ (Metric.ball c r) ≠ ∞ ∧ ∀ᵐ x ∂μ,
        (x ∉ Metric.ball c r → f x = 0) ∧ ‖f x‖ ≤ (μ.real (Metric.ball c r))⁻¹) →
    ∃ a : AtomValue (𝕜 := 𝕜) μ, a.val =ᵐ[μ] f

def AtomBound : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    ∀ a : AtomValue (𝕜 := 𝕜) μ, ‖a.val‖ ≤ 1

def CoefficientNorm : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    ∀ c : CoefficientsValue (𝕜 := 𝕜) μ, ‖c‖ = ∑' a, ‖c a‖

def CoefficientSupport : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    ∀ c : CoefficientsValue (𝕜 := 𝕜) μ, (Function.support c).Countable

def SynthesisSeries : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    ∀ c : CoefficientsValue (𝕜 := 𝕜) μ,
    HasSum (fun a => c a • a.val) (SynthesisValue μ c) ∧
    ‖SynthesisValue μ c‖ ≤ ∑' a, ‖c a‖

def KernelClosed : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    IsClosed (KernelValue (𝕜 := 𝕜) μ : Set (CoefficientsValue (𝕜 := 𝕜) μ))

def HardyComplete : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    CompleteSpace (HardyValue (𝕜 := 𝕜) μ)

def EmbeddingProperties : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    Function.Injective (EmbeddingValue (𝕜 := 𝕜) μ) ∧
    ∀ h : HardyValue (𝕜 := 𝕜) μ, ‖EmbeddingValue μ h‖ ≤ ‖h‖

def AtomicRange : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    ∀ f : L1 (𝕜 := 𝕜) μ,
    (∃ h : HardyValue μ, EmbeddingValue μ h = f) ↔
    ∃ c : CoefficientsValue μ, HasSum (fun a => c a • a.val) f

def AtomicNormFormula : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    ∀ h : HardyValue (𝕜 := 𝕜) μ,
    ‖h‖ = AtomicNormValue μ (EmbeddingValue μ h)

def IntegralZero : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    ∀ h : HardyValue (𝕜 := 𝕜) μ,
    (∫ x, EmbeddingValue μ h x ∂μ) = 0

def SequenceSeries : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    ∀ (a : ℕ → AtomValue (𝕜 := 𝕜) μ) (c : ℕ → 𝕜),
    Summable (fun j => ‖c j‖) → ∃ h : HardyValue μ,
      HasSum (fun j => c j • (a j).val) (EmbeddingValue μ h) ∧
      ‖h‖ ≤ ∑' j, ‖c j‖

def CountableRepresentation : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X),
    ∀ h : HardyValue (𝕜 := 𝕜) μ, ∃ c : CoefficientsValue μ,
    (Function.support c).Countable ∧
    HasSum (fun a : Function.support c => c a.val • a.val.val)
      (EmbeddingValue μ h)

/-- Specialization to precisely the Euclidean balls and Lebesgue measure of
paper.tex, without additional measure hypotheses on the atoms. -/
def EuclideanAtomRealization : Prop :=
  ∀ (d : ℕ) {𝕜 : Type v} [RCLike 𝕜] (f : EuclideanSpace ℝ (Fin d) → 𝕜),
    AEStronglyMeasurable f volume → (∫ x, f x) = 0 →
    (∃ c : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ ∀ᵐ x,
      (x ∉ Metric.ball c r → f x = 0) ∧
      ‖f x‖ ≤ (volume.real (Metric.ball c r))⁻¹) →
    ∃ a : AtomValue (𝕜 := 𝕜) (volume : Measure (EuclideanSpace ℝ (Fin d))),
      a.val =ᵐ[volume] f

/-- Reindexing full-set coefficients as an ordinary sequence preserves their
absolute sum. The nonempty dictionary condition only supplies a filler for
unused sequence indices; Euclidean atoms always contain the zero atom. -/
def CoefficientSequence : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X) [Nonempty (AtomValue (𝕜 := 𝕜) μ)]
    (c : CoefficientsValue (𝕜 := 𝕜) μ),
    ∃ a : ℕ → AtomValue (𝕜 := 𝕜) μ, ∃ b : ℕ → 𝕜,
      HasSum (fun j => ‖b j‖) ‖c‖ ∧
      HasSum (fun j => b j • (a j).val) (SynthesisValue μ c)

/-- The sequence definition and its exact coefficient-infimum norm, on the
source's Euclidean domain, allowing arbitrary repetitions of atoms. -/
def EuclideanSequenceNorm : Prop :=
  ∀ (d : ℕ) {𝕜 : Type v} [RCLike 𝕜]
    (h : HardyValue (𝕜 := 𝕜) (volume : Measure (EuclideanSpace ℝ (Fin d)))),
    ‖h‖ = sInf {r : ℝ | ∃ a : ℕ → AtomValue volume, ∃ c : ℕ → 𝕜,
      Summable (fun j => ‖c j‖) ∧
      HasSum (fun j => c j • (a j).val) (EmbeddingValue volume h) ∧
      (∑' j, ‖c j‖) = r}

def EuclideanSequenceRange : Prop :=
  ∀ (d : ℕ) {𝕜 : Type v} [RCLike 𝕜]
    (f : L1 (𝕜 := 𝕜) (volume : Measure (EuclideanSpace ℝ (Fin d)))),
    (∃ h : HardyValue volume, EmbeddingValue volume h = f) ↔
    ∃ a : ℕ → AtomValue volume, ∃ c : ℕ → 𝕜,
      Summable (fun j => ‖c j‖) ∧ HasSum (fun j => c j • (a j).val) f

/-- Every quotient atom has a strongly measurable representative with the
pointwise support and supremum bound used in the source. -/
def AtomRepresentative : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type v} [RCLike 𝕜] (μ : Measure X) (a : AtomValue (𝕜 := 𝕜) μ),
    ∃ f : X → 𝕜, StronglyMeasurable f ∧ f =ᵐ[μ] a.val ∧ (∫ x, f x ∂μ) = 0 ∧
    ∃ c : X, ∃ r : ℝ, 0 < r ∧ μ (Metric.ball c r) ≠ 0 ∧
      μ (Metric.ball c r) ≠ ∞ ∧
      (∀ x, x ∉ Metric.ball c r → f x = 0) ∧
      ∀ x, ‖f x‖ ≤ (μ.real (Metric.ball c r))⁻¹

end ExpandedFA.Hardy.AtomicHardySpaceSpec
