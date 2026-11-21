import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.ContinuousMap.Lattice

/-! Independent interface for paper.tex, `fa2:p1:positive-integral-completion`.
The quotient is represented by the range in L¹ of continuous functions. The
first isomorphism theorem identifies this range with the algebraic null-space
quotient; the required kernel and norm identities identify its norm with ℓ|f|.
No full-support, countability, or nonemptiness hypothesis is imposed.
-/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
universe u
namespace ExpandedFA.Supplements.PositiveIntegralCompletionSpec

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]

abbrev continuousToL1 : C(K, ℝ) →L[ℝ] Lp ℝ 1 μ := ContinuousMap.toLp 1 μ ℝ

/-- A concrete model of the algebraic quotient by the L¹ null space. -/
abbrev IntegralQuotient := LinearMap.range (continuousToL1 μ).toLinearMap

abbrev quotientMap : C(K, ℝ) →ₗ[ℝ] IntegralQuotient μ :=
  (continuousToL1 μ).toLinearMap.rangeRestrict

/-- Explicit first-isomorphism bridge; the kernel is identified with ℓ|f|=0
in `QuotientIdentification`, rather than being silently assumed so. -/
def algebraicQuotientEquiv :
    (C(K, ℝ) ⧸ LinearMap.ker (continuousToL1 μ).toLinearMap) ≃ₗ[ℝ]
      IntegralQuotient μ :=
  (continuousToL1 μ).toLinearMap.quotKerEquivRange

abbrev IntegralCompletion := UniformSpace.Completion (IntegralQuotient μ)

abbrev embed : C(K, ℝ) →ₗ[ℝ] IntegralCompletion μ :=
  (UniformSpace.Completion.toComplₗᵢ : IntegralQuotient μ →ₗᵢ[ℝ] _).toLinearMap.comp
    (quotientMap μ)

/-- The cone is defined intrinsically by norm closure of nonnegative continuous
functions, before any completion equivalence is chosen. -/
def positiveCone : Set (IntegralCompletion μ) :=
  closure {z | ∃ f : C(K, ℝ), (∀ x, 0 ≤ f x) ∧ embed μ f = z}

def completionLE (z w : IntegralCompletion μ) : Prop := w - z ∈ positiveCone μ

/-- Lipschitz calculus in the completion: continuous extension from C(K).
This is a property of an operation, with uniqueness required below. -/
def ExtendsCalculus (q : ℝ → ℝ) (T : IntegralCompletion μ → IntegralCompletion μ) : Prop :=
  Continuous T ∧ ∀ (f : C(K, ℝ)) (hq : Continuous q),
    T (embed μ f) = embed μ ((⟨q, hq⟩ : C(ℝ, ℝ)).comp f)

/-- An algebraic positive real functional and its finite regular representing
measure. The measurable structure is the Borel structure. -/
def Represents (ℓ : C(K, ℝ) →ₗ[ℝ] ℝ) : Prop :=
  (∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ ℓ f) ∧
  FunctionSpaces.PositiveRadonRepresentationSpec.PositiveRadon μ ∧
  ∀ f : C(K, ℝ), ℓ f = ∫ x, f x ∂μ

/-- The range model is exactly the quotient in the source, with its specified
norm, not the uniform quotient norm. -/
def QuotientIdentification : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (ℓ : C(K, ℝ) →ₗ[ℝ] ℝ), Represents μ ℓ →
    (∀ f g : C(K, ℝ), quotientMap μ f = quotientMap μ g ↔ ℓ |f - g| = 0) ∧
    (∀ f : C(K, ℝ), ‖quotientMap μ f‖ = ℓ |f|) ∧
    Function.Surjective (quotientMap μ)

/-- Explicit bridge from the literal algebraic null-space quotient to its
normed range model. The transported norm of each class is ℓ|f|. -/
def NullQuotientBridge : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (ℓ : C(K, ℝ) →ₗ[ℝ] ℝ), Represents μ ℓ →
    ∃ N : Submodule ℝ C(K, ℝ),
      (∀ f : C(K, ℝ), f ∈ N ↔ ℓ |f| = 0) ∧
      ∃ e : (C(K, ℝ) ⧸ N) ≃ₗ[ℝ] IntegralQuotient μ,
        (∀ f, e (N.mkQ f) = quotientMap μ f) ∧
        (∀ f, ‖e (N.mkQ f)‖ = ℓ |f|)

/-- Canonical linear isometric identification of the actual metric completion.
The intertwining property determines the equivalence uniquely. -/
def CompletionIdentification : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ],
    FunctionSpaces.PositiveRadonRepresentationSpec.PositiveRadon μ →
    ∃! e : IntegralCompletion μ ≃ₗᵢ[ℝ] Lp ℝ 1 μ,
      ∀ f : C(K, ℝ), e (embed μ f) = continuousToL1 μ f

/-- Integration is the unique continuous extension of ℓ to the completion. -/
def IntegrationExtension : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (ℓ : C(K, ℝ) →ₗ[ℝ] ℝ), Represents μ ℓ →
    ∀ e : IntegralCompletion μ ≃ₗᵢ[ℝ] Lp ℝ 1 μ,
      (∀ f : C(K, ℝ), e (embed μ f) = continuousToL1 μ f) →
      ∃! I : IntegralCompletion μ →L[ℝ] ℝ,
        (∀ f : C(K, ℝ), I (embed μ f) = ℓ f) ∧
        (∀ z, I z = ∫ x, e z x ∂μ)

/-- The intrinsic closed cone and its difference order agree with a.e. order. -/
def OrderIdentification : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (e : IntegralCompletion μ ≃ₗᵢ[ℝ] Lp ℝ 1 μ),
    (∀ f : C(K, ℝ), e (embed μ f) = continuousToL1 μ f) →
    (∀ z, z ∈ positiveCone μ ↔ ∀ᵐ x ∂μ, 0 ≤ e z x) ∧
    (∀ z w, completionLE μ z w ↔ ∀ᵐ x ∂μ, e z x ≤ e w x)

/-- All scalar Lipschitz maps, including maps with q(0) ≠ 0, extend with the
same Lipschitz bound and have the a.e. pointwise interpretation. -/
def LipschitzCalculus : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (e : IntegralCompletion μ ≃ₗᵢ[ℝ] Lp ℝ 1 μ),
    (∀ f : C(K, ℝ), e (embed μ f) = continuousToL1 μ f) →
    ∀ (q : ℝ → ℝ) (c : ℝ≥0), LipschitzWith c q →
      ∃! T : IntegralCompletion μ → IntegralCompletion μ,
        ExtendsCalculus μ q T ∧ LipschitzWith c T ∧
        ∀ z, e (T z) =ᵐ[μ] fun x => q (e z x)

/-- Absolute value is the unique continuous extension of the continuous-function
absolute value and realizes the native L¹ lattice absolute value. -/
def AbsoluteValue : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (e : IntegralCompletion μ ≃ₗᵢ[ℝ] Lp ℝ 1 μ),
    (∀ f : C(K, ℝ), e (embed μ f) = continuousToL1 μ f) →
    ∃! A : IntegralCompletion μ → IntegralCompletion μ,
      ExtendsCalculus μ (fun t => |t|) A ∧ LipschitzWith 1 A ∧
      ∀ z, e (A z) = |e z|

/-- Increasing L¹ sequences with integrals bounded above have an L¹ supremum,
are a.e. convergent to it, and converge in norm. No nonnegativity is assumed.
`IsLUB` states the pointwise supremum only a.e., so exceptional divergence on
null sets does not incorrectly require a finite everywhere supremum. -/
def MonotoneConvergence : Prop :=
  ∀ (K : Type u) [MeasurableSpace K] (μ : Measure K) (f : ℕ → Lp ℝ 1 μ),
    (∀ n, f n ≤ f (n + 1)) →
    BddAbove (Set.range fun n => ∫ x, f n x ∂μ) →
    ∃ g : Lp ℝ 1 μ,
      (∀ᵐ x ∂μ, IsLUB (Set.range fun n => f n x) (g x)) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) ∧
      Tendsto f atTop (𝓝 g) ∧
      Tendsto (fun n => ‖g - f n‖) atTop (𝓝 0)

/-- The monotone convergence assertion in the intrinsic completion order,
with the limit identified as the pointwise a.e. supremum. -/
def CompletionMonotoneConvergence : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (e : IntegralCompletion μ ≃ₗᵢ[ℝ] Lp ℝ 1 μ),
    (∀ f : C(K, ℝ), e (embed μ f) = continuousToL1 μ f) →
    ∀ f : ℕ → IntegralCompletion μ,
      (∀ n, completionLE μ (f n) (f (n + 1))) →
      BddAbove (Set.range fun n => ∫ x, e (f n) x ∂μ) →
      ∃ g : IntegralCompletion μ,
        (∀ᵐ x ∂μ, IsLUB (Set.range fun n => e (f n) x) (e g x)) ∧
        (∀ᵐ x ∂μ, Tendsto (fun n => e (f n) x) atTop (𝓝 (e g x))) ∧
        Tendsto f atTop (𝓝 g) ∧
        Tendsto (fun n => ‖g - f n‖) atTop (𝓝 0)

/-- All clauses of the assigned corollary, with the same canonical embedding. -/
def IntegralCompletionTheorem : Prop :=
  QuotientIdentification.{u} ∧ NullQuotientBridge.{u} ∧ CompletionIdentification.{u} ∧
  IntegrationExtension.{u} ∧ OrderIdentification.{u} ∧ LipschitzCalculus.{u} ∧
  AbsoluteValue.{u} ∧ MonotoneConvergence.{u} ∧ CompletionMonotoneConvergence.{u}

end ExpandedFA.Supplements.PositiveIntegralCompletionSpec
