import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.ReflexiveMeasureRange
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-!
Independent statements for `fa2:p4:vector-radon-nikodym`, paper.tex:20861–20923.
The scalar field is real or complex, the measure is sigma-finite, and the
ambient reflexive Banach space need not be separable. `VectorMeasure` uses
countable additivity in norm. Its native variation is the finite-partition
variation identified in the upstream specification. Integrability and a.e.
strong measurability are the native interfaces identified with the paper's
Bochner definitions upstream. Neither completeness of the measure nor
separability of the ambient space is an extra hypothesis.
-/

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
universe u v

namespace ExpandedFA.PartIV.VectorRadonNikodymSpec

/-- The complete Radon–Nikodym conclusion, including both forms of the
variation identity on every measurable set, and ordinary a.e. uniqueness. -/
def Representation : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {Y : Type v}
    [MeasurableSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [CompleteSpace Y], P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 Y →
    ∀ (μ : Measure X) [SigmaFinite μ] (m : VectorMeasure X Y),
      m.variation univ < ∞ →
      (∀ A, MeasurableSet A → μ A = 0 → m A = 0) →
      letI : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ 𝕜 Y
      ∃ g : X → Y, Integrable g μ ∧
        (∀ x, g x ∈ ReflexiveMeasureRangeSpec.rangeSpan 𝕜 m) ∧
        (∀ A, MeasurableSet A → m A = ∫ x in A, g x ∂μ) ∧
        (∀ A, MeasurableSet A →
          m.variation A = ∫⁻ x in A, ‖g x‖ₑ ∂μ ∧
          m.variation.real A = ∫ x in A, ‖g x‖ ∂μ) ∧
        ∀ f : X → Y, Integrable f μ →
          (∀ A, MeasurableSet A → m A = ∫ x in A, f x ∂μ) → f =ᵐ[μ] g

/-- Finishing a density construction does not require reflexivity or
sigma-finiteness. The construction of the density is the substantive step. -/
def DensityConsequences : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (μ : Measure X) (m : VectorMeasure X Y) (g : X → Y),
    Integrable g μ → (∀ A, MeasurableSet A → m A = ∫ x in A, g x ∂μ) →
      (∀ A, MeasurableSet A →
        m.variation A = ∫⁻ x in A, ‖g x‖ₑ ∂μ ∧
        m.variation.real A = ∫ x in A, ‖g x‖ ∂μ) ∧
      ∀ f : X → Y, Integrable f μ →
        (∀ A, MeasurableSet A → m A = ∫ x in A, f x ∂μ) → f =ᵐ[μ] g

/-- The separable closed range span has norm separable dual because it is
reflexive. There is no ambient separability hypothesis. -/
def DualSeparability : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {Y : Type v}
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    [SeparableSpace Y], P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 Y →
      SeparableSpace (Y →L[𝕜] 𝕜)

/-- Completion preserves the a.e. Bochner functions, their p-seminorms for
every p (including infinity), membership, and their equality relation. Thus
the same a.e. classes with the same norms form all of the Bochner spaces. -/
def CompletionInvariant : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [NormedAddCommGroup Y]
    (μ : Measure X) (f : X → Y),
    (AEStronglyMeasurable f μ ↔
      @AEStronglyMeasurable X Y _
        (inferInstanceAs (MeasurableSpace (NullMeasurableSpace X μ)))
        (inferInstanceAs (MeasurableSpace (NullMeasurableSpace X μ))) f μ.completion) ∧
    (∀ p : ℝ≥0∞, eLpNorm f p μ = eLpNorm f p μ.completion) ∧
    (∀ p : ℝ≥0∞, MemLp f p μ ↔
      @MemLp X Y (inferInstanceAs (MeasurableSpace (NullMeasurableSpace X μ))) _ _ f p μ.completion) ∧
    (∀ g : X → Y, f =ᵐ[μ] g ↔ f =ᵐ[μ.completion] g)

/-- Scalar RN packaged linearly in the test functional, with one integrable
majorant for the scalar representatives. This statement has no reflexivity
or separability assumption and does not assert a vector-valued density. -/
def ScalarDensityConstruction : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {Y : Type v}
    [MeasurableSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [CompleteSpace Y] (μ : Measure X) [SigmaFinite μ] (m : VectorMeasure X Y),
    m.variation univ < ∞ →
    (∀ A, MeasurableSet A → μ A = 0 → m A = 0) →
    ∃ h : X → ℝ, Integrable h μ ∧ (∀ x, 0 ≤ h x) ∧
      ∃ T : (Y →L[𝕜] 𝕜) →ₗ[𝕜] Lp 𝕜 1 μ,
        ∀ ℓ : Y →L[𝕜] 𝕜,
          (∀ᵐ x ∂μ, ‖T ℓ x‖ ≤ ‖ℓ‖ * h x) ∧
          ∀ A, MeasurableSet A → (∫ x in A, T ℓ x ∂μ) = ℓ (m A)

/-- An abstract reconstruction problem, independent of vector measures and
of scalar Radon–Nikodym. A single null set for countably many relations and
bounds gives a bounded element of the bidual pointwise. Reflexivity and
Pettis measurability then produce an integrable vector representative. -/
def BidualDensityReconstruction : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {Y : Type v}
    [MeasurableSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [CompleteSpace Y] [SeparableSpace Y] [SeparableSpace (Y →L[𝕜] 𝕜)],
    P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 Y →
    ∀ (μ : Measure X) (h : X → ℝ), Integrable h μ → (∀ x, 0 ≤ h x) →
      ∀ T : (Y →L[𝕜] 𝕜) →ₗ[𝕜] Lp 𝕜 1 μ,
        (∀ ℓ, ∀ᵐ x ∂μ, ‖T ℓ x‖ ≤ ‖ℓ‖ * h x) →
        letI : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ 𝕜 Y
        ∃ g : X → Y, Integrable g μ ∧
          ∀ ℓ : Y →L[𝕜] 𝕜, (fun x => ℓ (g x)) =ᵐ[μ] T ℓ

def Assembly : Prop :=
  ScalarDensityConstruction.{u,v} → BidualDensityReconstruction.{u,v} → Representation.{u,v}

end ExpandedFA.PartIV.VectorRadonNikodymSpec
