import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.TwoTimeAndExamples
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.PredictableTransforms

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207

namespace PredictableTransforms

abbrev processIncrement : PredictableTransformsSpec.processIncrementType.{u} :=
  @P207.processIncrement.{u}

abbrev predictableTransform : PredictableTransformsSpec.predictableTransformType.{u} :=
  @P207.predictableTransform.{u}

end PredictableTransforms

variable {Ω : Type u}

theorem predictableTransform_zero (H X : ℕ → Ω → ℝ) (ω : Ω) :
    predictableTransform H X 0 ω = 0 := by
  simp [predictableTransform]

theorem predictableTransform_succ (H X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    predictableTransform H X (n + 1) ω =
      predictableTransform H X n ω + H n ω * processIncrement X n ω := by
  simp only [predictableTransform, Finset.sum_range_succ]

theorem processIncrement_predictableTransform (H X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    processIncrement (predictableTransform H X) n ω = H n ω * processIncrement X n ω := by
  simp [processIncrement, predictableTransform_succ]

variable [m : MeasurableSpace Ω]

theorem adapted_predictableTransform (ℱ : Filtration ℕ m) (H X : ℕ → Ω → ℝ)
    (hH : Adapted ℱ H) (hX : Adapted ℱ X) :
    Adapted ℱ (predictableTransform H X) := by
  intro n
  apply Finset.measurable_sum
  intro k hk
  have hkn := Finset.mem_range.mp hk
  exact ((hH k).mono (ℱ.mono hkn.le) le_rfl).mul
    (((hX (k + 1)).mono (ℱ.mono (Nat.succ_le_of_lt hkn)) le_rfl).sub
      ((hX k).mono (ℱ.mono hkn.le) le_rfl))

theorem integrable_predictableTransform (μ : Measure Ω) (H X : ℕ → Ω → ℝ)
    (hprod : ∀ k, Integrable (fun ω => H k ω * processIncrement X k ω) μ)
    (n : ℕ) : Integrable (predictableTransform H X n) μ := by
  exact integrable_finsetSum _ fun k _ => hprod k

theorem integrable_transform_products_of_bounded (μ : Measure Ω)
    (ℱ : Filtration ℕ m) (H X : ℕ → Ω → ℝ)
    (hH : Adapted ℱ H) (hi : ∀ n, Integrable (X n) μ)
    (hb : ∀ k, ∃ C : ℝ, ∀ ω, ‖H k ω‖ ≤ C) (k : ℕ) :
    Integrable (fun ω => H k ω * processIncrement X k ω) μ := by
  obtain ⟨C, hC⟩ := hb k
  exact ((hi (k + 1)).sub (hi k)).bdd_mul
    (((hH k).mono (ℱ.le k) le_rfl).stronglyMeasurable.aestronglyMeasurable)
    (Filter.Eventually.of_forall hC)

theorem martingale_predictableTransform (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (H X : ℕ → Ω → ℝ)
    (hX : IsMartingale X ℱ μ) (hH : Adapted ℱ H)
    (hprod : ∀ k, Integrable (fun ω => H k ω * processIncrement X k ω) μ) :
    IsMartingale (predictableTransform H X) ℱ μ := by
  apply (martingale_iff_library μ ℱ _).mpr
  apply martingale_of_condExp_sub_eq_zero_nat
    (adapted_predictableTransform ℱ H X hH hX.1).stronglyAdapted
    (integrable_predictableTransform μ H X hprod)
  intro k
  have hpull := condExp_mul_of_stronglyMeasurable_left (hH k).stronglyMeasurable
    (hprod k) ((hX.2.1 (k + 1)).sub (hX.2.1 k))
  have hzero : μ[X (k + 1) - X k | ℱ k] =ᵐ[μ] 0 := by
    have hself := condExp_of_stronglyMeasurable (ℱ.le k)
      (hX.1.stronglyAdapted k) (hX.2.1 k)
    filter_upwards [condExp_sub (hX.2.1 (k + 1)) (hX.2.1 k) (ℱ k), hX.2.2 k]
      with ω hs hx
    simpa only [Pi.sub_apply, hself, hx, sub_self, Pi.zero_apply] using hs
  have hd : (predictableTransform H X (k + 1) - predictableTransform H X k) =
      (fun ω => H k ω * processIncrement X k ω) := by
    funext ω
    exact processIncrement_predictableTransform H X k ω
  rw [hd]
  filter_upwards [hpull, hzero] with ω hp hz
  change μ[H k * processIncrement X k | ℱ k] ω = 0
  rw [hp]
  change H k ω * μ[X (k + 1) - X k | ℱ k] ω = 0
  simp only [hz, Pi.zero_apply, mul_zero]

theorem submartingale_predictableTransform (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (H X : ℕ → Ω → ℝ)
    (hX : IsSubmartingale X ℱ μ) (hH : Adapted ℱ H) (hn : ∀ k ω, 0 ≤ H k ω)
    (hprod : ∀ k, Integrable (fun ω => H k ω * processIncrement X k ω) μ) :
    IsSubmartingale (predictableTransform H X) ℱ μ := by
  apply (submartingale_iff_library μ ℱ _).mpr
  apply submartingale_of_condExp_sub_nonneg_nat
    (adapted_predictableTransform ℱ H X hH hX.1).stronglyAdapted
    (integrable_predictableTransform μ H X hprod)
  intro k
  have hpull := condExp_mul_of_stronglyMeasurable_left (hH k).stronglyMeasurable
    (hprod k) ((hX.2.1 (k + 1)).sub (hX.2.1 k))
  have hnonneg := ((submartingale_iff_library μ ℱ X).mp hX).condExp_sub_nonneg k.le_succ
  have hd : (predictableTransform H X (k + 1) - predictableTransform H X k) =
      (fun ω => H k ω * processIncrement X k ω) := by
    funext ω
    exact processIncrement_predictableTransform H X k ω
  rw [hd]
  filter_upwards [hpull, hnonneg] with ω hp hz
  change 0 ≤ μ[H k * processIncrement X k | ℱ k] ω
  rw [hp]
  exact mul_nonneg (hn k ω) hz

theorem martingale_predictableTransform_of_bounded (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (H X : ℕ → Ω → ℝ)
    (hX : IsMartingale X ℱ μ) (hH : Adapted ℱ H)
    (hb : ∀ k, ∃ C : ℝ, ∀ ω, ‖H k ω‖ ≤ C) :
    IsMartingale (predictableTransform H X) ℱ μ :=
  martingale_predictableTransform μ ℱ H X hX hH
    (integrable_transform_products_of_bounded μ ℱ H X hH hX.2.1 hb)

theorem submartingale_predictableTransform_of_bounded (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (H X : ℕ → Ω → ℝ)
    (hX : IsSubmartingale X ℱ μ) (hH : Adapted ℱ H) (hn : ∀ k ω, 0 ≤ H k ω)
    (hb : ∀ k, ∃ C : ℝ, ∀ ω, ‖H k ω‖ ≤ C) :
    IsSubmartingale (predictableTransform H X) ℱ μ :=
  submartingale_predictableTransform μ ℱ H X hX hH hn
    (integrable_transform_products_of_bounded μ ℱ H X hH hX.2.1 hb)

end P207
