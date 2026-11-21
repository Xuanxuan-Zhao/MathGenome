import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.BasicConditionalIdentities
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.NonnegativeConditionalExistsUnique

/-! Proposition 3.3, paper.tex 867–897. The specified probability space and
its sub-sigma-algebras are arbitrary and need not be complete. Real inputs are
integrable; extended nonnegative inputs may have infinite expectation.
The two tower orders and preservation of the extended integral are included. -/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch03

universe u

theorem realConditionalExpectation_linear :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X Y : Ω → ℝ), Integrable X P → Integrable Y P → ∀ (a b : ℝ),
      realConditionalExpectation (F := F) G P (fun ω => a * X ω + b * Y ω) =ᵐ[P]
        (fun ω => a * realConditionalExpectation (F := F) G P X ω +
          b * realConditionalExpectation (F := F) G P Y ω) := by
  intro Ω G F P _ _hGF X Y hX hY a b
  have hadd := condExp_add (hX.const_mul a) (hY.const_mul b) G
  have ha := condExp_smul a X G (μ := P)
  have hb := condExp_smul b Y G (μ := P)
  filter_upwards [hadd, ha, hb] with ω hsum hleft hright
  exact hsum.trans (congrArg₂ (· + ·) hleft hright)

theorem realConditionalExpectation_mono :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X Y : Ω → ℝ), Integrable X P → Integrable Y P → X ≤ᵐ[P] Y →
      realConditionalExpectation (F := F) G P X ≤ᵐ[P] realConditionalExpectation (F := F) G P Y := by
  intro Ω G F P _ _hGF X Y hX hY hXY
  exact condExp_mono hX hY hXY

theorem realConditionalExpectation_nonneg :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), Integrable X P → (0 ≤ᵐ[P] X) →
      0 ≤ᵐ[P] realConditionalExpectation (F := F) G P X := by
  intro Ω G F P _ _hGF X _hX hpos
  exact condExp_nonneg hpos

theorem realConditionalExpectation_fixed :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), Measurable[G] X → Integrable X P →
      realConditionalExpectation (F := F) G P X =ᵐ[P] X := by
  intro Ω G F P _ hGF X hXm hX
  exact Filter.EventuallyEq.of_eq
    (condExp_of_stronglyMeasurable hGF hXm.stronglyMeasurable hX)

theorem realConditionalExpectation_tower :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H : MeasurableSpace Ω), H ≤ G → ∀ (X : Ω → ℝ), Integrable X P →
      realConditionalExpectation (F := F) H P (realConditionalExpectation (F := F) G P X) =ᵐ[P]
        realConditionalExpectation (F := F) H P X := by
  intro Ω G F P _ hGF H hHG X _hX
  exact condExp_condExp_of_le hHG hGF

theorem realConditionalExpectation_tower_reverse :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H : MeasurableSpace Ω), H ≤ G → ∀ (X : Ω → ℝ), Integrable X P →
      realConditionalExpectation (F := F) G P (realConditionalExpectation (F := F) H P X) =ᵐ[P]
        realConditionalExpectation (F := F) H P X := by
  intro Ω G F P _ hGF H hHG X _hX
  exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable hGF
    (stronglyMeasurable_condExp.mono hHG) integrable_condExp)

theorem integral_realConditionalExpectation :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), Integrable X P →
      (∫ ω, realConditionalExpectation (F := F) G P X ω ∂P) = ∫ ω, X ω ∂P := by
  intro Ω G F P _ hGF X _hX
  exact integral_condExp hGF

theorem nonnegativeConditionalExpectation_mono :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X Y : Ω → ℝ≥0∞), Measurable[F] X → Measurable[F] Y → X ≤ᵐ[P] Y →
      nonnegativeConditionalExpectation (F := F) G P X ≤ᵐ[P] nonnegativeConditionalExpectation (F := F) G P Y := by
  intro Ω G F P _ _hGF X Y _hXm _hYm hXY
  exact condLExp_mono hXY

theorem nonnegativeConditionalExpectation_add :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X Y : Ω → ℝ≥0∞), Measurable[F] X → Measurable[F] Y →
      nonnegativeConditionalExpectation (F := F) G P (fun ω => X ω + Y ω) =ᵐ[P]
        (fun ω => nonnegativeConditionalExpectation (F := F) G P X ω +
          nonnegativeConditionalExpectation (F := F) G P Y ω) := by
  intro Ω G F P _ _hGF X Y hXm _hYm
  exact condLExp_add_left Y hXm.aemeasurable

theorem nonnegativeConditionalExpectation_fixed :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ≥0∞), Measurable[G] X →
      nonnegativeConditionalExpectation (F := F) G P X =ᵐ[P] X := by
  intro Ω G F P _ hGF X hXm
  exact Filter.EventuallyEq.of_eq (condLExp_eq_self hGF P hXm)

theorem lintegral_nonnegativeConditionalExpectation :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ≥0∞), Measurable[F] X →
      (∫⁻ ω, nonnegativeConditionalExpectation (F := F) G P X ω ∂P) = ∫⁻ ω, X ω ∂P := by
  intro Ω G F P _ hGF X _hXm
  exact lintegral_condLExp hGF P X

theorem nonnegativeConditionalExpectation_tower :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H : MeasurableSpace Ω), H ≤ G → ∀ (X : Ω → ℝ≥0∞), Measurable[F] X →
      nonnegativeConditionalExpectation (F := F) H P (nonnegativeConditionalExpectation (F := F) G P X) =ᵐ[P]
        nonnegativeConditionalExpectation (F := F) H P X := by
  intro Ω G F P _ hGF H hHG X hXm
  have hHF : H ≤ F := hHG.trans hGF
  have hGX := nonnegativeConditionalExpectation_isVersion (F := F) G P hGF X hXm
  have hHX := nonnegativeConditionalExpectation_isVersion (F := F) H P hHF X hXm
  have hHGX := nonnegativeConditionalExpectation_isVersion (F := F) H P hHF
    (nonnegativeConditionalExpectation (F := F) G P X) (hGX.1.mono hGF le_rfl)
  apply nonnegativeConditionalExpectationVersion_ae_unique (F := F) H P hHF X _ _ hXm
    ⟨hHGX.1, ?_⟩ hHX
  intro A hA
  exact (hHGX.2 A hA).trans (hGX.2 A (hHG A hA))

theorem nonnegativeConditionalExpectation_tower_reverse :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H : MeasurableSpace Ω), H ≤ G → ∀ (X : Ω → ℝ≥0∞), Measurable[F] X →
      nonnegativeConditionalExpectation (F := F) G P (nonnegativeConditionalExpectation (F := F) H P X) =ᵐ[P]
        nonnegativeConditionalExpectation (F := F) H P X := by
  intro Ω G F P _ hGF H hHG X _hXm
  exact Filter.EventuallyEq.of_eq (condLExp_eq_self hGF P
    ((measurable_condLExp H P X).mono hHG le_rfl))

end ProbabilityFoundations.Ch03
