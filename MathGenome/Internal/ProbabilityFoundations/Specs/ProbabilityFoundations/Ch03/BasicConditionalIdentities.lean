import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-! Proposition 3.3, paper.tex 867–897. The specified probability space and
its sub-sigma-algebras are arbitrary and need not be complete. Real inputs are
integrable; extended nonnegative inputs may have infinite expectation.
The two tower orders and preservation of the extended integral are included. -/

open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch03.BasicConditionalIdentities

universe u

open Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

def realConditionalExpectation_linearType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X Y : Ω → ℝ), Integrable X P → Integrable Y P → ∀ (a b : ℝ),
      realConditionalExpectationValue (F := F) G P (fun ω => a * X ω + b * Y ω) =ᵐ[P]
        (fun ω => a * realConditionalExpectationValue (F := F) G P X ω +
          b * realConditionalExpectationValue (F := F) G P Y ω)

def realConditionalExpectation_monoType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X Y : Ω → ℝ), Integrable X P → Integrable Y P → X ≤ᵐ[P] Y →
      realConditionalExpectationValue (F := F) G P X ≤ᵐ[P] realConditionalExpectationValue (F := F) G P Y

def realConditionalExpectation_nonnegType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), Integrable X P → (0 ≤ᵐ[P] X) →
      0 ≤ᵐ[P] realConditionalExpectationValue (F := F) G P X

def realConditionalExpectation_fixedType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), Measurable[G] X → Integrable X P →
      realConditionalExpectationValue (F := F) G P X =ᵐ[P] X

def realConditionalExpectation_towerType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H : MeasurableSpace Ω), H ≤ G → ∀ (X : Ω → ℝ), Integrable X P →
      realConditionalExpectationValue (F := F) H P (realConditionalExpectationValue (F := F) G P X) =ᵐ[P]
        realConditionalExpectationValue (F := F) H P X

def realConditionalExpectation_tower_reverseType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H : MeasurableSpace Ω), H ≤ G → ∀ (X : Ω → ℝ), Integrable X P →
      realConditionalExpectationValue (F := F) G P (realConditionalExpectationValue (F := F) H P X) =ᵐ[P]
        realConditionalExpectationValue (F := F) H P X

def integral_realConditionalExpectationType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), Integrable X P →
      (∫ ω, realConditionalExpectationValue (F := F) G P X ω ∂P) = ∫ ω, X ω ∂P

def nonnegativeConditionalExpectation_monoType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X Y : Ω → ℝ≥0∞), Measurable[F] X → Measurable[F] Y → X ≤ᵐ[P] Y →
      nonnegativeConditionalExpectationValue (F := F) G P X ≤ᵐ[P] nonnegativeConditionalExpectationValue (F := F) G P Y

def nonnegativeConditionalExpectation_addType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X Y : Ω → ℝ≥0∞), Measurable[F] X → Measurable[F] Y →
      nonnegativeConditionalExpectationValue (F := F) G P (fun ω => X ω + Y ω) =ᵐ[P]
        (fun ω => nonnegativeConditionalExpectationValue (F := F) G P X ω +
          nonnegativeConditionalExpectationValue (F := F) G P Y ω)

def nonnegativeConditionalExpectation_fixedType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ≥0∞), Measurable[G] X →
      nonnegativeConditionalExpectationValue (F := F) G P X =ᵐ[P] X

def lintegral_nonnegativeConditionalExpectationType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ≥0∞), Measurable[F] X →
      (∫⁻ ω, nonnegativeConditionalExpectationValue (F := F) G P X ω ∂P) = ∫⁻ ω, X ω ∂P

def nonnegativeConditionalExpectation_towerType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H : MeasurableSpace Ω), H ≤ G → ∀ (X : Ω → ℝ≥0∞), Measurable[F] X →
      nonnegativeConditionalExpectationValue (F := F) H P (nonnegativeConditionalExpectationValue (F := F) G P X) =ᵐ[P]
        nonnegativeConditionalExpectationValue (F := F) H P X

def nonnegativeConditionalExpectation_tower_reverseType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (H : MeasurableSpace Ω), H ≤ G → ∀ (X : Ω → ℝ≥0∞), Measurable[F] X →
      nonnegativeConditionalExpectationValue (F := F) G P (nonnegativeConditionalExpectationValue (F := F) H P X) =ᵐ[P]
        nonnegativeConditionalExpectationValue (F := F) H P X

end Specs.ProbabilityFoundations.Ch03.BasicConditionalIdentities
