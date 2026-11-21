import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-! The definition and bounded real function consequence in paper.tex §4.4,
1209–1217. The specified spaces and sub-sigma-algebra are arbitrary; in
particular there is no standard Borel or completeness assumption. -/

open MeasureTheory
namespace Specs.ProbabilityFoundations.Ch04.ConditionalIndependence
open Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions
universe u v w

def independenceType :=
  ∀ {Ω : Type u} {S : Type v} {T : Type w} (G : MeasurableSpace Ω)
    [F : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T],
    Measure[F] Ω → (Ω → S) → (Ω → T) → Prop

noncomputable def independenceValue : independenceType :=
  fun {_Ω} {_S} {_T} G _F _mS _mT P Y Z => ∀ (B : Set _) (C : Set _), MeasurableSet B → MeasurableSet C →
    realConditionalExpectationValue G P
      ((Y ⁻¹' B ∩ Z ⁻¹' C).indicator (fun _ => (1 : ℝ))) =ᵐ[P]
      (fun ω => realConditionalExpectationValue G P
          ((Y ⁻¹' B).indicator (fun _ => (1 : ℝ))) ω *
        realConditionalExpectationValue G P
          ((Z ⁻¹' C).indicator (fun _ => (1 : ℝ))) ω)

def indicatorVersionsType : Prop :=
  ∀ {Ω : Type u} {S : Type v} {T : Type w} (G : MeasurableSpace Ω)
    [F : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (Y : Ω → S) (Z : Ω → T), Measurable Y → Measurable Z →
    independenceValue G P Y Z →
    ∀ B C, MeasurableSet B → MeasurableSet C → ∀ U V W : Ω → ℝ,
    realVersionValue G P ((Y ⁻¹' B).indicator (fun _ => (1 : ℝ))) U →
    realVersionValue G P ((Z ⁻¹' C).indicator (fun _ => (1 : ℝ))) V →
    realVersionValue G P ((Y ⁻¹' B ∩ Z ⁻¹' C).indicator (fun _ => (1 : ℝ))) W →
    W =ᵐ[P] (fun ω => U ω * V ω)

def boundedFactorizationType : Prop :=
  ∀ {Ω : Type u} {S : Type v} {T : Type w} (G : MeasurableSpace Ω)
    [F : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (Y : Ω → S) (Z : Ω → T), Measurable Y → Measurable Z →
    independenceValue G P Y Z → ∀ (u : S → ℝ) (v : T → ℝ),
    Measurable u → Measurable v →
    (∃ M : ℝ, ∀ y, ‖u y‖ ≤ M) → (∃ N : ℝ, ∀ z, ‖v z‖ ≤ N) →
    realConditionalExpectationValue G P (fun ω => u (Y ω) * v (Z ω)) =ᵐ[P]
      (fun ω => realConditionalExpectationValue G P (u ∘ Y) ω *
        realConditionalExpectationValue G P (v ∘ Z) ω)

def boundedVersionsType : Prop :=
  ∀ {Ω : Type u} {S : Type v} {T : Type w} (G : MeasurableSpace Ω)
    [F : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (Y : Ω → S) (Z : Ω → T), Measurable Y → Measurable Z →
    independenceValue G P Y Z → ∀ (u : S → ℝ) (v : T → ℝ),
    Measurable u → Measurable v →
    (∃ M : ℝ, ∀ y, ‖u y‖ ≤ M) → (∃ N : ℝ, ∀ z, ‖v z‖ ≤ N) →
    ∀ U V W : Ω → ℝ,
    realVersionValue G P (u ∘ Y) U → realVersionValue G P (v ∘ Z) V →
    realVersionValue G P (fun ω => u (Y ω) * v (Z ω)) W →
    W =ᵐ[P] (fun ω => U ω * V ω)

end Specs.ProbabilityFoundations.Ch04.ConditionalIndependence
