import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.Disintegration
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.CompletedMeasurableVersions
import Mathlib.MeasureTheory.Measure.Trim

/-!
Independent statements of paper.tex, Corollary `cor:conditional-law` (1175–1187).
The original probability need not be complete. The base space S and the
sub-sigma-algebra G are arbitrary. A completion extension assumes the displayed
originally measurable versions; it does not infer their existence for an
arbitrary measurable target from completion measurability alone.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch04.ConditionalLaws

universe u v w

def jointLawType : Prop :=
  ∀ {Ω : Type u} {S : Type v} {T : Type w}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [Nonempty T]
    (P : Measure Ω) [IsProbabilityMeasure P],
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    ∀ (X : Ω → S) (Y : Ω → T), Measurable X → Measurable Y →
    ∃ K : Kernel S T, IsMarkovKernel K ∧
      Measure.map (fun ω => (X ω, Y ω)) P =
        KernelMeasure.kernelMeasureValue (Measure.map X P) K

def conditionalLawType : Prop :=
  ∀ {Ω : Type u} {T : Type w} [F : MeasurableSpace Ω]
    [MeasurableSpace T] [Nonempty T] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ F),
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    ∀ (Y : Ω → T), @Measurable Ω T F _ Y →
    ∃ K : @Kernel Ω T G _, @IsMarkovKernel Ω T G _ K ∧
      ∀ (A : Set Ω), MeasurableSet[G] A →
      ∀ (B : Set T), MeasurableSet B →
      (∫⁻ ω in A, K ω B ∂P.trim hG) = P (A ∩ Y ⁻¹' B)

def completedJointLawType : Prop :=
  ∀ {Ω : Type u} {S : Type v} {T : Type w}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [Nonempty T]
    (P : Measure Ω) [IsProbabilityMeasure P],
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    ∀ (X X0 : Ω → S) (Y Y0 : Ω → T),
    Measurable X0 → Measurable Y0 → X =ᵐ[P] X0 → Y =ᵐ[P] Y0 →
    ∃ K : Kernel S T, IsMarkovKernel K ∧
      @Measure.map (NullMeasurableSpace Ω P) (S × T) _ _
        (fun ω => (X ω, Y ω)) P.completion =
        KernelMeasure.kernelMeasureValue
          (@Measure.map (NullMeasurableSpace Ω P) S _ _ X P.completion) K

def completedConditionalLawType : Prop :=
  ∀ {Ω : Type u} {T : Type w} [F : MeasurableSpace Ω]
    [MeasurableSpace T] [Nonempty T] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ F),
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    ∀ (Y Y0 : Ω → T), @Measurable Ω T F _ Y0 → Y =ᵐ[P] Y0 →
    ∃ K : @Kernel Ω T G _, @IsMarkovKernel Ω T G _ K ∧
      ∀ (A : Set Ω), MeasurableSet[G] A →
      ∀ (B : Set T), MeasurableSet B →
      (∫⁻ ω in A, K ω B ∂P.trim hG) = P.completion (A ∩ Y ⁻¹' B)

end Specs.ProbabilityFoundations.Ch04.ConditionalLaws
