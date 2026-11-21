import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.ConditionalLaws
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.ConditionalIndependence
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory

namespace Specs.ProbabilityFoundations.Ch04.ConditionalProductCriterion
universe u v w

/-- The defining event identities for a chosen regular conditional law. The
kernel is defined on the original conditioning sigma-algebra. -/
def IsConditionalLaw {Ω : Type u} {T : Type v} [F : MeasurableSpace Ω]
    [MeasurableSpace T] (P : Measure Ω) (G : MeasurableSpace Ω) (hG : G ≤ F)
    (Y : Ω → T) (K : @Kernel Ω T G _) : Prop :=
  ∀ A, MeasurableSet[G] A → ∀ B, MeasurableSet B →
    (∫⁻ ω in A, K ω B ∂P.trim hG) = P (A ∩ Y ⁻¹' B)

def binaryProductType : Prop :=
  ∀ (T : Type v) (U : Type w) [MeasurableSpace T] [MeasurableSpace U],
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue U →
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue (T × U)

def existenceType : Prop :=
  ∀ {Ω : Type u} {T : Type v} {U : Type w} [F : MeasurableSpace Ω]
    [mT : MeasurableSpace T] [mU : MeasurableSpace U] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ F),
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue U →
    ∀ (Y : Ω → T) (Z : Ω → U), @Measurable Ω T F mT Y → @Measurable Ω U F mU Z →
    ∃ (KY : @Kernel Ω T G _) (KZ : @Kernel Ω U G _)
      (KJ : @Kernel Ω (T × U) G _),
      IsMarkovKernel KY ∧ IsMarkovKernel KZ ∧ IsMarkovKernel KJ ∧
      @IsConditionalLaw Ω T F mT P G hG Y KY ∧ @IsConditionalLaw Ω U F mU P G hG Z KZ ∧
      @IsConditionalLaw Ω (T × U) F (mT.prod mU) P G hG (fun ω => (Y ω, Z ω)) KJ

/-- The criterion holds for every choice of the three regular conditional laws;
the exceptional set is measurable in G and the entire measures agree off it. -/
def criterionType : Prop :=
  ∀ {Ω : Type u} {T : Type v} {U : Type w} [F : MeasurableSpace Ω]
    [mT : MeasurableSpace T] [mU : MeasurableSpace U] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ F),
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue U →
    ∀ (Y : Ω → T) (Z : Ω → U), @Measurable Ω T F mT Y → @Measurable Ω U F mU Z →
    ∀ (KY : @Kernel Ω T G _) (KZ : @Kernel Ω U G _)
      (KJ : @Kernel Ω (T × U) G _)
      [IsMarkovKernel KY] [IsMarkovKernel KZ] [IsMarkovKernel KJ],
      @IsConditionalLaw Ω T F mT P G hG Y KY → @IsConditionalLaw Ω U F mU P G hG Z KZ →
      @IsConditionalLaw Ω (T × U) F (mT.prod mU) P G hG (fun ω => (Y ω, Z ω)) KJ →
      (@ConditionalIndependence.independenceValue Ω T U G F mT mU P Y Z ↔
        ∃ N : Set Ω, MeasurableSet[G] N ∧ P N = 0 ∧
          ∀ ω ∉ N, KJ ω = (KY ω).prod (KZ ω))

end Specs.ProbabilityFoundations.Ch04.ConditionalProductCriterion
