import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.StandardBorel
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.KernelMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic

/-! Theorem `thm:kernel-randomization`, paper.tex:1239–1253.
The unit interval has its trace sigma-algebra and restricted Lebesgue probability.
All fiber identities are pointwise in the arbitrary measurable base. -/

open MeasureTheory ProbabilityTheory Set

namespace Specs.ProbabilityFoundations.Ch04.KernelRandomization

universe u v w

/-- Lebesgue probability on the closed interval, with its trace sigma-algebra. -/
noncomputable def unitUniform : Measure (Icc (0 : ℝ) 1) :=
  Measure.comap Subtype.val (volume : Measure ℝ)

def randomizationType : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T] [Nonempty T]
    (K : Kernel S T) [IsMarkovKernel K],
    ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    ∃ g : S × Icc (0 : ℝ) 1 → T, Measurable g ∧
      ∀ s, Measure.map (fun z => g (s, z)) unitUniform = K s

/-- Any measurable sampler with the pointwise fiber identity has the stated
joint law for every independent uniform on any probability space. -/
def jointLawType : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T]
    (K : Kernel S T) [IsMarkovKernel K]
    (g : S × Icc (0 : ℝ) 1 → T), Measurable g →
    (∀ s, Measure.map (fun z => g (s, z)) unitUniform = K s) →
    ∀ {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → S) (V : Ω → Icc (0 : ℝ) 1) (μ : Measure S),
      Measurable X → Measurable V → P.map X = μ → P.map V = unitUniform →
      IndepFun X V P →
      P.map (fun ω => (X ω, g (X ω, V ω))) =
        Specs.ProbabilityFoundations.Ch04.KernelMeasure.kernelMeasureValue μ K

end Specs.ProbabilityFoundations.Ch04.KernelRandomization
