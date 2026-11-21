import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions

/-!
Independent statements for paper.tex:2177–2192.

Subsequences and further subsequences have strictly increasing natural indices.
The convergence predicates are the shared global strict-deviation predicate and
the ordinary a.e. predicate with a measurable null envelope. The forward
implication holds on arbitrary positive measure spaces, even without function
measurability. The equivalence retains the source's finite total mass and
measurable real/complex scalar functions, expressed uniformly using `RCLike`.
No completeness or sigma-finiteness of the original space is imposed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u v

namespace Specs.D11.Ch07.SubsequenceCharacterization

open Specs.D11.Ch07.ConvergenceDefinitions

def every_subsequence_has_ae_subsequence : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (F : ℕ → X → E) (f : X → E),
    inMeasureConverges_value μ F f →
    ∀ ns : ℕ → ℕ, StrictMono ns →
      ∃ ms : ℕ → ℕ, StrictMono ms ∧
        aeConverges_value μ (fun n => F (ns (ms n))) f

def finite_subsequence_characterization : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (F : ℕ → X → 𝕜) (f : X → 𝕜),
    μ univ < ∞ → (∀ n, Measurable (F n)) → Measurable f →
    (inMeasureConverges_value μ F f ↔
      ∀ ns : ℕ → ℕ, StrictMono ns →
        ∃ ms : ℕ → ℕ, StrictMono ms ∧
          aeConverges_value μ (fun n => F (ns (ms n))) f)

end Specs.D11.Ch07.SubsequenceCharacterization
