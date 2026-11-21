import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.SubsequenceCharacterization
import MathGenome.Internal.RealAnalysis.D11.Ch07.SubsequenceUniqueness
import MathGenome.Internal.RealAnalysis.D11.Ch07.FiniteAeToMeasure
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Subsequence characterization of global convergence in measure

This proves paper.tex:2177–2192 with the canonical representative predicates.
Every subsequence of a sequence converging globally in measure still converges
in measure, so the accepted arbitrary-measure extraction theorem gives the
forward implication without finiteness.

For the converse, fix a deviation threshold. The filter subsequence criterion
reduces convergence of its measures to finding a convergent further sequence
inside every sequence of indices tending to infinity. Extract strictly
increasing indices first, apply the assumed a.e. subsequence property, and
apply the finite-space a.e.-to-measure theorem to that further subsequence.
The argument uses the given measurable scalar functions on the original space.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u v

namespace D11.Ch07.SubsequenceCharacterization

open D11.Ch07.ConvergenceDefinitions
open D11.Ch07.SubsequenceUniqueness
open D11.Ch07.FiniteAeToMeasure

/-- The forward implication requires neither finite mass nor measurability. -/
theorem every_subsequence_has_ae_subsequence
    {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (F : ℕ → X → E) (f : X → E)
    (h : inMeasureConverges μ F f) :
    ∀ ns : ℕ → ℕ, StrictMono ns →
      ∃ ms : ℕ → ℕ, StrictMono ms ∧
        aeConverges μ (fun n => F (ns (ms n))) f := by
  intro ns hns
  exact exists_ae_subsequence μ (fun n => F (ns n)) f
    (fun ε hε => (h ε hε).comp hns.tendsto_atTop)

/-- On a finite space the subsequence property is equivalent to global
convergence in measure, for finite measurable real or complex functions. -/
theorem finite_subsequence_characterization
    {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (F : ℕ → X → 𝕜) (f : X → 𝕜)
    (hμ : μ univ < ∞) (hF : ∀ n, Measurable (F n)) (hf : Measurable f) :
    inMeasureConverges μ F f ↔
      ∀ ns : ℕ → ℕ, StrictMono ns →
        ∃ ms : ℕ → ℕ, StrictMono ms ∧
          aeConverges μ (fun n => F (ns (ms n))) f := by
  constructor
  · exact every_subsequence_has_ae_subsequence μ F f
  · intro h ε hε
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ks, _hks, hnsks⟩ := strictMono_subseq_of_tendsto_atTop hns
    obtain ⟨ms, _hms, hlim⟩ := h (ns ∘ ks) hnsks
    have hmeasure := finite_ae_to_measure μ
      (fun n => F (ns (ks (ms n)))) f hμ (fun n => hF _) hf hlim
    exact ⟨ks ∘ ms, hmeasure ε hε⟩

end D11.Ch07.SubsequenceCharacterization
