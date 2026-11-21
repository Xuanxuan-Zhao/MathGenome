import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.UniformIntegrability
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.DeLaValleePoussin
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.DeLaValleePoussin
import Batteries.Tactic.OpenPrivate

/-! De la Vallée--Poussin's criterion for indexed Banach-valued families.
We identify the indexed family with its range to apply the general normed-group
criterion in MathGenome. The reverse implication uses the superlinear-tail
estimate itself, so no normalization at zero is required of the witness.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

universe u v w

namespace P207.Martingale

open private source_of_superlinear_bound from
  MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.DeLaValleePoussin

variable {Ω : Type u} {E : Type v} {I : Type w}
  [MeasurableSpace Ω] [NormedAddCommGroup E]

private theorem sourceUniformIntegrable_range (μ : Measure Ω) (X : I → Ω → E) :
    SourceUniformIntegrable μ X ↔
      ProbabilityFoundations.Ch01.SourceUniformIntegrable μ (range X) := by
  have tails : ProbabilityFoundations.Ch01.uniformTailIntegral μ (range X) =
      uniformTailIntegral μ X := by
    funext R
    simp only [uniformTailIntegral, tailIntegral,
      ProbabilityFoundations.Ch01.uniformTailIntegral,
      ProbabilityFoundations.Ch01.tailIntegral, iSup_range]
  simp only [SourceUniformIntegrable,
    ProbabilityFoundations.Ch01.SourceUniformIntegrable, tails, forall_mem_range]

/-- The equivalence of W31 (1) and (3), with a genuine finite extended moment
bound. No nonemptiness, countability, or codomain separability is needed. -/
theorem de_la_vallee_poussin (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : I → Ω → E) (hX : ∀ i, Integrable (X i) μ) :
    SourceUniformIntegrable μ X ↔
      ∃ Φ : ℝ → ℝ,
        (∀ t, 0 ≤ t → 0 ≤ Φ t) ∧
        MonotoneOn Φ (Ici 0) ∧ ConvexOn ℝ (Ici 0) Φ ∧
        Tendsto (fun t => Φ t / t) atTop atTop ∧
        (⨆ i, ∫⁻ x, ENNReal.ofReal (Φ ‖X i x‖) ∂μ) < ∞ := by
  have hRange : ∀ f ∈ range X, Integrable f μ := by
    simpa only [forall_mem_range] using hX
  rw [sourceUniformIntegrable_range]
  constructor
  · intro h
    obtain ⟨Φ, hmono, hconv, hnonneg, _, hsuper, hbound⟩ :=
      (ProbabilityFoundations.Ch01.de_la_vallee_poussin (range X) hRange).mp h
    exact ⟨Φ, hnonneg, hmono, hconv, hsuper, by
      simpa only [iSup_range] using hbound⟩
  · rintro ⟨Φ, _, _, _, hsuper, hbound⟩
    apply source_of_superlinear_bound hRange Φ hsuper
    simpa only [iSup_range] using hbound

end P207.Martingale
