import MathGenome.Internal.RealAnalysis.D11.Ch07.ConvergenceDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.SubsequenceUniqueness

/-!
# Subsequences and uniqueness for global convergence in measure

This proves paper.tex:2157–2175 on arbitrary positive measure spaces, using
the shared global convergence and ordinary a.e. definitions.

For a positive threshold ε, the sets {‖fₙ-g‖ ≥ ε} are contained in
{‖fₙ-g‖ > ε/2}. Conversely, {‖fₙ-g‖ > ε} is contained in
{‖fₙ-g‖ ≥ ε}. Squeezing their measures between zero and the corresponding
deviation measures identifies the strict and non-strict definitions.

Mathlib's subsequence theorem uses summable geometric deviation measures and
the first Borel–Cantelli lemma. Its uniqueness theorem takes two successive
a.e. convergent subsequences and uses uniqueness of pointwise limits. Neither
result requires finite mass, sigma-finiteness, completeness, or measurability.
The native a.e. conclusion is transported through the proved upstream bridge,
which supplies a measurable null envelope even on an incomplete measure space.
-/

open Filter MeasureTheory
open scoped Topology

universe u v

namespace D11.Ch07.SubsequenceUniqueness

open D11.Ch07.ConvergenceDefinitions
open D11.Ch04.AeCommonException

variable {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]

/-- Changing strict to non-strict deviations does not change global convergence. -/
theorem inMeasureConverges_iff_native (μ : Measure X) (f : ℕ → X → E) (g : X → E) :
    inMeasureConverges μ f g ↔ TendstoInMeasure μ f atTop g := by
  rw [tendstoInMeasure_iff_norm]
  constructor
  · intro h ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h (ε / 2) (half_pos hε)) (fun _ => bot_le) ?_
    intro n
    exact measure_mono (fun x hx => lt_of_lt_of_le (half_lt_self hε) hx)
  · intro h ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h ε hε) (fun _ => bot_le) ?_
    intro n
    apply measure_mono
    intro x hx
    exact (show ε < ‖f n x - g x‖ from hx).le

/-- Global convergence in measure supplies an a.e. convergent subsequence. -/
theorem exists_ae_subsequence (μ : Measure X) (f : ℕ → X → E) (g : X → E)
    (h : inMeasureConverges μ f g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ aeConverges μ (fun n => f (ns n)) g := by
  obtain ⟨ns, hns, hlim⟩ :=
    ((inMeasureConverges_iff_native μ f g).mp h).exists_seq_tendsto_ae
  exact ⟨ns, hns, (almostEverywhere_iff_native μ _).mpr hlim⟩

/-- Two global limits in measure agree outside a measurable null envelope. -/
theorem limit_unique (μ : Measure X) (f : ℕ → X → E) (g h : X → E)
    (hg : inMeasureConverges μ f g) (hh : inMeasureConverges μ f h) :
    aeEq μ g h := by
  apply (aeEq_iff_native μ g h).mpr
  exact tendstoInMeasure_ae_unique
    ((inMeasureConverges_iff_native μ f g).mp hg)
    ((inMeasureConverges_iff_native μ f h).mp hh)

end D11.Ch07.SubsequenceUniqueness
