import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions

/-!
# First Borel--Cantelli lemma: independent statement

This is paper.tex:359–369 (`d11:01:borel-cantelli-one`). The measure is
the canonical positive measure of the upstream source/native correspondence.
The sets belong to the specified sigma-algebra; their limsup is measurable
by the upstream set-systems result, and `Filter.limsup E Filter.atTop` is
exactly the source's `⋂ N, ⋃ n ≥ N, E n`.

No completeness, finite total mass, sigma-finiteness, independence, or
probability normalization is required. Empty spaces and zero measures are
allowed. The sum takes its value in `[0,∞]`.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace Specs.D11.Ch01.BorelCantelli

def first_borel_cantelli : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : ℕ → Set α),
    (∀ n, MeasurableSet (E n)) → (∑' n, μ (E n)) < ∞ →
      μ (Filter.limsup E Filter.atTop) = 0

end Specs.D11.Ch01.BorelCantelli
