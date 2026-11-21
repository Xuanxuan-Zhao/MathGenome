import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.LatticeLocalBounds
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.GreenCriterion

/-! Independent statements for paper.tex, Theorem `p207:thm:polya`.
The recurrence predicates use the actual canonical first positive return event;
the Fourier integral is only an auxiliary characterization. -/

open MeasureTheory
open scoped ENNReal MeasureTheory

namespace P207.Walk.PolyaClassificationSpec

/-- Translation invariance of all transition probabilities of the fixed kernel. -/
def power_translation : Prop := ∀ (d : ℕ) [NeZero d] (n : ℕ)
    (a x y : Lattice d),
  Markov.power (latticeKernel d) n (a + x) (a + y) =
    Markov.power (latticeKernel d) n x y

/-- In particular, the first positive return probability is independent of the state. -/
def firstReturn_translation : Prop := ∀ (d : ℕ) [NeZero d] (x : Lattice d),
  Markov.returnProbability (latticeKernel d) x =
    Markov.returnProbability (latticeKernel d) 0

/-- Extended-valued Tonelli identity, including the singular values at the two peaks. -/
def green_integral : Prop := ∀ (d : ℕ) [NeZero d] (x : Lattice d),
  Markov.greenSeries (latticeKernel d) x =
    ∫⁻ t : Torus d, (ENNReal.ofReal (1 - phi t ^ 2))⁻¹ ∂torusMeasure d

/-- All states, in every positive dimension, with the original return-event meaning. -/
def recurrent_iff : Prop := ∀ (d : ℕ) [NeZero d] (x : Lattice d),
  Markov.Recurrent (latticeKernel d) x ↔ d = 1 ∨ d = 2

def transient_iff : Prop := ∀ (d : ℕ) [NeZero d] (x : Lattice d),
  Markov.Transient (latticeKernel d) x ↔ 3 ≤ d

end P207.Walk.PolyaClassificationSpec
