import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.EntourageCalculus
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions

open Set Filter
open scoped Uniformity
universe u

namespace Specs.D10Topology.Ch12.DyadicChains

/-- The dyadic lemma, paper.tex `d10:12:dyadic-chains`.
The real power `(1 / 2)^n` is `2^{-n}`. Entourage membership and symmetry are required at positive indices,
exactly as in the source; index zero is fixed to the universal relation.
The uniform continuity conclusion uses the original product uniformity, not
an instance supplied by the new pseudometric. No separation or countable-base
assumption on the original uniformity is made. -/
def dyadic_chains : Prop :=
  ∀ {X : Type u} [UniformSpace X] (V : ℕ → Set (X × X)),
    V 0 = univ →
    (∀ n, V (n + 1) ∈ 𝓤 X) →
    (∀ n, UniformConventions.relationInverse (V (n + 1)) = V (n + 1)) →
    (∀ n, EntourageCalculus.relationPower (V (n + 1)) 3 ⊆ V n) →
    ∃ p : X → X → ℝ,
      Specs.D10Topology.Ch09.MetricConventions.PseudometricAxioms p ∧
      (∀ x y, p x y ≤ 1) ∧
      (∀ n, V n ⊆ {q | p q.1 q.2 ≤ (1 / 2 : ℝ) ^ n} ∧
        {q | p q.1 q.2 < (1 / 2 : ℝ) ^ (n + 1)} ⊆ V n) ∧
      UniformContinuous (fun q : X × X => p q.1 q.2)

end Specs.D10Topology.Ch12.DyadicChains
