import MathGenome.Internal.Specs.D07.Ch05.OrbitStabilizerDefinitions
import Mathlib.GroupTheory.Coset.Defs

/-!
Independent specification of `K07.05.orbit_stabilizer_equivalence`
(paper.tex:841–848). The quotient is the set of left cosets, defined for
every subgroup, and the orbit and stabilizer are the upstream objects.
There are no finiteness, normality, faithfulness, or transitivity assumptions.
The acted-on type may be empty; the assertion is quantified over its points.
-/

namespace Specs.D07.Ch05.OrbitStabilizerEquivalence

universe u v

open Specs.D07.Ch05.OrbitStabilizerDefinitions

/-- The specified coset map is a bijection onto the orbit. The equation on
every representative fixes the map, rather than merely asserting that the
two types happen to admit some bijection. -/
def OrbitStabilizerEquivalence : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] (x : X),
    ∃ e : (G ⧸ stabilizerValue G X x) ≃ ↥(orbitValue G X x),
      ∀ g : G, (e (QuotientGroup.mk g) : X) = g • x

end Specs.D07.Ch05.OrbitStabilizerEquivalence
