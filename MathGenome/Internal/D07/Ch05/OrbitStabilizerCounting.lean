import MathGenome.Internal.D07.Ch03.Lagrange
import MathGenome.Internal.D07.Ch05.OrbitStabilizerDefinitions
import MathGenome.Internal.D07.Ch05.OrbitStabilizerEquivalence
import MathGenome.Internal.Specs.D07.Ch05.OrbitStabilizerCounting

/-!
# Orbit–stabilizer counting

`K07.05.orbit_stabilizer_counting`, paper.tex:849–860.
The index formula uses the accepted coset-to-orbit bijection, and the
product formula uses Lagrange. Finite additivity follows from the
decomposition of X as the disjoint union of its distinct orbits.
-/

namespace D07.Ch05.OrbitStabilizerCounting

universe u v

open D07.Ch05.OrbitStabilizerDefinitions

theorem finite_orbit (G : Type u) (X : Type v) [Group G] [MulAction G X]
    [Finite G] (x : X) : (orbit G X x).Finite :=
  Set.finite_range (fun g : G => g • x)

theorem orbit_card_eq_index (G : Type u) (X : Type v) [Group G] [MulAction G X]
    [Finite G] (x : X) : Nat.card ↥(orbit G X x) = (stabilizer G X x).index := by
  obtain ⟨e, _⟩ :=
    OrbitStabilizerEquivalence.orbit_stabilizer_equivalence G X x
  exact (Nat.card_congr e).symm

theorem orbit_card_mul_stabilizer_card (G : Type u) (X : Type v)
    [Group G] [MulAction G X] [Finite G] (x : X) :
    Nat.card ↥(orbit G X x) * Nat.card (stabilizer G X x) = Nat.card G := by
  rw [orbit_card_eq_index, Nat.mul_comm,
    ← D07.Ch03.Lagrange.coset_count_eq_index G (stabilizer G X x)]
  exact (D07.Ch03.Lagrange.cardinality_formula G (stabilizer G X x)).symm

theorem card_eq_sum_orbit_cards (G : Type u) (X : Type v)
    [Group G] [MulAction G X] [Finite X] :
    letI := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
    Nat.card X = ∑ q : MulAction.orbitRel.Quotient G X, Nat.card ↥q.orbit := by
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  calc
    Nat.card X = Nat.card (Σ q : MulAction.orbitRel.Quotient G X, ↥q.orbit) :=
      Nat.card_congr (MulAction.selfEquivSigmaOrbits' G X)
    _ = ∑ q : MulAction.orbitRel.Quotient G X, Nat.card ↥q.orbit := Nat.card_sigma

end D07.Ch05.OrbitStabilizerCounting
