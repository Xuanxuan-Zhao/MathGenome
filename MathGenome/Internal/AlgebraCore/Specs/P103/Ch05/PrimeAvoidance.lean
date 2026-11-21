import Mathlib.RingTheory.Ideal.Operations

/-! Independent statements of Lemma 5.2 (paper.tex, finite prime avoidance).
The indices `Fin n` retain repeated ideals. No properness or incomparability
assumption is imposed. The two alternatives have separate statements, so the
infinite-field assumption does not enter the prime-ideal alternative. -/

namespace Specs.P103.Ch05

universe u v

/-- At most two members of the indexed family are nonprime. -/
def finitePrimeAvoidanceType : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (n : ℕ), 1 ≤ n →
    ∀ (J : Ideal R) (I : Fin n → Ideal R),
    (Finset.univ.filter (fun i => ¬ (I i).IsPrime)).card ≤ 2 →
    (↑J : Set R) ⊆ ⋃ i, (I i : Set R) → ∃ i, J ≤ I i

/-- The alternative where the ring contains an infinite field through a unital embedding. -/
def infiniteFieldAvoidanceType : Prop :=
  ∀ (R : Type u) [CommRing R] (k : Type v) [Field k] [Infinite k]
    (f : k →+* R), Function.Injective f →
    ∀ (n : ℕ), 1 ≤ n → ∀ (J : Ideal R) (I : Fin n → Ideal R),
    (↑J : Set R) ⊆ ⋃ i, (I i : Set R) → ∃ i, J ≤ I i

end Specs.P103.Ch05
