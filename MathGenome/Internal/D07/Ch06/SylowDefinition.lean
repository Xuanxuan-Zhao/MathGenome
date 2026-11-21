import MathGenome.Internal.Specs.D07.Ch06.SylowDefinition
import MathGenome.Internal.D07.Ch06.SylowContainment
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
Cardinality and maximality agree (`paper.tex:1032–1039`).

The accepted containment theorem uses the cardinality definition of a
Sylow subgroup. A maximal p-subgroup equals its containing subgroup of
order p^a. Conversely, given P ≤ Q with |P| = p^a and Q a p-subgroup,
put Q inside S of order p^a. The finite inclusion P ≤ S is an equality,
and hence Q = P. This proves the converse without assuming the very
maximality/cardinality equivalence being established here.
-/

namespace D07.Ch06.SylowDefinition

universe u

open Specs.D07.Ch06.SylowDefinition
open PgroupDefinition

theorem maximal_iff_card (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) (P : Subgroup G) :
    maximalPSubgroup p P ↔ Nat.card P = p ^ a := by
  constructor
  · rintro ⟨hP, hmax⟩
    obtain ⟨S, hPS, hS⟩ :=
      SylowContainment.exists_sylow_containing G p a m hp hcard hm P hP
    have hSP := hmax S ⟨inferInstance, a, hS⟩ hPS
    simpa only [hSP] using hS
  · intro hP
    refine ⟨⟨inferInstance, a, hP⟩, ?_⟩
    intro Q hQ hPQ
    obtain ⟨S, hQS, hS⟩ :=
      SylowContainment.exists_sylow_containing G p a m hp hcard hm Q hQ
    have hPS : P = S :=
      Subgroup.eq_of_le_of_card_ge (hPQ.trans hQS) (by rw [hS, hP])
    exact le_antisymm (hQS.trans hPS.ge) hPQ

/-- A bridge checks the actual elementwise p-group predicate used by
`Sylow`, rather than relying on the name of that structure. -/
theorem sylow_iff_card (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) (P : Subgroup G) :
    (∃ S : Sylow p G, S.toSubgroup = P) ↔ Nat.card P = p ^ a := by
  rw [← maximal_iff_card G p a m hp hcard hm P]
  constructor
  · rintro ⟨S, rfl⟩
    refine ⟨(finitePGroup_iff_finite_isPGroup S.toSubgroup p hp).mpr
      ⟨inferInstance, S.isPGroup'⟩, ?_⟩
    intro Q hQ hSQ
    exact S.is_maximal'
      ((finitePGroup_iff_finite_isPGroup Q p hp).mp hQ).2 hSQ
  · rintro ⟨hP, hmax⟩
    refine ⟨⟨P, ((finitePGroup_iff_finite_isPGroup P p hp).mp hP).2, ?_⟩, rfl⟩
    intro Q hQ hPQ
    exact hmax Q ((finitePGroup_iff_finite_isPGroup Q p hp).mpr
      ⟨inferInstance, hQ⟩) hPQ

theorem maximal_iff_bot_of_not_dvd_card (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hcard : ¬ p ∣ Nat.card G) (P : Subgroup G) :
    maximalPSubgroup p P ↔ P = ⊥ := by
  rw [maximal_iff_card G p 0 (Nat.card G) hp (by simp) hcard P, pow_zero]
  exact P.eq_bot_iff_card.symm

end D07.Ch06.SylowDefinition
