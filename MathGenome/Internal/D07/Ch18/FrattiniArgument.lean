import MathGenome.Internal.Specs.D07.Ch18.FrattiniArgument

/-!
Frattini's argument (K07.18.frattini_argument).

Mathlib's Frattini theorem applies to a Sylow subgroup of the normal subgroup
A. Normality converts its join with the ambient normalizer to the ordered
set product A N_G(P). The relative-index identity is the cardinality form
of the second isomorphism theorem, and Lagrange gives the divisibility.
-/

namespace D07.Ch18.FrattiniArgument

open scoped Pointwise
universe u

theorem normal_product (G : Type u) [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] (p : ℕ) (hp : p.Prime) (P : Sylow p A) :
    (Set.univ : Set G) = (A : Set G) * 
      (Subgroup.normalizer (P.map A.subtype : Set G) : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  have h := P.normalizer_sup_eq_top
  rw [← Subgroup.normal_mul, sup_comm, h]
  rfl

theorem index_formula (G : Type u) [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] (p : ℕ) (hp : p.Prime) (P : Sylow p A) :
    A.index = (A.subgroupOf (Subgroup.normalizer (P.map A.subtype : Set G))).index := by
  let : Fact p.Prime := ⟨hp⟩
  have h := Subgroup.relIndex_sup_right (Subgroup.normalizer (P.map A.subtype : Set G)) A
  rw [P.normalizer_sup_eq_top, Subgroup.relIndex_top_right] at h
  exact h

theorem index_divides_normalizer_order (G : Type u) [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] (p : ℕ) (hp : p.Prime) (P : Sylow p A) :
    A.index ∣ Nat.card (Subgroup.normalizer (P.map A.subtype : Set G)) := by
  rw [index_formula G A p hp P]
  exact (A.subgroupOf (Subgroup.normalizer (P.map A.subtype : Set G))).index_dvd_card

theorem normalizer_of_not_dvd_card (G : Type u) [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] (p : ℕ) (hp : p.Prime) (P : Sylow p A)
    (hcard : ¬ p ∣ Nat.card A) :
    (P : Subgroup A) = ⊥ ∧ Subgroup.normalizer (P.map A.subtype : Set G) = ⊤ := by
  let : Fact p.Prime := ⟨hp⟩
  have hP : (P : Subgroup A) = ⊥ := by
    apply (P : Subgroup A).eq_bot_iff_card.mpr
    rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hcard, pow_zero]
  refine ⟨hP, ?_⟩
  rw [hP, Subgroup.map_bot]
  exact (⊥ : Subgroup G).normalizer_eq_top

end D07.Ch18.FrattiniArgument
