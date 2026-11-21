import MathGenome.Internal.Specs.D07.Ch06.SylowContainment
import MathGenome.Internal.D07.Ch05.CosetActionKernel
import MathGenome.Internal.D07.Ch06.PgroupFixedPoints
import MathGenome.Internal.D07.Ch06.SylowExistence
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
Containment of prime-power subgroups (`paper.tex:1024–1031`).

The fixed Sylow subgroup is specified by its order, as in the source.
Left multiplication by P on G/Q has a fixed point because |G/Q| = m
is prime to p. A representative g of this point satisfies g⁻¹ P g ≤ Q,
which gives P ⊆ g Q g⁻¹. The conjugation automorphism preserves subgroup
cardinality, so this conjugate is still a Sylow subgroup in the source's
cardinality sense. No equivalence with maximal p-subgroups is used.
-/

namespace D07.Ch06.SylowContainment

universe u

open PgroupDefinition

theorem contained_in_conjugate (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) (P Q : Subgroup G)
    (hP : FinitePGroup p P) (hQ : Nat.card Q = p ^ a) :
    ∃ g : G, (P : Set G) ⊆ (fun x : G => g * x * g⁻¹) '' (Q : Set G) := by
  have hquot : Nat.card (G ⧸ Q) = m := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a)
    calc
      p ^ a * Nat.card (G ⧸ Q) = Nat.card G := by
        simpa only [hQ, Subgroup.index] using Q.card_mul_index
      _ = p ^ a * m := hcard
  obtain ⟨q, hq⟩ := PgroupFixedPoints.exists_fixed_point_of_not_dvd_card
    P (G ⧸ Q) p hp hP (by simpa only [hquot] using hm)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, ?_⟩
  intro x hx
  have hfix : (QuotientGroup.mk (x * g) : G ⧸ Q) = QuotientGroup.mk g := by
    have h := hq ⟨x, hx⟩
    change x • (QuotientGroup.mk g : G ⧸ Q) = QuotientGroup.mk g at h
    rwa [Ch05.CosetActionKernel.coset_action_apply] at h
  have hmem : g⁻¹ * x * g ∈ Q := by
    simpa only [mul_assoc] using QuotientGroup.eq.mp hfix.symm
  refine ⟨g⁻¹ * x * g, hmem, ?_⟩
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

theorem exists_sylow_containing (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) (P : Subgroup G) (hP : FinitePGroup p P) :
    ∃ S : Subgroup G, P ≤ S ∧ Nat.card S = p ^ a := by
  obtain ⟨Q, hQ⟩ := SylowExistence.largest_prime_power_existence G p a m hp hcard hm
  obtain ⟨g, hg⟩ := contained_in_conjugate G p a m hp hcard hm P Q hP hQ
  refine ⟨Q.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
  · exact hg
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hQ]

end D07.Ch06.SylowContainment
