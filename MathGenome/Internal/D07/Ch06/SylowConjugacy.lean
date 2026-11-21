import MathGenome.Internal.Specs.D07.Ch06.SylowConjugacy
import MathGenome.Internal.D07.Ch06.SylowContainment
import MathGenome.Internal.D07.Ch06.SylowDefinition
import Mathlib.Data.Nat.Factorization.Basic

/-!
Conjugacy of Sylow subgroups (`paper.tex:1040–1047`).
The accepted containment theorem gives P ≤ gQg⁻¹. Conjugation preserves
cardinality, so the two finite subgroups have equal cardinality and are
equal. The maximality formulation then follows from the accepted
cardinality/maximality equivalence and prime-power factorization of |G|.
-/

namespace D07.Ch06.SylowConjugacy

universe u

theorem conjugate_of_card (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) (P Q : Subgroup G)
    (hP : Nat.card P = p ^ a) (hQ : Nat.card Q = p ^ a) :
    ∃ g : G, (P : Set G) = (fun x : G => g * x * g⁻¹) '' (Q : Set G) := by
  obtain ⟨g, hg⟩ := SylowContainment.contained_in_conjugate
    G p a m hp hcard hm P Q ⟨inferInstance, a, hP⟩ hQ
  have heq : P = Q.map (MulAut.conj g).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hg (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP, hQ])
  exact ⟨g, congrArg (fun H : Subgroup G => (H : Set G)) heq⟩

theorem sylow_conjugacy (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (P Q : Subgroup G)
    (hP : Specs.D07.Ch06.SylowDefinition.maximalPSubgroup p P)
    (hQ : Specs.D07.Ch06.SylowDefinition.maximalPSubgroup p Q) :
    ∃ g : G, (P : Set G) = (fun x : G => g * x * g⁻¹) '' (Q : Set G) := by
  obtain ⟨a, m, hm, hcard⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := G)).ne' p hp.ne_one
  exact conjugate_of_card G p a m hp hcard hm P Q
    ((SylowDefinition.maximal_iff_card G p a m hp hcard hm P).mp hP)
    ((SylowDefinition.maximal_iff_card G p a m hp hcard hm Q).mp hQ)

end D07.Ch06.SylowConjugacy
