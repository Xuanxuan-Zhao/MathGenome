import MathGenome.Internal.Specs.D07.Ch04.CommutatorAbelianization
import MathGenome.Internal.D07.Ch04.CharacteristicSubgroups
import MathGenome.Internal.D07.Ch04.QuotientUniversalProperty

/-!
The universal abelian quotient, `K07.04.commutator_abelianization`.
The commutator subgroup is ordinary subgroup generation. Automorphisms preserve
it; characteristicity supplies normality. The quotient criterion says precisely
that all commutators become identities. Finally an abelian target kills every
generator, and the upstream quotient universal property gives unique descent.
-/

namespace D07.Ch04.CommutatorAbelianization

open Specs.D07.Ch01.GroupDefinition (abelianPredicateValue)
open scoped commutatorElement

universe u v

theorem commutator_generated (G : Type u) [Group G] :
    commutator G = Subgroup.closure {z : G | ∃ x y : G, x * y * x⁻¹ * y⁻¹ = z} := by
  simpa only [commutatorSet, commutatorElement_def] using (commutator_eq_closure G)

theorem convention_generators_agree (G : Type u) [Group G] :
    {z : G | ∃ x y : G, x⁻¹ * y⁻¹ * x * y = z} =
      {z : G | ∃ x y : G, x * y * x⁻¹ * y⁻¹ = z} := by
  ext z
  constructor
  · rintro ⟨x, y, rfl⟩
    exact ⟨x⁻¹, y⁻¹, by simp⟩
  · rintro ⟨x, y, rfl⟩
    exact ⟨x⁻¹, y⁻¹, by simp⟩

theorem commutator_characteristic (G : Type u) [Group G] :
    (commutator G).Characteristic := inferInstance

theorem commutator_normal (G : Type u) [Group G] :
    (commutator G).Normal :=
  CharacteristicSubgroups.characteristic_normal G (commutator G)
    (commutator_characteristic G)

theorem quotient_abelian_iff (G : Type u) [Group G]
    (N : Subgroup G) [N.Normal] :
    abelianPredicateValue (G ⧸ N) ↔ commutator G ≤ N := by
  change (∀ a b : G ⧸ N, a * b = b * a) ↔ _
  rw [← isMulCommutative_iff]
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le

theorem abelian_quotient (G : Type u) [Group G] :
    abelianPredicateValue (G ⧸ commutator G) :=
  (quotient_abelian_iff G (commutator G)).mpr le_rfl

theorem commutator_le_kernel (G : Type u) (A : Type v) [Group G] [Group A]
    (hA : abelianPredicateValue A) (f : G →* A) : commutator G ≤ f.ker := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro z ⟨x, y, rfl⟩
  change f ⁅x, y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (hA (f x) (f y))

theorem factors_uniquely (G : Type u) (A : Type v) [Group G] [Group A]
    (hA : abelianPredicateValue A) (f : G →* A) :
    ∃! fbar : G ⧸ commutator G →* A,
      fbar.comp (QuotientGroup.mk' (commutator G)) = f := by
  obtain ⟨fbar, hfactor⟩ :=
    (QuotientUniversalProperty.factorization_iff G A (commutator G) f).mpr
      (commutator_le_kernel G A hA f)
  refine ⟨fbar, hfactor, ?_⟩
  intro other hother
  exact QuotientUniversalProperty.factorization_unique G A (commutator G) f
    other fbar hother hfactor

theorem factorization_formula (G : Type u) (A : Type v) [Group G] [Group A]
    (_hA : abelianPredicateValue A) (f : G →* A)
    (fbar : G ⧸ commutator G →* A)
    (hfactor : fbar.comp (QuotientGroup.mk' (commutator G)) = f) (g : G) :
    fbar (QuotientGroup.mk' (commutator G) g) = f g :=
  QuotientUniversalProperty.factorization_formula G A (commutator G) f fbar hfactor g

end D07.Ch04.CommutatorAbelianization
