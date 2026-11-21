import MathGenome.Internal.D07.Ch01.SubgroupDefinitionTest
import MathGenome.Internal.Specs.D07.Ch01.FiniteSubgroupTest

/-!
# Finite multiplicatively closed subsets

Formalization of `K07.01.finite_subgroup_test`. Left multiplication on the
finite subset is injective by ambient cancellation, hence surjective.
This recovers the ambient identity and all inverses, and the upstream
closure characterization then supplies a subgroup with exactly this carrier.
-/

namespace D07.Ch01.FiniteSubgroupTest

universe u

theorem finite_subgroup_test (G : Type u) [Group G] (s : Set G)
    (hs : s.Finite) (hne : s.Nonempty)
    (hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ s) :
    ∃ H : Subgroup G, (H : Set G) = s := by
  have hsurj (a : G) (ha : a ∈ s) : Set.SurjOn (fun x => a * x) s s := by
    have hmap : Set.MapsTo (fun x => a * x) s s := fun x hx => hmul a ha x hx
    have hinj : Set.InjOn (fun x => a * x) s :=
      fun _ _ _ _ h => mul_left_cancel h
    exact ((hs.injOn_iff_bijOn_of_mapsTo hmap).1 hinj).surjOn
  obtain ⟨a, ha⟩ := hne
  have h1 : (1 : G) ∈ s := by
    obtain ⟨b, hb, hab⟩ := hsurj a ha ha
    have hb1 : b = 1 := mul_left_cancel (hab.trans (mul_one a).symm)
    exact hb1 ▸ hb
  have hinv : ∀ x ∈ s, x⁻¹ ∈ s := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hsurj x hx h1
    exact (eq_inv_of_mul_eq_one_right hxc) ▸ hc
  exact (SubgroupDefinitionTest.subgroup_iff_closed G s).2 ⟨h1, hmul, hinv⟩

theorem positive_integers_counterexample :
    ({z : ℤ | 0 < z} : Set ℤ).Nonempty ∧
      (∀ x ∈ ({z : ℤ | 0 < z} : Set ℤ),
        ∀ y ∈ ({z : ℤ | 0 < z} : Set ℤ),
          x + y ∈ ({z : ℤ | 0 < z} : Set ℤ)) ∧
      ¬ (∃ H : AddSubgroup ℤ, (H : Set ℤ) = {z : ℤ | 0 < z}) := by
  refine ⟨⟨1, by decide⟩, ?_, ?_⟩
  · intro x hx y hy
    exact Int.add_pos hx hy
  · rintro ⟨H, hH⟩
    have hz : (0 : ℤ) ∈ ({z : ℤ | 0 < z} : Set ℤ) := hH ▸ H.zero_mem
    exact (lt_irrefl (0 : ℤ)) hz

end D07.Ch01.FiniteSubgroupTest
