import MathGenome.Internal.D07.Ch05.CentralizersNormalizers
import MathGenome.Internal.D07.Ch05.ConjugationAction
import MathGenome.Internal.D07.Ch05.OrbitStabilizerCounting
import MathGenome.Internal.Specs.D07.Ch05.ConjugacyCounting

/-!
Counting element and subgroup conjugates, `K07.05.conjugacy_counting`
(paper.tex:891–898). Both formulas follow from orbit–stabilizer. The subgroup
action maps subgroups by conjugation automorphisms; its orbit consists of
distinct conjugate subgroups and its stabilizer is the normalizer.
-/

namespace D07.Ch05.ConjugacyCounting

universe u

theorem conjugacy_class_card_eq_index (G : Type u) [Group G] [Finite G] (x : G) :
    Nat.card ↥(ConjClasses.mk x).carrier = (Subgroup.centralizer {x}).index := by
  letI : MulAction G G := ConjugationAction.conjugationAction G
  have h := OrbitStabilizerCounting.orbit_card_eq_index G G x
  dsimp only [OrbitStabilizerDefinitions.orbit, OrbitStabilizerDefinitions.stabilizer] at h
  rw [ConjugationAction.orbit_eq_conjugacy_class,
    ConjugationAction.stabilizer_eq_centralizer] at h
  exact h

theorem conjugate_subgroups_card_eq_index (G : Type u) [Group G] [Finite G]
    (H : Subgroup G) :
    Nat.card {K : Subgroup G //
      ∃ g : G, (fun h : G => g * h * g⁻¹) '' (H : Set G) = (K : Set G)} =
        (Subgroup.normalizer (H : Set G)).index := by
  letI : MulAction G (Subgroup G) :=
    { smul := fun g K => K.map (MulAut.conj g).toMonoidHom
      one_smul := by
        intro K
        change K.map (MulAut.conj (1 : G)).toMonoidHom = K
        rw [map_one]
        exact K.map_id
      mul_smul := by
        intro g h K
        change K.map (MulAut.conj (g * h)).toMonoidHom =
          (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        apply MonoidHom.ext
        intro k
        simp [MulAut.conj_apply, mul_assoc] }
  have orbit_eq : MulAction.orbit G H =
      {K : Subgroup G |
        ∃ g : G, (fun h : G => g * h * g⁻¹) '' (H : Set G) = (K : Set G)} := by
    ext K
    change (∃ g : G, H.map (MulAut.conj g).toMonoidHom = K) ↔ _
    exact exists_congr fun g => SetLike.coe_injective.eq_iff.symm
  have stabilizer_eq : MulAction.stabilizer G H =
      Subgroup.normalizer (H : Set G) := by
    ext g
    change H.map (MulAut.conj g).toMonoidHom = H ↔
      g ∈ Subgroup.normalizer (H : Set G)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.symm
  have h := OrbitStabilizerCounting.orbit_card_eq_index G (Subgroup G) H
  change Nat.card ↥(MulAction.orbit G H) = (MulAction.stabilizer G H).index at h
  rw [orbit_eq, stabilizer_eq] at h
  exact h

end D07.Ch05.ConjugacyCounting
