import MathGenome.Internal.D07.Ch01.GeneratedWords
import MathGenome.Internal.D07.Ch01.HomPreservesPowers
import MathGenome.Internal.Specs.D07.Ch01.HomOnGenerators
import Mathlib.Algebra.Group.Subgroup.Map

/-!
Homomorphisms on generated subgroups, as in `K07.01.hom_on_generators`.
Agreement is preserved by identity, multiplication, and inversion, so
the upstream generation induction applies. For the image assertion,
`MonoidHom.map_closure` gives equality of subgroups, whose underlying
sets are exactly the ordinary images in the source statement.
-/

namespace D07.Ch01.HomOnGenerators

universe u v

theorem agree_on_generated (G : Type u) (H : Type v) [Group G] [Group H]
    (f g : HomomorphismDefinition.GroupHom G H) (S : Set G)
    (hS : ∀ s ∈ S, f s = g s) :
    ∀ x ∈ Subgroup.closure S, f x = g x := by
  apply GeneratedWords.generation_induction G S (fun x => f x = g x) hS
  · rw [map_one, map_one]
  · intro x y hx hy
    rw [map_mul, map_mul, hx, hy]
  · intro x hx
    rw [map_inv, map_inv, hx]

theorem image_generated (G : Type u) (H : Type v) [Group G] [Group H]
    (f : HomomorphismDefinition.GroupHom G H) (S : Set G) :
    f '' (Subgroup.closure S : Set G) =
      (Subgroup.closure (f '' S) : Set H) := by
  rw [← Subgroup.coe_map, MonoidHom.map_closure]

end D07.Ch01.HomOnGenerators
