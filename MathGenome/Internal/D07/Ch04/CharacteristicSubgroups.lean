import MathGenome.Internal.Specs.D07.Ch04.CharacteristicSubgroups
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
Characteristic subgroups, `K07.04.characteristic_subgroups`.

An automorphism restricts to a characteristic subgroup. In the normal case,
each ambient conjugation restricts to an automorphism of the normal subgroup.
The library inheritance results use these restrictions to preserve `K` and
then its image under the inclusion `H.subtype`. The center result uses
surjectivity of automorphisms to preserve commutation with every element.
-/

namespace D07.Ch04.CharacteristicSubgroups

universe u

/-- Characteristic means that every automorphism maps the subgroup onto itself. -/
theorem characteristic_iff_invariant (G : Type u) [Group G] (H : Subgroup G) :
    H.Characteristic ↔ ∀ f : MulAut G, H.map f.toMonoidHom = H :=
  Subgroup.characteristic_iff_map_eq

theorem characteristic_normal (G : Type u) [Group G] (H : Subgroup G)
    (hH : H.Characteristic) : H.Normal := by
  let := hH
  exact Subgroup.normal_of_characteristic H

theorem characteristic_in_characteristic (G : Type u) [Group G]
    (H : Subgroup G) (K : Subgroup H)
    (hH : H.Characteristic) (hK : K.Characteristic) :
    (K.map H.subtype).Characteristic := by
  let := hH
  let := hK
  exact Subgroup.characteristic_of_characteristic_of_characteristic

theorem characteristic_in_normal (G : Type u) [Group G]
    (H : Subgroup G) (K : Subgroup H)
    (hH : H.Normal) (hK : K.Characteristic) :
    (K.map H.subtype).Normal := by
  let := hH
  let := hK
  exact ConjAct.normal_of_characteristic_of_normal

theorem center_characteristic (G : Type u) [Group G] :
    (Subgroup.center G).Characteristic :=
  Subgroup.centerCharacteristic

end D07.Ch04.CharacteristicSubgroups
