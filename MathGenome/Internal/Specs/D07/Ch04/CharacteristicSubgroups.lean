import Mathlib.GroupTheory.Subgroup.Center

/-!
Independent specification of `K07.04.characteristic_subgroups`,
paper.tex:761–768 (chapters/M07.04.tex:102–109).

The canonical predicate `Subgroup.Characteristic` is identified with the
source's requirement that every automorphism map the subgroup onto itself.
For a subgroup `H` of `G` and a subgroup `K` of `H`, `K.map H.subtype`
is precisely `K` viewed as a subgroup of `G`. Thus the two inheritance
statements quantify over all nested subgroups, with their respective
characteristic or normal hypotheses explicit. No finiteness, nontriviality
or commutativity is imposed, and no quotient operations are used.
-/

namespace Specs.D07.Ch04.CharacteristicSubgroups

universe u

def CharacteristicIffInvariant : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    H.Characteristic ↔ ∀ f : MulAut G, H.map f.toMonoidHom = H

def CharacteristicNormal : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    H.Characteristic → H.Normal

def CharacteristicInCharacteristic : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (K : Subgroup H),
    H.Characteristic → K.Characteristic → (K.map H.subtype).Characteristic

def CharacteristicInNormal : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (K : Subgroup H),
    H.Normal → K.Characteristic → (K.map H.subtype).Normal

def CenterCharacteristic : Prop :=
  ∀ (G : Type u) [Group G], (Subgroup.center G).Characteristic

end Specs.D07.Ch04.CharacteristicSubgroups
