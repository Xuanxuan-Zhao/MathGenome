import MathGenome.Internal.Specs.D07.Ch03.CosetsPartition

/-!
Independent specification of K07.03.coset_bijections (paper.tex:583–590).
Cosets use the shared image-of-multiplication definitions. Their spaces are
the sets of distinct coset subsets, represented by subtypes of `Set.range`.
These are set equivalences for arbitrary groups and subgroups, with no
finiteness or normality hypothesis. The formulas record the source's maps
and their inverses as well as the existence of the bijections.
-/

namespace Specs.D07.Ch03.CosetBijections

open Specs.D07.Ch03.CosetsPartition

universe u

def LeftCosetBijection : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (g : G),
    ∃ e : H ≃ ↥(leftCoset H g),
      (∀ h : H, (e h : G) = g * (h : G)) ∧
      (∀ x : ↥(leftCoset H g), (e.symm x : G) = g⁻¹ * (x : G))

def RightCosetBijection : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (g : G),
    ∃ e : H ≃ ↥(rightCoset H g),
      (∀ h : H, (e h : G) = (h : G) * g) ∧
      (∀ x : ↥(rightCoset H g), (e.symm x : G) = (x : G) * g⁻¹)

def CosetSpacesBijection : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    ∃ e : ↥(Set.range (leftCoset H)) ≃ ↥(Set.range (rightCoset H)),
      (∀ C, (e C : Set G) = Inv.inv '' (C : Set G)) ∧
      (∀ D, (e.symm D : Set G) = Inv.inv '' (D : Set G))

end Specs.D07.Ch03.CosetBijections
