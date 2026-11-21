import MathGenome.Internal.Specs.D07.Ch01.SubgroupDefinitionTest
import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Data.Set.Lattice.Indexed

/-!
Independent specification of K07.03.cosets_partition (paper.tex:574–581).
Cosets are images of the subgroup carrier under multiplication in the stated
order. All carriers and subgroups are arbitrary; neither finiteness nor
normality is assumed. Partition means nonempty blocks covering the group,
with exactly one distinct block containing each element. Representatives
are not required to be unique.
-/

namespace Specs.D07.Ch03.CosetsPartition

universe u

/-- The source's set `xH = {xh : h ∈ H}`. -/
def leftCoset {G : Type u} [Group G] (H : Subgroup G) (x : G) : Set G :=
  (fun h => x * h) '' (H : Set G)

/-- The source's set `Hx = {hx : h ∈ H}`. -/
def rightCoset {G : Type u} [Group G] (H : Subgroup G) (x : G) : Set G :=
  (fun h => h * x) '' (H : Set G)

def LeftRelationEquivalence : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    Equivalence (fun x y : G => x⁻¹ * y ∈ H)

def RightRelationEquivalence : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    Equivalence (fun x y : G => y * x⁻¹ ∈ H)

def LeftClassEqCoset : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (x : G),
    {y : G | x⁻¹ * y ∈ H} = leftCoset H x

def RightClassEqCoset : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (x : G),
    {y : G | y * x⁻¹ ∈ H} = rightCoset H x

def LeftCosetsEqOrDisjoint : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (x y : G),
    leftCoset H x = leftCoset H y ∨ Disjoint (leftCoset H x) (leftCoset H y)

def RightCosetsEqOrDisjoint : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (x y : G),
    rightCoset H x = rightCoset H y ∨ Disjoint (rightCoset H x) (rightCoset H y)

def LeftCosetsPartition : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    (∀ x : G, (leftCoset H x).Nonempty) ∧
    (⋃ x : G, leftCoset H x) = Set.univ ∧
    ∀ z : G, ∃! C : Set G, C ∈ Set.range (leftCoset H) ∧ z ∈ C

def RightCosetsPartition : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    (∀ x : G, (rightCoset H x).Nonempty) ∧
    (⋃ x : G, rightCoset H x) = Set.univ ∧
    ∀ z : G, ∃! C : Set G, C ∈ Set.range (rightCoset H) ∧ z ∈ C

end Specs.D07.Ch03.CosetsPartition
