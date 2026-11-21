import MathGenome.Internal.Specs.D07.Ch01.GroupNormalQuotient

/-!
Independent specification of `K07.04.normality_equivalences`, paper.tex:662–668.

The conjugate `gNg⁻¹` is the image of the subgroup carrier under
`n ↦ g * n * g⁻¹`. Left and right cosets are the existing shared set-valued
cosets, with multiplication in the source's order. All quantifiers range
over arbitrary groups and subgroups. Quotients require explicit normality.
The kernel witness may be in the same universe as the original group;
normality of kernels allows arbitrary source and target universes.
-/

namespace Specs.D07.Ch04.NormalityEquivalences

open Specs.D07.Ch03.CosetsPartition

universe u v

def ConjugationIffConjugateEq : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G),
    (∀ g n : G, n ∈ N → g * n * g⁻¹ ∈ N) ↔
      ∀ g : G, (fun n => g * n * g⁻¹) '' (N : Set G) = (N : Set G)

def ConjugateEqIffCosetsEq : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G),
    (∀ g : G, (fun n => g * n * g⁻¹) '' (N : Set G) = (N : Set G)) ↔
      ∀ g : G, leftCoset N g = rightCoset N g

def NormalIffConjugateEq : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G),
    N.Normal ↔ ∀ g : G, (fun n => g * n * g⁻¹) '' (N : Set G) = (N : Set G)

def NormalIffCosetsEq : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G),
    N.Normal ↔ ∀ g : G, leftCoset N g = rightCoset N g

def KernelNormal : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    f.ker.Normal

def NormalIsKernel : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G), N.Normal →
    ∃ (H : Type u) (_ : Group H) (f : G →* H), f.ker = N

end Specs.D07.Ch04.NormalityEquivalences
