import MathGenome.Internal.Specs.D07.Ch01.HomomorphismDefinition
import MathGenome.Internal.Specs.D07.Ch01.SubgroupDefinitionTest
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
Independent specification of `K07.01.kernel_image` (paper.tex:311–323).

The kernel and image are Mathlib's canonical subgroup objects `f.ker` and
`f.range`. Their carrier formulas identify them with the source's sets.
Normality is the source's closure under every conjugation, as made explicit
by `NormalIffConjugation`. All groups are arbitrary, including trivial groups;
the source and target may belong to different universes.
-/

namespace Specs.D07.Ch01.KernelImage

universe u v

def KernelCarrier : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    (f.ker : Set G) = {x : G | f x = 1}

def ImageCarrier : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    (f.range : Set H) = {y : H | ∃ x : G, f x = y}

def KernelIsSubgroup : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    ∃ K : Subgroup G, (K : Set G) = {x : G | f x = 1}

def ImageIsSubgroup : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    ∃ I : Subgroup H, (I : Set H) = {y : H | ∃ x : G, f x = y}

def NormalIffConjugation : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G),
    N.Normal ↔ ∀ g n : G, n ∈ N → g * n * g⁻¹ ∈ N

def KernelNormal : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    f.ker.Normal

end Specs.D07.Ch01.KernelImage
