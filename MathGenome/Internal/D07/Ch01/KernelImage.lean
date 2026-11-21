import MathGenome.Internal.D07.Ch01.HomomorphismDefinition
import MathGenome.Internal.D07.Ch01.SubgroupDefinitionTest
import MathGenome.Internal.Specs.D07.Ch01.KernelImage

/-!
Kernels, images, and normality (`K07.01.kernel_image`). The canonical
subgroups have exactly the source's carriers, with inherited operations.
No finiteness, commutativity, or nontriviality assumption is imposed.
-/

namespace D07.Ch01.KernelImage

universe u v

theorem kernel_carrier (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) : (f.ker : Set G) = {x : G | f x = 1} :=
  rfl

theorem image_carrier (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) : (f.range : Set H) = {y : H | ∃ x : G, f x = y} :=
  rfl

theorem kernel_is_subgroup (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) : ∃ K : Subgroup G, (K : Set G) = {x : G | f x = 1} :=
  ⟨f.ker, kernel_carrier G H f⟩

theorem image_is_subgroup (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) : ∃ I : Subgroup H, (I : Set H) = {y : H | ∃ x : G, f x = y} :=
  ⟨f.range, image_carrier G H f⟩

theorem normal_iff_conjugation (G : Type u) [Group G] (N : Subgroup G) :
    N.Normal ↔ ∀ g n : G, n ∈ N → g * n * g⁻¹ ∈ N := by
  constructor
  · intro h g n hn
    exact h.conj_mem n hn g
  · intro h
    exact ⟨fun n hn g => h g n hn⟩

theorem kernel_normal (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) : f.ker.Normal := by
  apply (normal_iff_conjugation G f.ker).2
  intro g n hn
  change f (g * n * g⁻¹) = 1
  have hn' : f n = 1 := MonoidHom.mem_ker.mp hn
  rw [map_mul, map_mul, map_inv, hn', mul_one, mul_inv_cancel]

end D07.Ch01.KernelImage
