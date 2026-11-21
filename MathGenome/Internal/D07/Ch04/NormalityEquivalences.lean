import MathGenome.Internal.D07.Ch01.GroupNormalQuotient
import MathGenome.Internal.Specs.D07.Ch04.NormalityEquivalences

/-!
Equivalent forms of normality (`K07.04.normality_equivalences`).
The set arguments use the shared cosets, with no finiteness assumption.
The quotient projection supplies the kernel witness only after normality
has been installed explicitly.
-/

namespace D07.Ch04.NormalityEquivalences

open Specs.D07.Ch03.CosetsPartition

universe u v

theorem conjugation_iff_conjugate_eq (G : Type u) [Group G] (N : Subgroup G) :
    (∀ g n : G, n ∈ N → g * n * g⁻¹ ∈ N) ↔
      ∀ g : G, (fun n => g * n * g⁻¹) '' (N : Set G) = (N : Set G) := by
  constructor
  · intro h g
    apply Set.Subset.antisymm
    · rintro _ ⟨n, hn, rfl⟩
      exact h g n hn
    · intro n hn
      refine ⟨g⁻¹ * n * g, ?_, ?_⟩
      · simpa only [inv_inv, SetLike.mem_coe] using h g⁻¹ n hn
      · simp [mul_assoc]
  · intro h g n hn
    have hmem : g * n * g⁻¹ ∈ (fun n => g * n * g⁻¹) '' (N : Set G) :=
      ⟨n, hn, rfl⟩
    rw [h g] at hmem
    exact hmem

theorem conjugate_eq_iff_cosets_eq (G : Type u) [Group G] (N : Subgroup G) :
    (∀ g : G, (fun n => g * n * g⁻¹) '' (N : Set G) = (N : Set G)) ↔
      ∀ g : G, leftCoset N g = rightCoset N g := by
  constructor
  · intro h g
    have hconj := (conjugation_iff_conjugate_eq G N).mpr h
    apply Set.Subset.antisymm
    · rintro _ ⟨n, hn, rfl⟩
      exact ⟨g * n * g⁻¹, hconj g n hn, by simp [mul_assoc]⟩
    · rintro _ ⟨n, hn, rfl⟩
      refine ⟨g⁻¹ * n * g, ?_, ?_⟩
      · simpa only [inv_inv, SetLike.mem_coe] using hconj g⁻¹ n hn
      · simp [mul_assoc]
  · intro h
    apply (conjugation_iff_conjugate_eq G N).mp
    intro g n hn
    have hmem : g * n ∈ leftCoset N g := ⟨n, hn, rfl⟩
    rw [h g] at hmem
    obtain ⟨m, hm, heq⟩ := hmem
    have hcancel : m = g * n * g⁻¹ := by
      calc
        m = (m * g) * g⁻¹ := by simp [mul_assoc]
        _ = (g * n) * g⁻¹ := congrArg (fun x => x * g⁻¹) heq
    exact hcancel ▸ hm

theorem normal_iff_conjugate_eq (G : Type u) [Group G] (N : Subgroup G) :
    N.Normal ↔ ∀ g : G, (fun n => g * n * g⁻¹) '' (N : Set G) = (N : Set G) :=
  (D07.Ch01.KernelImage.normal_iff_conjugation G N).trans
    (conjugation_iff_conjugate_eq G N)

theorem normal_iff_cosets_eq (G : Type u) [Group G] (N : Subgroup G) :
    N.Normal ↔ ∀ g : G, leftCoset N g = rightCoset N g :=
  (normal_iff_conjugate_eq G N).trans (conjugate_eq_iff_cosets_eq G N)

theorem kernel_normal (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) : f.ker.Normal :=
  D07.Ch01.KernelImage.kernel_normal G H f

theorem normal_is_kernel (G : Type u) [Group G] (N : Subgroup G) (hN : N.Normal) :
    ∃ (H : Type u) (_ : Group H) (f : G →* H), f.ker = N := by
  let : N.Normal := hN
  exact ⟨G ⧸ N, inferInstance, QuotientGroup.mk' N,
    D07.Ch01.GroupNormalQuotient.projection_kernel G N⟩

end D07.Ch04.NormalityEquivalences
