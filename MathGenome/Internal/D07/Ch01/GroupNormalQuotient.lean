import MathGenome.Internal.D07.Ch01.KernelImage
import MathGenome.Internal.D07.Ch03.CosetsPartition
import MathGenome.Internal.Specs.D07.Ch01.GroupNormalQuotient

/-!
# The normal quotient and unique descent

Lemma `normal-quotient-preliminary`, paper.tex:390–399.
Mathlib's quotient is by the relation `g⁻¹ * h ∈ N`. We first identify
its fibers with the shared set-valued left cosets. The group structure
and projection are the canonical ones for the given normal subgroup.
-/

namespace D07.Ch01.GroupNormalQuotient

open Specs.D07.Ch03.CosetsPartition

universe u v

theorem projection_fiber (G : Type u) [Group G] (N : Subgroup G) [N.Normal] (g : G) :
    {x : G | QuotientGroup.mk' N x = QuotientGroup.mk' N g} = leftCoset N g := by
  rw [← D07.Ch03.CosetsPartition.left_class_eq_coset G N g]
  ext x
  change ((x : G ⧸ N) = (g : G ⧸ N)) ↔ g⁻¹ * x ∈ N
  exact eq_comm.trans QuotientGroup.eq

theorem quotient_eq_iff_coset_eq (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (g h : G) : QuotientGroup.mk' N g = QuotientGroup.mk' N h ↔
      leftCoset N g = leftCoset N h := by
  constructor
  · intro heq
    rw [← projection_fiber G N g, ← projection_fiber G N h, heq]
  · intro heq
    have hg : g ∈ leftCoset N g := ⟨1, N.one_mem, mul_one g⟩
    rw [heq, ← projection_fiber G N h] at hg
    exact hg

theorem quotient_group_laws (G : Type u) [Group G] (N : Subgroup G) [N.Normal] :
    Specs.D07.Ch01.GroupDefinition.groupAxiomsValue (G ⧸ N) (· * ·) 1 Inv.inv :=
  ⟨mul_assoc, one_mul, mul_one, mul_inv_cancel, inv_mul_cancel⟩

theorem quotient_operations (G : Type u) [Group G] (N : Subgroup G) [N.Normal] :
    (∀ g h : G, QuotientGroup.mk' N g * QuotientGroup.mk' N h =
      QuotientGroup.mk' N (g * h)) ∧
    QuotientGroup.mk' N 1 = 1 ∧
    (∀ g : G, (QuotientGroup.mk' N g)⁻¹ = QuotientGroup.mk' N g⁻¹) :=
  ⟨fun g h => ((QuotientGroup.mk' N).map_mul g h).symm,
    (QuotientGroup.mk' N).map_one,
    fun g => (map_inv (QuotientGroup.mk' N) g).symm⟩

theorem product_independent (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (g g' h h' : G) (hg : leftCoset N g = leftCoset N g')
    (hh : leftCoset N h = leftCoset N h') :
    leftCoset N (g * h) = leftCoset N (g' * h') := by
  apply (quotient_eq_iff_coset_eq G N (g * h) (g' * h')).mp
  rw [map_mul, map_mul, (quotient_eq_iff_coset_eq G N g g').mpr hg,
    (quotient_eq_iff_coset_eq G N h h').mpr hh]

theorem projection_surjective (G : Type u) [Group G] (N : Subgroup G) [N.Normal] :
    Function.Surjective (QuotientGroup.mk' N) :=
  QuotientGroup.mk'_surjective N

theorem projection_kernel (G : Type u) [Group G] (N : Subgroup G) [N.Normal] :
    (QuotientGroup.mk' N).ker = N :=
  QuotientGroup.ker_mk' N

theorem descends_unique_iff (G : Type u) (H : Type v) [Group G] [Group H]
    (N : Subgroup G) [N.Normal] (f : G →* H) :
    (∃! fbar : G ⧸ N →* H, fbar.comp (QuotientGroup.mk' N) = f) ↔ N ≤ f.ker := by
  constructor
  · rintro ⟨fbar, hfactor, _⟩ n hn
    change f n = 1
    have hproj : QuotientGroup.mk' N n = 1 := QuotientGroup.eq_one_iff n |>.mpr hn
    calc
      f n = fbar (QuotientGroup.mk' N n) := (DFunLike.congr_fun hfactor n).symm
      _ = fbar 1 := congrArg fbar hproj
      _ = 1 := fbar.map_one
  · intro hN
    refine ⟨QuotientGroup.lift N f hN, QuotientGroup.lift_comp_mk' N f hN, ?_⟩
    intro fbar hfactor
    apply QuotientGroup.monoidHom_ext
    exact hfactor.trans (QuotientGroup.lift_comp_mk' N f hN).symm

end D07.Ch01.GroupNormalQuotient
