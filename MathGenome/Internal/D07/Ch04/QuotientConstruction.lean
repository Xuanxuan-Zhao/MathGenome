import MathGenome.Internal.D07.Ch04.NormalityEquivalences
import MathGenome.Internal.Specs.D07.Ch04.QuotientConstruction

/-!
The quotient group, `K07.04.quotient_construction` (paper.tex:670–680).
The shared preliminary construction supplies the canonical group laws and
projection. For the converse, apply representative independence to `nN = N`
and multiply on the right by `g⁻¹N`. The resulting equality forces
`g * n * g⁻¹ ∈ N`, giving normality without assuming it.
-/

namespace D07.Ch04.QuotientConstruction

open Specs.D07.Ch03.CosetsPartition

universe u

theorem quotient_eq_iff_coset_eq (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (g h : G) : QuotientGroup.mk' N g = QuotientGroup.mk' N h ↔
      leftCoset N g = leftCoset N h :=
  D07.Ch01.GroupNormalQuotient.quotient_eq_iff_coset_eq G N g h

theorem quotient_group_laws (G : Type u) [Group G] (N : Subgroup G) [N.Normal] :
    Specs.D07.Ch01.GroupDefinition.groupAxiomsValue (G ⧸ N) (· * ·) 1 Inv.inv :=
  D07.Ch01.GroupNormalQuotient.quotient_group_laws G N

theorem quotient_operations (G : Type u) [Group G] (N : Subgroup G) [N.Normal] :
    (∀ g h : G, QuotientGroup.mk' N g * QuotientGroup.mk' N h =
      QuotientGroup.mk' N (g * h)) ∧
    QuotientGroup.mk' N 1 = 1 ∧
    (∀ g : G, (QuotientGroup.mk' N g)⁻¹ = QuotientGroup.mk' N g⁻¹) :=
  D07.Ch01.GroupNormalQuotient.quotient_operations G N

theorem identity_coset (G : Type u) [Group G] (N : Subgroup G) :
    leftCoset N 1 = (N : Set G) := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    simpa only [one_mul] using hn
  · intro hx
    exact ⟨x, hx, one_mul x⟩

theorem projection_surjective (G : Type u) [Group G] (N : Subgroup G) [N.Normal] :
    Function.Surjective (QuotientGroup.mk' N) :=
  D07.Ch01.GroupNormalQuotient.projection_surjective G N

theorem projection_kernel (G : Type u) [Group G] (N : Subgroup G) [N.Normal] :
    (QuotientGroup.mk' N).ker = N :=
  D07.Ch01.GroupNormalQuotient.projection_kernel G N

theorem product_independent_iff_normal (G : Type u) [Group G] (N : Subgroup G) :
    (∀ g g' h h' : G,
      leftCoset N g = leftCoset N g' → leftCoset N h = leftCoset N h' →
        leftCoset N (g * h) = leftCoset N (g' * h')) ↔ N.Normal := by
  constructor
  · intro hind
    apply (D07.Ch01.KernelImage.normal_iff_conjugation G N).mpr
    intro g n hn
    have hncoset : leftCoset N n = leftCoset N 1 := by
      rw [← D07.Ch03.CosetsPartition.left_class_eq_coset G N n,
        ← D07.Ch03.CosetsPartition.left_class_eq_coset G N 1]
      ext x
      change (n⁻¹ * x ∈ N) ↔ 1⁻¹ * x ∈ N
      simp only [inv_one, one_mul]
      constructor
      · intro hx
        simpa only [mul_inv_cancel_left] using N.mul_mem hn hx
      · intro hx
        exact N.mul_mem (N.inv_mem hn) hx
    have heq := hind n 1 g⁻¹ g⁻¹ hncoset rfl
    have hmem : n * g⁻¹ ∈ leftCoset N (1 * g⁻¹) :=
      heq ▸ (show n * g⁻¹ ∈ leftCoset N (n * g⁻¹) from
        ⟨1, N.one_mem, mul_one _⟩)
    rw [← D07.Ch03.CosetsPartition.left_class_eq_coset G N (1 * g⁻¹)] at hmem
    simpa only [Set.mem_ofPred_eq, one_mul, inv_inv, ← mul_assoc] using hmem
  · intro hN
    let : N.Normal := hN
    exact D07.Ch01.GroupNormalQuotient.product_independent G N

theorem quotient_bottom (G : Type u) [Group G] :
    ∃ e : G ⧸ (⊥ : Subgroup G) ≃* G,
      ∀ g : G, e (QuotientGroup.mk' (⊥ : Subgroup G) g) = g := by
  let e := QuotientGroup.liftEquiv (⊥ : Subgroup G)
    (φ := MonoidHom.id G) Function.surjective_id (by ext x; simp)
  exact ⟨e, fun _ => rfl⟩

theorem quotient_top_trivial (G : Type u) [Group G]
    (q : G ⧸ (⊤ : Subgroup G)) : q = 1 := by
  obtain ⟨g, rfl⟩ := projection_surjective G (⊤ : Subgroup G) q
  exact (QuotientGroup.eq_one_iff g).mpr (Subgroup.mem_top g)

end D07.Ch04.QuotientConstruction
