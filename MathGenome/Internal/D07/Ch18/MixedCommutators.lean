import MathGenome.Internal.Specs.D07.Ch18.MixedCommutators

/-!
Commutators of arbitrary subgroups, `K07.18.mixed_commutators`.
The library's mixed bracket is ordinary closure with precisely the source's
commutator convention. Its image theorem holds for every homomorphism.

For the final criterion, projection kills the mixed commutator exactly when
its image is trivial. The image theorem and surjectivity of projection identify
that image with `[G/N, image(A)]`, whose triviality says `image(A)` is central.
The two quotient-product bridges make the source's `AN/N` explicit.
-/

namespace D07.Ch18.MixedCommutators

open scoped commutatorElement

universe u v

theorem commutator_generated (G : Type u) [Group G] (A B : Subgroup G) :
    ⁅A, B⁆ = Subgroup.closure
      {z : G | ∃ a ∈ A, ∃ b ∈ B, a * b * a⁻¹ * b⁻¹ = z} := by
  simpa only [commutatorElement_def] using Subgroup.commutator_def A B

theorem element_commutator_inverse (G : Type u) [Group G] (a b : G) :
    (a * b * a⁻¹ * b⁻¹)⁻¹ = b * a * b⁻¹ * a⁻¹ := by
  simpa only [commutatorElement_def] using commutatorElement_inv a b

theorem element_commutator_map (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) (a b : G) :
    f (a * b * a⁻¹ * b⁻¹) = f a * f b * (f a)⁻¹ * (f b)⁻¹ := by
  simpa only [commutatorElement_def] using map_commutatorElement f a b

theorem commutator_symmetry (G : Type u) [Group G] (A B : Subgroup G) :
    ⁅A, B⁆ = ⁅B, A⁆ :=
  Subgroup.commutator_comm A B

theorem commutator_monotone (G : Type u) [Group G] (A B A' B' : Subgroup G)
    (hA : A ≤ A') (hB : B ≤ B') : ⁅A, B⁆ ≤ ⁅A', B'⁆ :=
  Subgroup.commutator_mono hA hB

theorem commutator_image (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) (A B : Subgroup G) :
    (⁅A, B⁆).map f = ⁅A.map f, B.map f⁆ :=
  Subgroup.map_commutator A B f

theorem commutator_image_set (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) (A B : Subgroup G) :
    f '' ((⁅A, B⁆ : Subgroup G) : Set G) = ((⁅A.map f, B.map f⁆ : Subgroup H) : Set H) := by
  rw [← Subgroup.coe_map, commutator_image G H f A B]

theorem automorphism_image (G : Type u) [Group G] (α : MulAut G)
    (A B : Subgroup G) :
    (⁅A, B⁆).map α.toMonoidHom = ⁅A.map α.toMonoidHom, B.map α.toMonoidHom⁆ :=
  commutator_image G G α.toMonoidHom A B

theorem commutator_characteristic (G : Type u) [Group G] (A B : Subgroup G)
    (hA : A.Characteristic) (hB : B.Characteristic) : (⁅A, B⁆).Characteristic := by
  let := hA
  let := hB
  exact Subgroup.commutator_characteristic A B

theorem commutator_normal (G : Type u) [Group G] (A B : Subgroup G)
    (hA : A.Normal) (hB : B.Normal) : (⁅A, B⁆).Normal := by
  let := hA
  let := hB
  exact Subgroup.commutator_normal A B

theorem normal_element_commutator (G : Type u) [Group G] (A : Subgroup G)
    (hA : A.Normal) (a : G) (ha : a ∈ A) (g : G) :
    a * g * a⁻¹ * g⁻¹ ∈ A := by
  simpa only [mul_assoc] using A.mul_mem ha (hA.conj_mem a⁻¹ (A.inv_mem ha) g)

theorem normal_commutator_le (G : Type u) [Group G] (A : Subgroup G)
    (hA : A.Normal) : ⁅A, (⊤ : Subgroup G)⁆ ≤ A := by
  let := hA
  exact Subgroup.commutator_le_left A ⊤

theorem quotient_product_image (G : Type u) [Group G] (A N : Subgroup G)
    [N.Normal] :
    (A ⊔ N).map (QuotientGroup.mk' N) = A.map (QuotientGroup.mk' N) := by
  have hN : N.map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [Subgroup.map_sup, hN, sup_bot_eq]

theorem quotient_product_membership (G : Type u) [Group G] (A N : Subgroup G)
    [N.Normal] (z : G ⧸ N) :
    z ∈ (A ⊔ N).map (QuotientGroup.mk' N) ↔
      ∃ a ∈ A, ∃ n ∈ N, QuotientGroup.mk' N (a * n) = z := by
  rw [quotient_product_image G A N]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, 1, N.one_mem, by rw [mul_one]⟩
  · rintro ⟨a, ha, n, hn, rfl⟩
    have hn' : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, hn', mul_one]
    exact Subgroup.mem_map_of_mem _ ha

theorem quotient_center_criterion (G : Type u) [Group G] (A N : Subgroup G)
    [N.Normal] :
    ⁅(⊤ : Subgroup G), A⁆ ≤ N ↔
      (A ⊔ N).map (QuotientGroup.mk' N) ≤ Subgroup.center (G ⧸ N) := by
  have hker : ⁅(⊤ : Subgroup G), A⁆ ≤ N ↔
      (⁅(⊤ : Subgroup G), A⁆).map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [quotient_product_image G A N, hker, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  exact Subgroup.commutator_top_left_eq_bot_iff_le_center

end D07.Ch18.MixedCommutators
