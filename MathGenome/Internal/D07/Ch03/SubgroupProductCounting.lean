import MathGenome.Internal.D07.Ch03.CosetBijections
import MathGenome.Internal.Specs.D07.Ch03.SubgroupProductCounting

/-!
# Products of subgroups as sets
K07.03.subgroup_product_counting (paper.tex:627–641).
A representation of `hk` is uniquely `(ht, t⁻¹k)` for `t ∈ H ⊓ K`.
This gives the fibre count and, by counting all fibres, the product formula.
The subgroup criterion and normality statements do not require finiteness.
-/
namespace D07.Ch03.SubgroupProductCounting

open scoped Pointwise
universe u
variable {G : Type u} [Group G]

/-- The parametrization of the fibre over a specified product. -/
def representationEquiv (H K : Subgroup G) (h : H) (k : K) :
    ↥(H ⊓ K) ≃ {p : H × K // (p.1 : G) * (p.2 : G) = (h : G) * (k : G)} where
  toFun t := ⟨(⟨(h : G) * t, H.mul_mem h.property t.property.1⟩,
    ⟨(t : G)⁻¹ * k, K.mul_mem (K.inv_mem t.property.2) k.property⟩), by
      simp only [mul_assoc, mul_inv_cancel_left]⟩
  invFun p := ⟨(h : G)⁻¹ * (p.val.1 : G), H.mul_mem (H.inv_mem h.property) p.val.1.property, by
    have he : (h : G)⁻¹ * (p.val.1 : G) = (k : G) * (p.val.2 : G)⁻¹ := by
      calc
        (h : G)⁻¹ * (p.val.1 : G) =
            (h : G)⁻¹ * ((p.val.1 : G) * (p.val.2 : G)) * (p.val.2 : G)⁻¹ := by
              simp only [mul_assoc, mul_inv_cancel, mul_one]
        _ = (k : G) * (p.val.2 : G)⁻¹ := by rw [p.property]; simp only [inv_mul_cancel_left]
    rw [he]
    exact K.mul_mem k.property (K.inv_mem p.val.2.property)⟩
  left_inv t := Subtype.ext (inv_mul_cancel_left _ _)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (mul_inv_cancel_left _ _)
    · apply Subtype.ext
      change ((h : G)⁻¹ * (p.val.1 : G))⁻¹ * (k : G) = (p.val.2 : G)
      calc
        _ = (p.val.1 : G)⁻¹ * ((h : G) * (k : G)) := by
          simp only [mul_inv_rev, inv_inv, mul_assoc]
        _ = (p.val.1 : G)⁻¹ * ((p.val.1 : G) * (p.val.2 : G)) :=
          congrArg (fun z : G => (p.val.1 : G)⁻¹ * z) p.property.symm
        _ = (p.val.2 : G) := inv_mul_cancel_left _ _

/-- Every nonempty multiplication fibre is in bijection with the intersection,
without a finiteness assumption. -/
theorem representation_equiv_exists (H K : Subgroup G) (x : G)
    (hx : x ∈ (H : Set G) * (K : Set G)) :
    Nonempty (↥(H ⊓ K) ≃ {p : H × K // (p.1 : G) * (p.2 : G) = x}) := by
  obtain ⟨h, hh, k, hk, rfl⟩ := hx
  exact ⟨representationEquiv H K ⟨h, hh⟩ ⟨k, hk⟩⟩

theorem representation_count (G : Type u) [Group G] (H K : Subgroup G)
    [Finite H] [Finite K] (x : G) (hx : x ∈ (H : Set G) * (K : Set G)) :
    Nat.card {p : H × K // (p.1 : G) * (p.2 : G) = x} = Nat.card ↥(H ⊓ K) := by
  obtain ⟨e⟩ := representation_equiv_exists H K x hx
  exact Nat.card_congr e.symm

/-- Counting the multiplication map by its equally sized fibres. -/
theorem product_cardinality (G : Type u) [Group G] (H K : Subgroup G)
    [Finite H] [Finite K] :
    ((H : Set G) * (K : Set G)).Finite ∧
      Nat.card ↥((H : Set G) * (K : Set G)) =
        Nat.card H * Nat.card K / Nat.card ↥(H ⊓ K) := by
  classical
  let f : H × K → ↥((H : Set G) * (K : Set G)) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), p.1, p.1.property, p.2, p.2.property, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, h, hh, k, hk, he⟩
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext he⟩
  have : Finite ↥((H : Set G) * (K : Set G)) := Finite.of_surjective f hf
  have : Finite ↥(H ⊓ K) :=
    Finite.of_injective (Subgroup.inclusion (show H ⊓ K ≤ H from inf_le_left))
      (Subgroup.inclusion_injective _)
  let e (x : ↥((H : Set G) * (K : Set G))) : {p // f p = x} ≃ ↥(H ⊓ K) :=
    (Equiv.subtypeEquivRight (fun _ => Subtype.ext_iff)).trans
      (Classical.choice (representation_equiv_exists H K x x.property)).symm
  have hc : Nat.card H * Nat.card K =
      Nat.card ↥((H : Set G) * (K : Set G)) * Nat.card ↥(H ⊓ K) := by
    simpa only [Nat.card_prod] using
      Nat.card_congr ((Equiv.sigmaFiberEquiv f).symm.trans
        (Equiv.sigmaEquivProdOfEquiv e))
  refine ⟨Set.toFinite _, ?_⟩
  rw [hc, Nat.mul_div_cancel]
  exact Nat.card_pos

theorem product_subgroup_iff (G : Type u) [Group G] (H K : Subgroup G) :
    (∃ L : Subgroup G, (L : Set G) = (H : Set G) * (K : Set G)) ↔
      (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G) := by
  constructor
  · rintro ⟨L, hL⟩
    calc
      (H : Set G) * (K : Set G) = (L : Set G) := hL.symm
      _ = (L : Set G)⁻¹ := inv_coe_set.symm
      _ = ((H : Set G) * (K : Set G))⁻¹ := congrArg Inv.inv hL
      _ = (K : Set G) * (H : Set G) := by rw [mul_inv_rev, inv_coe_set, inv_coe_set]
  · intro hcomm
    apply (D07.Ch01.SubgroupDefinitionTest.subgroup_iff_closed G _).2
    refine ⟨⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩, ?_, ?_⟩
    · rintro _ ⟨h, hh, k, hk, rfl⟩ _ ⟨h', hh', k', hk', rfl⟩
      have hkh : k * h' ∈ (H : Set G) * (K : Set G) := by
        rw [hcomm]
        exact ⟨k, hk, h', hh', rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := hkh
      change a * b = k * h' at hab
      refine ⟨h * a, H.mul_mem hh ha, b * k', K.mul_mem hb hk', ?_⟩
      calc
        (h * a) * (b * k') = h * (a * b) * k' := by simp only [mul_assoc]
        _ = (h * k) * (h' * k') := by rw [hab]; simp only [mul_assoc]
    · rintro _ ⟨h, hh, k, hk, rfl⟩
      rw [hcomm, mul_inv_rev]
      exact ⟨k⁻¹, K.inv_mem hk, h⁻¹, H.inv_mem hh, rfl⟩

theorem normal_left_product_comm (G : Type u) [Group G] (H K : Subgroup G) [H.Normal] :
    (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G) :=
  (Subgroup.set_mul_normal_comm (K : Set G) H).symm

theorem normal_right_product_comm (G : Type u) [Group G] (H K : Subgroup G) [K.Normal] :
    (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G) :=
  Subgroup.set_mul_normal_comm (H : Set G) K

/-- The subgroup `{1,s}` for an involution `s`. -/
private def involutionSubgroup (s : G) (hs : s * s = 1) : Subgroup G where
  carrier := {a | a = 1 ∨ a = s}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp [hs]
  inv_mem' := by
    rintro a (rfl | rfl)
    · simp
    · exact Or.inr (inv_eq_of_mul_eq_one_right hs)

/-- Two distinct transposition subgroups in `S₃` give a non-subgroup product. -/
theorem product_not_always_subgroup :
    ∃ H K : Subgroup (Equiv.Perm (Fin 3)),
      ¬ ∃ L : Subgroup (Equiv.Perm (Fin 3)),
        (L : Set (Equiv.Perm (Fin 3))) = (H : Set _) * (K : Set _) := by
  let s : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let t : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let H := involutionSubgroup s (by decide)
  let K := involutionSubgroup t (by decide)
  refine ⟨H, K, ?_⟩
  intro h
  have he := (product_subgroup_iff _ H K).mp h
  have hts : t * s ∈ (K : Set (Equiv.Perm (Fin 3))) * (H : Set (Equiv.Perm (Fin 3))) :=
    ⟨t, Or.inr rfl, s, Or.inr rfl, rfl⟩
  rw [← he] at hts
  obtain ⟨a, ha, b, hb, hab⟩ := hts
  change a = 1 ∨ a = s at ha
  change b = 1 ∨ b = t at hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    have : False := by
      have hh := congrArg (fun p : Equiv.Perm (Fin 3) => p 0) hab
      revert hh
      decide
  all_goals contradiction

end D07.Ch03.SubgroupProductCounting
