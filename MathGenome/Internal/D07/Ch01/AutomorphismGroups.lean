import MathGenome.Internal.D07.Ch01.IsomorphismDefinition
import MathGenome.Internal.D07.Ch01.KernelImage
import MathGenome.Internal.D07.Ch01.GroupNormalQuotient
import MathGenome.Internal.Specs.D07.Ch01.AutomorphismGroups
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
Automorphisms and conjugation, `K07.01.automorphism_groups`.
The kernel computation identifies trivial conjugation with commuting with
every element. The first isomorphism theorem then gives the specified map
from the quotient by the center onto the inner automorphisms.
-/

namespace D07.Ch01.AutomorphismGroups

universe u

/-- The group of automorphisms of the given group. -/
abbrev Aut (G : Type u) [Group G] : Type u := MulAut G

/-- The homomorphism sending an element to conjugation by that element. -/
def conjugation (G : Type u) [Group G] : G →* Aut G := MulAut.conj

/-- Inner automorphisms form the image subgroup of conjugation. -/
def Inner (G : Type u) [Group G] : Subgroup (Aut G) := (conjugation G).range

theorem automorphism_group_laws (G : Type u) [Group G] :
    GroupDefinition.groupAxioms (Aut G) (· * ·) 1 Inv.inv :=
  GroupDefinition.group_laws (Aut G)

theorem automorphism_operations (G : Type u) [Group G] :
    (∀ f g : Aut G, ((f * g : Aut G) : G → G) = f ∘ g) ∧
    (1 : Aut G) = MulEquiv.refl G ∧
    (∀ f : Aut G, f⁻¹ = f.symm) :=
  ⟨fun _ _ => rfl, rfl, fun _ => rfl⟩

theorem conjugation_formula (G : Type u) [Group G] (g x : G) :
    conjugation G g x = g * x * g⁻¹ := rfl

theorem conjugation_multiplicative (G : Type u) [Group G] (g h : G) :
    conjugation G (g * h) = conjugation G g * conjugation G h :=
  (conjugation G).map_mul g h

theorem center_carrier (G : Type u) [Group G] :
    (Subgroup.center G : Set G) = {z : G | ∀ x : G, z * x = x * z} := by
  ext z
  exact Subgroup.mem_center_iff.trans
    ⟨fun h x => (h x).symm, fun h x => (h x).symm⟩

theorem conjugation_kernel (G : Type u) [Group G] :
    (conjugation G).ker = Subgroup.center G := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hg x
    have hx : g * x * g⁻¹ = x := DFunLike.congr_fun hg x
    have hcomm : g * x = x * g := (mul_inv_eq_iff_eq_mul).mp hx
    exact hcomm.symm
  · intro hg
    apply MulEquiv.ext
    intro x
    change g * x * g⁻¹ = x
    rw [← hg x, mul_inv_cancel_right]

theorem center_normal (G : Type u) [Group G] : (Subgroup.center G).Normal := by
  rw [← conjugation_kernel G]
  exact KernelImage.kernel_normal G (Aut G) (conjugation G)

theorem inner_carrier (G : Type u) [Group G] :
    (Inner G : Set (Aut G)) = {f : Aut G | ∃ g : G, conjugation G g = f} := rfl

theorem quotient_center_iso_inner (G : Type u) [Group G] :
    ∃ e : G ⧸ Subgroup.center G ≃* Inner G,
      ∀ g : G, (e (QuotientGroup.mk' (Subgroup.center G) g) : Aut G) =
        conjugation G g := by
  let e := (QuotientGroup.quotientMulEquivOfEq (conjugation_kernel G).symm).trans
    (QuotientGroup.quotientKerEquivRange (conjugation G))
  exact ⟨e, fun _ => rfl⟩

theorem inner_of_abelian (G : Type u) [Group G] (h : GroupDefinition.IsAbelian G)
    (g : G) : conjugation G g = 1 := by
  apply MulEquiv.ext
  intro x
  change g * x * g⁻¹ = x
  rw [h g x, mul_inv_cancel_right]

theorem inner_eq_bot_of_abelian (G : Type u) [Group G]
    (h : GroupDefinition.IsAbelian G) : Inner G = ⊥ := by
  apply le_antisymm _ bot_le
  rintro f ⟨g, rfl⟩
  exact Subgroup.mem_bot.mpr (inner_of_abelian G h g)

theorem integer_negation_outer :
    ∃ e : ℤ ≃+ ℤ,
      (∀ x : ℤ, e x = -x) ∧ e ≠ AddEquiv.refl ℤ ∧
        ¬ ∃ g : ℤ, ∀ x : ℤ, e x = g + x + -g := by
  let e : ℤ ≃+ ℤ :=
    { toFun := fun x => -x
      invFun := fun x => -x
      left_inv := neg_neg
      right_inv := neg_neg
      map_add' := neg_add }
  refine ⟨e, fun _ => rfl, ?_, ?_⟩
  · intro he
    have h1 : e 1 ≠ (AddEquiv.refl ℤ) 1 := by decide
    exact h1 (DFunLike.congr_fun he 1)
  · rintro ⟨g, hg⟩
    have h1 : (-1 : ℤ) = g + 1 + -g := hg 1
    have hc : g + 1 + -g = (1 : ℤ) := by
      rw [add_comm g 1, add_neg_cancel_right]
    exact (by decide : (-1 : ℤ) ≠ 1) (h1.trans hc)

end D07.Ch01.AutomorphismGroups
