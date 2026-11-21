import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.H2Classification
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.CyclicTwo

namespace ALG02GroupTheory.Extensions.CyclicTwo

open NormalizedCohomology H2Classification
open _root_.Specs.ALG02GroupTheory.Extensions
open _root_.Specs.ALG02GroupTheory.Extensions.H2Classification
open _root_.Specs.ALG02GroupTheory.Extensions.CyclicTwo
open scoped _root_.Specs.ALG02GroupTheory.Extensions.CyclicTwo

-- Use the specified action even when elaborating a standalone scalar multiplication.
local instance : SMul C2 A := trivialAction.toMulAction.toSMul

private theorem eq_zero_or_one (a : A) : a = 0 ∨ a = 1 := by
  have h := ZMod.val_lt a
  rcases (show a.val = 0 ∨ a.val = 1 by omega) with hzero | hone
  · exact Or.inl ((ZMod.val_eq_zero a).mp hzero)
  · exact Or.inr ((ZMod.val_eq_one (by decide) a).mp hone)

private theorem eq_one_or_t (q : C2) : q = 1 ∨ q = t :=
  (eq_zero_or_one q.toAdd).imp (congrArg Multiplicative.ofAdd) (congrArg Multiplicative.ofAdd)

private theorem t_ne_one : t ≠ 1 := by decide

private theorem t_mul_t : t * t = 1 := by decide

private theorem add_self (a : A) : a + a = 0 := by
  rw [← two_mul]
  change (2 : ZMod 2) * a = 0
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

@[local simp] private theorem trivial_smul (q : C2) (a : A) : q • a = a := rfl

private def cochain (a : A) (p : C2 × C2) : A := if p = (t, t) then a else 0

@[local simp] private theorem cochain_at_t (a : A) : cochain a (t, t) = a := by
  simp [cochain]

@[local simp] private theorem cochain_one_left (a : A) (r : C2) : cochain a (1, r) = 0 := by
  simp [cochain, t_ne_one.symm]

@[local simp] private theorem cochain_one_right (a : A) (q : C2) : cochain a (q, 1) = 0 := by
  simp [cochain, t_ne_one.symm]

private def cocycle (a : A) : NormalizedCocycle C2 A :=
  ⟨⟨cochain a, by
      change IsTwoCocycle (cochain a)
      intro q r s
      rcases eq_one_or_t q with rfl | rfl
      · simp
      rcases eq_one_or_t r with rfl | rfl
      · simp
      rcases eq_one_or_t s with rfl | rfl
      · simp
      · simp [t_mul_t]⟩,
    fun q => ⟨cochain_one_left a q, cochain_one_right a q⟩⟩

@[local simp] private theorem cocycle_at_t (a : A) : (cocycle a).val.val (t, t) = a :=
  cochain_at_t a

private theorem cocycle_eq (c : NormalizedCocycle C2 A) : cocycle (c.val.val (t, t)) = c := by
  apply Subtype.ext
  apply Subtype.ext
  funext p
  obtain ⟨q, r⟩ := p
  change cochain (c.val.val (t, t)) (q, r) = c.val.val (q, r)
  rcases eq_one_or_t q with rfl | rfl
  · simp [(c.property r).1]
  rcases eq_one_or_t r with rfl | rfl
  · simp [(c.property t).2]
  · simp

theorem normalized_cocycles : NormalizedCocycles := by
  intro a
  refine ⟨cocycle a, cocycle_at_t a, ?_⟩
  intro c hc
  exact (cocycle_eq c).symm.trans (congrArg cocycle hc)

theorem normalized_coboundaries : NormalizedCoboundaries := by
  intro a ha
  simp [differential, t_mul_t, ha, add_self]

private theorem class_eq_iff_eval_eq (c d : NormalizedCocycle C2 A) :
    classOf C2 A c.val = classOf C2 A d.val ↔ c.val.val (t, t) = d.val.val (t, t) := by
  constructor
  · intro h
    obtain ⟨a, ha, hcd⟩ := (normalized_class_eq_iff c.val d.val c.property d.property).mp h
    exact sub_eq_zero.mp ((hcd t t).trans (normalized_coboundaries a ha))
  · intro h
    rw [← cocycle_eq c, ← cocycle_eq d, h]

private def cocycleHom : A →+ TwoCocycle C2 A where
  toFun a := (cocycle a).val
  map_zero' := by
    apply Subtype.ext
    funext p
    change cochain 0 p = 0
    simp [cochain]
  map_add' a b := by
    apply Subtype.ext
    funext p
    change cochain (a + b) p = cochain a p + cochain b p
    by_cases hp : p = (t, t) <;> simp [cochain, hp]

private def classHom : A →+ H2 C2 A := (classOf C2 A).comp cocycleHom

private theorem classHom_bijective : Function.Bijective classHom := by
  constructor
  · intro a b h
    change classOf C2 A (cocycle a).val = classOf C2 A (cocycle b).val at h
    simpa using (class_eq_iff_eval_eq _ _).mp h
  · intro x
    obtain ⟨c, hc, heq⟩ := exists_normalized_representative x
    let d : NormalizedCocycle C2 A := ⟨c, hc⟩
    refine ⟨d.val.val (t, t), ?_⟩
    change classOf C2 A (cocycle (d.val.val (t, t))).val = x
    rw [cocycle_eq]
    exact heq

theorem evaluation_equivalence : EvaluationEquivalence := by
  let e := AddEquiv.ofBijective classHom classHom_bijective
  refine ⟨e.symm, fun c => e.symm_apply_eq.mpr ?_⟩
  change classOf C2 A c.val = classOf C2 A (cocycle (c.val.val (t, t))).val
  rw [cocycle_eq]

theorem extension_correspondence : ExtensionCorrespondence := by
  constructor
  · obtain ⟨e, he⟩ := evaluation_equivalence
    refine ⟨(extensionClassification C2 A).trans e.toEquiv, ?_⟩
    intro c h
    change e (extensionToH2 C2 A (crossedProductClass c)) = c.val.val (t, t)
    rw [extensionToH2_crossedProductClass]
    exact he c
  · intro E _ S hS
    obtain ⟨s⟩ := normalizedSectionExists (S := S)
    obtain ⟨c, hc⟩ := exists_sectionCocycle S hS s
    let e := sectionCoordinates hS hc
    refine ⟨c, ⟨e⟩, ?_⟩
    rintro d ⟨f⟩
    have h := (extension_class_eq_iff (cocycleExtension d) (cocycleExtension c)
      (crossedProduct_action d) (crossedProduct_action c) _ _ d c
      (crossedProduct_recovery d) (crossedProduct_recovery c)).mpr ⟨f.trans e.symm⟩
    rw [← cocycle_eq d, ← cocycle_eq c, (class_eq_iff_eval_eq d c).mp h]

private theorem class_eq_zero_iff (c : NormalizedCocycle C2 A) :
    classOf C2 A c.val = 0 ↔ c.val.val (t, t) = 0 := by
  obtain ⟨e, he⟩ := evaluation_equivalence
  rw [← e.injective.eq_iff, he, map_zero]

theorem split_case : SplitCase := by
  intro c hc
  have hz := (class_eq_zero_iff c).mpr hc
  refine ⟨hz, (zero_class_iff_splitting (cocycleExtension c) (crossedProduct_action c)
    _ c (crossedProduct_recovery c)).1.mp hz, ?_⟩
  have hcz (q r : C2) : c.val.val (q, r) = 0 := by
    rw [← cocycle_eq c, hc]
    change cochain 0 (q, r) = 0
    simp [cochain]
  let f : Middle c →* (Multiplicative A × C2) :=
    { toFun := fun x => (x.left, x.right)
      map_one' := rfl
      map_mul' := by
        intro x y
        rw [(crossedProduct_formula c).1 x y]
        apply Prod.ext
        · change Multiplicative.ofAdd
            (x.left.toAdd + x.right • y.left.toAdd + c.val.val (x.right, y.right)) =
              Multiplicative.ofAdd (x.left.toAdd + y.left.toAdd)
          simp [hcz]
        · rfl }
  exact ⟨GroupExtension.Equiv.ofMonoidHom f (MonoidHom.ext fun _ => rfl)
    (MonoidHom.ext fun _ => rfl)⟩

private def middleEquivPair (c : NormalizedCocycle C2 A) : Middle c ≃ (ZMod 2 × ZMod 2) where
  toFun x := (x.left.toAdd, x.right.toAdd)
  invFun x := ⟨Multiplicative.ofAdd x.1, Multiplicative.ofAdd x.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

private theorem card_middle (c : NormalizedCocycle C2 A) : Nat.card (Middle c) = 4 := by
  simp [Nat.card_congr (middleEquivPair c)]

theorem cyclic_case : CyclicCase := by
  intro c hc
  have hc1 := (eq_zero_or_one (c.val.val (t, t))).resolve_left hc
  have hsquare : (lift c) ^ 2 = (cocycleExtension c).inl (Multiplicative.ofAdd (1 : A)) := by
    rw [pow_two, (crossedProduct_formula c).1]
    change CrossedProductModel.mk
      (Multiplicative.ofAdd (0 + t • (0 : A) + c.val.val (t, t))) (t * t) =
        CrossedProductModel.mk (Multiplicative.ofAdd (1 : A)) (1 : C2)
    simp [hc1, t_mul_t]
  have hne : (lift c) ^ 2 ≠ 1 := by
    rw [hsquare, ← map_one (cocycleExtension c).inl]
    exact fun h => t_ne_one ((cocycleExtension c).inl_injective h)
  have hf : (lift c) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hsquare, ← map_pow]
    exact map_one (cocycleExtension c).inl
  have ho : orderOf (lift c) = 4 := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime_pow (p := 2) (n := 1) hne hf
  have hgen : Subgroup.zpowers (lift c) = ⊤ := by
    let : Finite (Middle c) := Finite.of_injective _ (middleEquivPair c).injective
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, ho, card_middle]
  have hmem (x : Middle c) : x ∈ Subgroup.zpowers (lift c) := by
    rw [hgen]
    exact Subgroup.mem_top x
  exact ⟨fun h => hc ((class_eq_zero_iff c).mp h), rfl, hsquare, ho, hgen,
    zmodMulEquivOfGenerator hmem (card_middle c), zmodMulEquivOfGenerator_apply_ofAdd_one _ _⟩

theorem distinct_extensions : DistinctExtensions := by
  intro c d hc hd
  have hneq : classOf C2 A c.val ≠ classOf C2 A d.val := by
    intro h
    exact hd (((class_eq_iff_eval_eq c d).mp h).symm.trans hc)
  refine ⟨crossedProduct_action c, crossedProduct_action d, hneq, fun h => hneq ?_⟩
  exact (extension_class_eq_iff (cocycleExtension c) (cocycleExtension d)
    (crossedProduct_action c) (crossedProduct_action d) _ _ c d
    (crossedProduct_recovery c) (crossedProduct_recovery d)).mpr h

end ALG02GroupTheory.Extensions.CyclicTwo
