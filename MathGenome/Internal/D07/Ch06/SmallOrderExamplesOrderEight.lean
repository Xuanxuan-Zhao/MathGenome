import MathGenome.Internal.Specs.D07.Ch06.SmallOrderExamplesOrderEight
import MathGenome.Internal.D07.Ch03.FiniteElementOrders
import MathGenome.Internal.D07.Ch04.IndexTwoNormal
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Push
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Sets
import Mathlib.Algebra.Group.Semiconj.Basic

/-! The order-eight part of `K07.06.small_order_examples`. -/
namespace D07.Ch06.SmallOrderExamplesOrderEight

open Specs.D07.Ch06.SmallOrderExamplesOrderEight

/-- An isomorphism preserves the set of solutions of `x^n = 1`. -/
def rootsEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    {x : G // x ^ n = 1} ≃ {y : H // y ^ n = 1} where
  toFun x := ⟨e x, by simp [← map_pow, x.property]⟩
  invFun y := ⟨e.symm y, by simp [← map_pow, y.property]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

/-- Identity is included in this count. In particular it is one more than the
number of involutions when `n = 2`. -/
noncomputable def rootsCount (G : Type*) [Group G] (n : ℕ) : ℕ :=
  Nat.card {x : G // x ^ n = 1}

lemma rootsCount_invariant {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (n : ℕ) : rootsCount G n = rootsCount H n :=
  Nat.card_congr (rootsEquiv e n)

theorem model_cardinalities : ModelCardinalities := by
  intro i
  fin_cases i <;>
    simp [Model, Nat.card_eq_fintype_card, Fintype.card_prod,
      Fintype.card_multiplicative, ZMod.card, DihedralGroup.card, QuaternionGroup.card]

/-- The pair (number of square roots of one, number of fourth roots of one)
is a complete distinguishing invariant for this list. -/
lemma model_root_counts :
    ∀ i : Fin 5, (rootsCount (Model i) 2, rootsCount (Model i) 4) =
      ![(2, 4), (4, 8), (8, 8), (6, 8), (2, 8)] i := by
  intro i
  fin_cases i <;> unfold rootsCount
  all_goals rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  all_goals decide

theorem pairwise_nonisomorphic : PairwiseNonisomorphic := by
  intro i j
  constructor
  · rintro ⟨e⟩
    have h : (rootsCount (Model i) 2, rootsCount (Model i) 4) =
        (rootsCount (Model j) 2, rootsCount (Model j) 4) :=
      Prod.ext (rootsCount_invariant e 2) (rootsCount_invariant e 4)
    rw [model_root_counts, model_root_counts] at h
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro rfl
    exact ⟨MulEquiv.refl _⟩

theorem model_normal_forms : ModelNormalForms := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · decide
    · decide
    · simp only [ExistsUnique]; decide
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · decide
    · decide
    · simp only [ExistsUnique]; decide

/-- Multiplication of powers indexed by residues, derived from the exact order. -/
lemma power_val_add {G : Type*} [Group G] (a : G) (ha : orderOf a = 4)
    (i j : Fin 4) : a ^ (i + j).val = a ^ i.val * a ^ j.val := by
  change a ^ ((i.val + j.val) % 4) = _
  have h := pow_mod_orderOf a (i.val + j.val)
  rw [ha] at h
  exact h.trans (pow_add a _ _)

lemma power_val_neg {G : Type*} [Group G] (a : G) (ha : orderOf a = 4)
    (i : Fin 4) : a ^ (-i).val = (a ^ i.val)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← power_val_add a ha]
  have hz : (-i + i : Fin 4) = 0 := by fin_cases i <;> decide
  rw [hz]; simp

/-- The multiplication of coordinates forced by the two presentations. -/
def coordinateMul (q : Bool) : (Fin 4 × Bool) → (Fin 4 × Bool) → (Fin 4 × Bool)
  | (i, false), (j, false) => ((i : ZMod 4) + j, false)
  | (i, false), (j, true) => ((i : ZMod 4) + j, true)
  | (i, true), (j, false) => ((i : ZMod 4) - j, true)
  | (i, true), (j, true) => ((i : ZMod 4) - j + (if q then 2 else 0), false)

lemma word_mul {G : Type*} [Group G] (a b : G) (q : Bool)
    (ha : orderOf a = 4) (hc : b * a * b⁻¹ = a⁻¹)
    (hb : b ^ 2 = if q then a ^ 2 else 1) (p r : Fin 4 × Bool) :
    word a b (coordinateMul q p r) = word a b p * word a b r := by
  have hs : SemiconjBy b a a⁻¹ := (mul_inv_eq_iff_eq_mul).mp hc
  have hs' (j : Fin 4) : b * a ^ j.val = a ^ (-j).val * b := by
    rw [power_val_neg a ha]
    simpa [SemiconjBy, inv_pow] using hs.pow_right j.val
  rcases p with ⟨i, ep⟩
  rcases r with ⟨j, er⟩
  cases ep <;> cases er
  · exact power_val_add a ha i j
  · change a ^ ((i : ZMod 4) + j).val * b = a ^ i.val * (a ^ j.val * b)
    rw [power_val_add a ha i j, mul_assoc]
  · change a ^ ((i : ZMod 4) - j).val * b = (a ^ i.val * b) * a ^ j.val
    rw [sub_eq_add_neg, power_val_add a ha i (-j), mul_assoc, mul_assoc, hs' j]
  · change a ^ ((i : ZMod 4) - j + (if q then 2 else 0)).val =
      (a ^ i.val * b) * (a ^ j.val * b)
    calc
      _ = (a ^ i.val * a ^ (-j).val) *
          (if q then a ^ 2 else 1) := by
        rw [power_val_add a ha _ _, sub_eq_add_neg, power_val_add a ha i (-j)]
        cases q <;> simp
      _ = a ^ i.val * ((a ^ (-j).val * b) * b) := by
        rw [← hb, pow_two]
        simp only [mul_assoc]
      _ = _ := by rw [← hs' j]; simp only [mul_assoc]

lemma word_bijective {G : Type*} [Group G] {a b : G} {q : Bool}
    (h : NormalForm a b q) : Function.Bijective (word a b) := by
  constructor
  · intro p r hpr
    obtain ⟨t, ht, hu⟩ := h.2.2.2 (word a b p)
    exact (hu p rfl).trans (hu r hpr).symm
  · intro g
    obtain ⟨p, hp, _⟩ := h.2.2.2 g
    exact ⟨p, hp.symm⟩

/-- Two complete normal-form realizations of the same relations are isomorphic.
The argument proves multiplicativity, rather than assuming a presentation certificate. -/
noncomputable def equivalenceOfNormalForms {G H : Type*} [Group G] [Group H]
    (a b : G) (a' b' : H) (q : Bool)
    (h : NormalForm a b q) (h' : NormalForm a' b' q) : G ≃* H :=
  let e := Equiv.ofBijective (word a b) (word_bijective h)
  let e' := Equiv.ofBijective (word a' b') (word_bijective h')
  { e.symm.trans e' with
    map_mul' := by
      intro x y
      obtain ⟨p, rfl⟩ := (word_bijective h).surjective x
      obtain ⟨r, rfl⟩ := (word_bijective h).surjective y
      change e' (e.symm (word a b p * word a b r)) =
        e' (e.symm (word a b p)) * e' (e.symm (word a b r))
      rw [← word_mul a b q h.1 h.2.1 h.2.2.1]
      change e' (e.symm (e (coordinateMul q p r))) =
        e' (e.symm (e p)) * e' (e.symm (e r))
      simp only [Equiv.symm_apply_apply]
      exact word_mul a' b' q h'.1 h'.2.1 h'.2.2.1 p r }

lemma equivalenceOfNormalForms_word {G H : Type*} [Group G] [Group H]
    (a b : G) (a' b' : H) (q : Bool)
    (h : NormalForm a b q) (h' : NormalForm a' b' q) (p : Fin 4 × Bool) :
    equivalenceOfNormalForms a b a' b' q h h' (word a b p) = word a' b' p :=
  congrArg (word a' b') ((Equiv.ofBijective (word a b) (word_bijective h)).symm_apply_apply p)

theorem normal_form_recognition : NormalFormRecognition := by
  intro G _ a b q h
  cases q
  · refine ⟨equivalenceOfNormalForms _ _ a b false model_normal_forms.1 h, ?_, ?_⟩
    · simpa [word] using
        equivalenceOfNormalForms_word _ _ a b false model_normal_forms.1 h (1, false)
    · simpa [word] using
        equivalenceOfNormalForms_word _ _ a b false model_normal_forms.1 h (0, true)
  · refine ⟨equivalenceOfNormalForms _ _ a b true model_normal_forms.2 h, ?_, ?_⟩
    · simpa [word] using
        equivalenceOfNormalForms_word _ _ a b true model_normal_forms.2 h (1, false)
    · simpa [word] using
        equivalenceOfNormalForms_word _ _ a b true model_normal_forms.2 h (0, true)

lemma possible_orders {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 8)
    (x : G) : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 4 ∨ orderOf x = 8 := by
  have hd : orderOf x ∣ 8 := hcard ▸ orderOf_dvd_natCard x
  have hle := Nat.le_of_dvd (by decide : 0 < 8) hd
  interval_cases ho : orderOf x <;> norm_num at *

lemma cyclic_subgroup_index {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 8) (a : G) (ha : orderOf a = 4) :
    (Subgroup.zpowers a).index = 2 := by
  have h := (Subgroup.zpowers a).card_mul_index
  rw [Nat.card_zpowers, ha, hcard] at h
  omega

lemma exists_outside_cyclic_subgroup {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 8) (a : G) (ha : orderOf a = 4) :
    ∃ b : G, b ∉ Subgroup.zpowers a := by
  by_contra h
  push Not at h
  have ht : Subgroup.zpowers a = ⊤ := (Subgroup.eq_top_iff' _).mpr h
  have hc := Nat.card_zpowers a
  rw [ht, Subgroup.card_top, hcard, ha] at hc
  omega

lemma finite_power_representation {G : Type*} [Group G] [Finite G]
    (a : G) (ha : orderOf a = 4) {g : G} (hg : g ∈ Subgroup.zpowers a) :
    ∃ i : Fin 4, a ^ i.val = g := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hg
  obtain ⟨n, hn, he⟩ := hg
  exact ⟨⟨n, by simpa [ha] using hn⟩, he⟩

/-- An index-two cyclic subgroup gives the eight distinct source words. -/
lemma order_four_coordinates {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 8) (a b : G) (ha : orderOf a = 4)
    (hb : b ∉ Subgroup.zpowers a) :
    ∀ g : G, ∃! p : Fin 4 × Bool, g = word a b p := by
  classical
  have hi := cyclic_subgroup_index hcard a ha
  have hs : Function.Surjective (word a b) := by
    intro g
    by_cases hg : g ∈ Subgroup.zpowers a
    · obtain ⟨i, he⟩ := finite_power_representation a ha hg
      exact ⟨(i, false), he⟩
    · have hm : g * b⁻¹ ∈ Subgroup.zpowers a := by
        apply (Subgroup.mul_mem_iff_of_index_two hi).mpr
        simp [hg, hb]
      obtain ⟨i, he⟩ := finite_power_representation a ha hm
      refine ⟨(i, true), ?_⟩
      change a ^ i.val * b = g
      rw [he, inv_mul_cancel_right]
  have hc : Nat.card (Fin 4 × Bool) = Nat.card G := by
    simp [Nat.card_prod, Nat.card_eq_fintype_card, hcard]
  have hinj := ((Nat.bijective_iff_surjective_and_card _).mpr ⟨hs, hc⟩).injective
  intro g
  obtain ⟨p, hp⟩ := hs g
  exact ⟨p, hp.symm, fun r hr => hinj (hr.symm.trans hp.symm)⟩

lemma commutative_of_coordinates {G : Type*} [Group G] (a b : G)
    (hforms : ∀ g : G, ∃! p : Fin 4 × Bool, g = word a b p)
    (hab : Commute a b) : ∀ x y : G, x * y = y * x := by
  have ha (g : G) : Commute a g := by
    obtain ⟨⟨i, e⟩, he, _⟩ := hforms g
    rw [he]
    cases e
    · exact (Commute.refl a).pow_right i.val
    · exact ((Commute.refl a).pow_right i.val).mul_right hab
  have hb (g : G) : Commute b g := by
    obtain ⟨⟨i, e⟩, he, _⟩ := hforms g
    rw [he]
    cases e
    · exact hab.symm.pow_right i.val
    · exact (hab.symm.pow_right i.val).mul_right (Commute.refl b)
  intro x y
  obtain ⟨⟨i, e⟩, he, _⟩ := hforms x
  rw [he]
  cases e
  · exact ((ha y).pow_left i.val).eq
  · exact (((ha y).pow_left i.val).mul_left (hb y)).eq

theorem nonabelian_reduction : NonabelianReduction := by
  intro G _ _ hcard hnab
  classical
  have hno8 (x : G) : orderOf x ≠ 8 := by
    intro hx
    letI : IsCyclic G := isCyclic_of_orderOf_eq_card x (hx.trans hcard.symm)
    letI : CommGroup G := IsCyclic.commGroup
    obtain ⟨g, h, hgh⟩ := hnab
    exact hgh (mul_comm g h)
  have hex : ∃ a : G, orderOf a = 4 := by
    by_contra h
    push Not at h
    have hdiv (x : G) : orderOf x ∣ 2 := by
      rcases possible_orders hcard x with hx | hx | hx | hx
      · simp [hx]
      · simp [hx]
      · exact False.elim (h x hx)
      · exact False.elim (hno8 x hx)
    obtain ⟨g, k, hgk⟩ := hnab
    exact hgk (Commute.of_orderOf_dvd_two hdiv g k).eq
  obtain ⟨a, ha⟩ := hex
  obtain ⟨b, hb⟩ := exists_outside_cyclic_subgroup hcard a ha
  have hi := cyclic_subgroup_index hcard a ha
  have hforms := order_four_coordinates hcard a b ha hb
  have hn : (Subgroup.zpowers a).Normal :=
    D07.Ch04.IndexTwoNormal.normal_of_index_two G _ hi
  have hconj : b * a * b⁻¹ ∈ Subgroup.zpowers a :=
    hn.conj_mem a (Subgroup.mem_zpowers a) b
  obtain ⟨k, hk⟩ := finite_power_representation a ha hconj
  have hko : orderOf (a ^ k.val) = 4 := by
    rw [hk]
    exact ((MulAut.conj b).orderOf_eq a).trans ha
  have hki : k = 1 ∨ k = 3 := by
    rw [orderOf_pow a, ha] at hko
    fin_cases k <;> norm_num at *
  have hc : b * a * b⁻¹ = a⁻¹ := by
    rcases hki with rfl | rfl
    · have hab : Commute a b := by
        exact ((mul_inv_eq_iff_eq_mul).mp (by simpa using hk.symm)).symm
      obtain ⟨x, y, hxy⟩ := hnab
      exact False.elim (hxy (commutative_of_coordinates a b hforms hab x y))
    · rw [← hk]
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ]
      simpa [ha] using pow_orderOf_eq_one a
  obtain ⟨j, hj⟩ := finite_power_representation a ha (Subgroup.sq_mem_of_index_two hi b)
  have ho : orderOf (b ^ 2) ∣ 2 := by
    rw [orderOf_pow b]
    rcases possible_orders hcard b with h | h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
    · exact False.elim (hno8 b h)
  rw [← hj, orderOf_pow a, ha] at ho
  have hji : j = 0 ∨ j = 2 := by fin_cases j <;> norm_num at *
  rcases hji with rfl | rfl
  · exact ⟨a, b, false, ha, hc, by simpa using hj.symm, hforms⟩
  · exact ⟨a, b, true, ha, hc, by simpa using hj.symm, hforms⟩

/-- A generator killed by `n` gives a homomorphism from the cyclic model. -/
def cyclicMap {G : Type*} [Group G] (n : ℕ) [NeZero n] (a : G) (ha : a ^ n = 1) :
    C n →* G where
  toFun i := a ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change a ^ (i.toAdd + j.toAdd).val = a ^ i.toAdd.val * a ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ ha, pow_add]

/-- Exponent-two groups of order eight are three-dimensional over the two-element field. -/
lemma elementary_abelian_case {G : Type*} [CommGroup G] [Finite G]
    (hcard : Nat.card G = 8) (h2 : ∀ x : G, x ^ 2 = 1) :
    Nonempty (G ≃* Model 2) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule (n := 2)
    (fun x => by exact h2 x.toMul)
  have hc : 2 ^ Module.finrank (ZMod 2) (Additive G) = 2 ^ 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive G)
    change Nat.card G = _ at h
    simpa [hcard] using h.symm
  have hd : Module.finrank (ZMod 2) (Additive G) = 3 :=
    (Nat.pow_right_injective (by decide : 2 ≤ 2)) hc
  let e := (Module.finBasisOfFinrankEq (ZMod 2) (Additive G) hd).equivFun
  let t : (Fin 3 → ZMod 2) ≃+ (ZMod 2 × (ZMod 2 × ZMod 2)) :=
    { toFun := fun x => (x 0, x 1, x 2)
      invFun := fun x => ![x.1, x.2.1, x.2.2]
      left_inv := by intro x; funext i; fin_cases i <;> rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl }
  let t' : Multiplicative (ZMod 2 × (ZMod 2 × ZMod 2)) ≃* Model 2 :=
    { toFun := fun x => (Multiplicative.ofAdd x.toAdd.1,
        Multiplicative.ofAdd x.toAdd.2.1, Multiplicative.ofAdd x.toAdd.2.2)
      invFun := fun x => Multiplicative.ofAdd (x.1.toAdd, x.2.1.toAdd, x.2.2.toAdd)
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_mul' := by intro x y; rfl }
  exact ⟨(e.toAddEquiv.trans t).toMultiplicative.trans t'⟩

lemma abelian_order_four_case {G : Type*} [CommGroup G] [Finite G]
    (hcard : Nat.card G = 8) (hno8 : ∀ x : G, orderOf x ≠ 8)
    (a : G) (ha : orderOf a = 4) : Nonempty (G ≃* Model 1) := by
  classical
  obtain ⟨b, hb⟩ := exists_outside_cyclic_subgroup hcard a ha
  have hi := cyclic_subgroup_index hcard a ha
  obtain ⟨j, hj⟩ := finite_power_representation a ha (Subgroup.sq_mem_of_index_two hi b)
  have ho : orderOf (b ^ 2) ∣ 2 := by
    rw [orderOf_pow b]
    rcases possible_orders hcard b with h | h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
    · exact False.elim (hno8 b h)
  rw [← hj, orderOf_pow a, ha] at ho
  have hji : j = 0 ∨ j = 2 := by fin_cases j <;> norm_num at *
  have hex : ∃ c : G, c ∉ Subgroup.zpowers a ∧ c ^ 2 = 1 := by
    rcases hji with rfl | rfl
    · exact ⟨b, hb, by simpa using hj.symm⟩
    · refine ⟨b * a⁻¹, ?_, ?_⟩
      · intro h
        apply hb
        simpa [mul_assoc] using
          (Subgroup.zpowers a).mul_mem h (Subgroup.mem_zpowers a)
      · rw [mul_pow, ← hj]
        simp [inv_pow]
  obtain ⟨c, hc, hc2⟩ := hex
  have hforms := order_four_coordinates hcard a c ha hc
  have ha4 : a ^ 4 = 1 := by simpa [ha] using pow_orderOf_eq_one a
  let fa := cyclicMap 4 a ha4
  let fc := cyclicMap 2 c hc2
  let f : C 4 × C 2 →* G :=
    (fa.comp (MonoidHom.fst _ _)) * (fc.comp (MonoidHom.snd _ _))
  have hs : Function.Surjective f := by
    intro g
    obtain ⟨⟨i, ep⟩, he, _⟩ := hforms g
    cases ep
    · refine ⟨(Multiplicative.ofAdd i, 1), ?_⟩
      change a ^ i.val * c ^ 0 = g
      simpa [word] using he.symm
    · refine ⟨(Multiplicative.ofAdd i, Multiplicative.ofAdd 1), ?_⟩
      change a ^ i.val * c ^ 1 = g
      simpa [word] using he.symm
  have hc : Nat.card (C 4 × C 2) = Nat.card G := by
    exact (model_cardinalities 1).trans hcard.symm
  exact ⟨(MulEquiv.ofBijective f
    ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hs, hc⟩)).symm⟩

/-- Exhaustion of the list; uniqueness is supplied separately by the invariants. -/
lemma classification_exists (G : Type*) [Group G] [Finite G] (hcard : Nat.card G = 8) :
    ∃ i : Fin 5, Nonempty (G ≃* Model i) := by
  classical
  by_cases h8 : ∃ a : G, orderOf a = 8
  · obtain ⟨a, ha⟩ := h8
    have hgen : Subgroup.zpowers a = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, ha, hcard]
    obtain ⟨_, _, e, _⟩ :=
      D07.Ch02.CyclicModelsIsomorphism.finite_model G a 8 hgen (by decide) ha
    exact ⟨0, ⟨e.symm⟩⟩
  have hno8 : ∀ a : G, orderOf a ≠ 8 := by simpa using h8
  by_cases hnab : ∃ x y : G, x * y ≠ y * x
  · obtain ⟨a, b, q, h⟩ := nonabelian_reduction G hcard hnab
    have hr := normal_form_recognition G a b q h
    cases q
    · obtain ⟨e, _, _⟩ := hr
      exact ⟨3, ⟨e.symm⟩⟩
    · obtain ⟨e, _, _⟩ := hr
      exact ⟨4, ⟨e.symm⟩⟩
  have hcomm : ∀ x y : G, x * y = y * x := by simpa using hnab
  letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  by_cases h4 : ∃ a : G, orderOf a = 4
  · obtain ⟨a, ha⟩ := h4
    exact ⟨1, abelian_order_four_case hcard hno8 a ha⟩
  · refine ⟨2, elementary_abelian_case hcard ?_⟩
    intro x
    rcases possible_orders hcard x with h | h | h | h
    · rw [orderOf_eq_one_iff.mp h]; simp
    · simpa [h] using pow_orderOf_eq_one x
    · exact False.elim (h4 ⟨x, h⟩)
    · exact False.elim (hno8 x h)

theorem classification : Classification := by
  intro G _ _ hcard
  obtain ⟨i, hi⟩ := classification_exists G hcard
  refine ⟨i, hi, ?_⟩
  intro j hj
  obtain ⟨ei⟩ := hi
  obtain ⟨ej⟩ := hj
  exact (pairwise_nonisomorphic j i).mp ⟨ej.symm.trans ei⟩

end D07.Ch06.SmallOrderExamplesOrderEight
