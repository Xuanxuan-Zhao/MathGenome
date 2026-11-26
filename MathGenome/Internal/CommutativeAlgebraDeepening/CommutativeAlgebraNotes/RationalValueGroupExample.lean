import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RationalValueGroupExample
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.NoetherianValuationRings
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace CommutativeAlgebraNotes.RationalValueGroupExample

open Polynomial Additive
open OrderedValuationGroups (ValueGroup value AddValuationInequality)
open ValuationPrimesAndConvexSubgroups (ConvexAddSubgroup)
open Specs.CommutativeAlgebraNotes.RationalValueGroupExample

universe u

variable {k : Type u} [Field k]

private theorem exponent_mul_factorial {i j : ℕ} (h : i ≤ j) :
    embeddingExponent i j * (i + 1).factorial = (j + 1).factorial :=
  Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.succ_le_succ h))

private theorem exponent_pos {i j : ℕ} (h : i ≤ j) : 0 < embeddingExponent i j := by
  apply Nat.pos_of_ne_zero
  intro hz
  have he := exponent_mul_factorial h
  rw [hz, zero_mul] at he
  exact Nat.factorial_ne_zero _ he.symm

private theorem exponent_comp {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    embeddingExponent j l * embeddingExponent i j = embeddingExponent i l := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (i + 1))
  rw [Nat.mul_assoc, exponent_mul_factorial hij, exponent_mul_factorial hjl,
    exponent_mul_factorial (hij.trans hjl)]

private theorem exponent_succ (i : ℕ) : embeddingExponent i (i + 1) = i + 2 := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (i + 1))
  rw [exponent_mul_factorial (Nat.le_succ i), Nat.factorial_succ]

private theorem expand_preserves_nonZeroDivisors {m : ℕ} (hm : 0 < m) :
    nonZeroDivisors (Polynomial k) ≤ (nonZeroDivisors (Polynomial k)).comap (expand k m) := by
  intro p hp
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    ((expand_ne_zero hm).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hp))

/-- Substitution by a positive power on the rational function field. -/
private def substitute (k : Type u) [Field k] (m : ℕ) (hm : 0 < m) :
    RatFunc k →+* RatFunc k :=
  RatFunc.mapRingHom (expand k m) (expand_preserves_nonZeroDivisors hm)

private theorem substitute_fraction {m : ℕ} (hm : 0 < m) (p q : Polynomial k) :
    substitute k m hm (algebraMap (Polynomial k) (RatFunc k) p /
      algebraMap (Polynomial k) (RatFunc k) q) =
    algebraMap (Polynomial k) (RatFunc k) (expand k m p) /
      algebraMap (Polynomial k) (RatFunc k) (expand k m q) := by
  exact RatFunc.map_apply_div _ (expand_preserves_nonZeroDivisors hm) p q

private theorem substitute_polynomial {m : ℕ} (hm : 0 < m) (p : Polynomial k) :
    substitute k m hm (algebraMap (Polynomial k) (RatFunc k) p) =
      algebraMap (Polynomial k) (RatFunc k) (expand k m p) := by
  simpa only [map_one, div_one] using substitute_fraction hm p (1 : Polynomial k)

/-- The indices represent stages one higher than their natural-number labels. -/
def transition (k : Type u) [Field k] (i j : ℕ) (h : i ≤ j) : RatFunc k →+* RatFunc k :=
  substitute k (embeddingExponent i j) (exponent_pos h)

instance transitionDirectedSystem (k : Type u) [Field k] :
    DirectedSystem (fun _ : ℕ ↦ RatFunc k) (transition k · · ·) where
  map_self := by
    intro i x
    induction x using RatFunc.induction_on with
    | _ p q hq =>
      unfold transition
      rw [substitute_fraction]
      simp [embeddingExponent, Nat.div_self (Nat.factorial_pos (i + 1))]
  map_map := by
    intro l j i hij hjl x
    induction x using RatFunc.induction_on with
    | _ p q hq =>
      simp only [transition, substitute_fraction, expand_expand, exponent_comp hij hjl]

/-- The union of the rational function fields with these substitution embeddings. -/
abbrev Limit (k : Type u) [Field k] := DirectLimit (fun _ : ℕ ↦ RatFunc k) (transition k)

def includeStage (k : Type u) [Field k] (i : ℕ) : RatFunc k →+* Limit k :=
  DirectLimit.Ring.of (fun _ : ℕ ↦ RatFunc k) (transition k) i

private theorem trailing_expand {m : ℕ} (hm : 0 < m) (p : Polynomial k) :
    (expand k m p).natTrailingDegree = p.natTrailingDegree * m := by
  by_cases hp : p = 0
  · simp [hp]
  apply le_antisymm
  · apply natTrailingDegree_le_of_ne_zero
    rw [coeff_expand_mul hm]
    exact coeff_natTrailingDegree_ne_zero.mpr hp
  · apply le_natTrailingDegree ((expand_ne_zero hm).mpr hp)
    intro n hn
    rw [coeff_expand hm]
    split_ifs with hd
    · rw [coeff_eq_zero_of_lt_natTrailingDegree]
      apply (Nat.mul_lt_mul_right hm).mp
      rwa [Nat.div_mul_cancel hd]
    · rfl

private theorem min_trailing_le_add {p q : Polynomial k} (h : p + q ≠ 0) :
    min p.natTrailingDegree q.natTrailingDegree ≤ (p + q).natTrailingDegree := by
  apply le_natTrailingDegree h
  intro m hm
  rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree (hm.trans_le (min_le_left _ _)),
    coeff_eq_zero_of_lt_natTrailingDegree (hm.trans_le (min_le_right _ _)), add_zero]

/-- The unscaled order at the generator, used on nonzero fractions. -/
private def orderAtGenerator (x : RatFunc k) : ℚ :=
  (x.num.natTrailingDegree : ℚ) - (x.denom.natTrailingDegree : ℚ)

private theorem order_fraction {p q : Polynomial k} (hp : p ≠ 0) (hq : q ≠ 0) :
    orderAtGenerator (algebraMap (Polynomial k) (RatFunc k) p /
      algebraMap (Polynomial k) (RatFunc k) q) =
      (p.natTrailingDegree : ℚ) - (q.natTrailingDegree : ℚ) := by
  let x := algebraMap (Polynomial k) (RatFunc k) p /
    algebraMap (Polynomial k) (RatFunc k) q
  have hx : x ≠ 0 := div_ne_zero (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq)
  have he := congrArg natTrailingDegree ((RatFunc.num_mul_eq_mul_denom_iff (x := x) hq).mpr rfl)
  rw [natTrailingDegree_mul (RatFunc.num_ne_zero hx) hq,
    natTrailingDegree_mul hp (RatFunc.denom_ne_zero x)] at he
  have he' : (x.num.natTrailingDegree : ℚ) + q.natTrailingDegree =
      (p.natTrailingDegree : ℚ) + x.denom.natTrailingDegree := by exact_mod_cast he
  change orderAtGenerator x = _
  unfold orderAtGenerator
  linarith

private theorem order_mul {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0) :
    orderAtGenerator (x * y) = orderAtGenerator x + orderAtGenerator y := by
  have he := congrArg natTrailingDegree (RatFunc.num_denom_mul x y)
  rw [natTrailingDegree_mul (RatFunc.num_ne_zero (mul_ne_zero hx hy))
      (mul_ne_zero x.denom_ne_zero y.denom_ne_zero),
    natTrailingDegree_mul (mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy))
      (x * y).denom_ne_zero,
    natTrailingDegree_mul x.denom_ne_zero y.denom_ne_zero,
    natTrailingDegree_mul (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy)] at he
  have he' := congrArg (fun a : ℕ ↦ (a : ℚ)) he
  push_cast at he'
  unfold orderAtGenerator
  linarith

private theorem min_order_le_add {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) :
    min (orderAtGenerator x) (orderAtGenerator y) ≤ orderAtGenerator (x + y) := by
  let p := x.num * y.denom + x.denom * y.num
  have hp : p ≠ 0 := RatFunc.num_mul_denom_add_denom_mul_num_ne_zero hxy
  have he := congrArg natTrailingDegree (RatFunc.num_denom_add x y)
  change _ = (p * (x + y).denom).natTrailingDegree at he
  rw [natTrailingDegree_mul (RatFunc.num_ne_zero hxy)
      (mul_ne_zero x.denom_ne_zero y.denom_ne_zero),
    natTrailingDegree_mul hp (x + y).denom_ne_zero,
    natTrailingDegree_mul x.denom_ne_zero y.denom_ne_zero] at he
  have he' := congrArg (fun a : ℕ ↦ (a : ℚ)) he
  push_cast at he'
  have hm := min_trailing_le_add hp
  rw [natTrailingDegree_mul (RatFunc.num_ne_zero hx) y.denom_ne_zero,
    natTrailingDegree_mul x.denom_ne_zero (RatFunc.num_ne_zero hy), min_le_iff] at hm
  rw [min_le_iff]
  unfold orderAtGenerator
  rcases hm with hm | hm
  · left
    have hm' := (Nat.cast_le (α := ℚ)).mpr hm
    push_cast at hm'
    linarith
  · right
    have hm' := (Nat.cast_le (α := ℚ)).mpr hm
    push_cast at hm'
    linarith

private theorem order_substitute {m : ℕ} (hm : 0 < m) (x : RatFunc k) :
    orderAtGenerator (substitute k m hm x) = (m : ℚ) * orderAtGenerator x := by
  by_cases hx : x = 0
  · simp [hx, orderAtGenerator]
  have he := x.num_div_denom
  nth_rw 1 [← he]
  rw [substitute_fraction, order_fraction ((expand_ne_zero hm).mpr (RatFunc.num_ne_zero hx))
    ((expand_ne_zero hm).mpr x.denom_ne_zero), trailing_expand hm, trailing_expand hm]
  unfold orderAtGenerator
  push_cast
  ring

private def stageOrder (i : ℕ) (x : RatFunc k) : ℚ :=
  orderAtGenerator x / ((i + 1).factorial : ℚ)

private theorem stageOrder_compatible {i j : ℕ} (h : i ≤ j) (x : RatFunc k) :
    stageOrder i x = stageOrder j (transition k i j h x) := by
  unfold stageOrder transition
  rw [order_substitute]
  have he : (embeddingExponent i j : ℚ) * ((i + 1).factorial : ℚ) =
      ((j + 1).factorial : ℚ) := by exact_mod_cast exponent_mul_factorial h
  rw [← he]
  have hm : (embeddingExponent i j : ℚ) ≠ 0 := by exact_mod_cast (exponent_pos h).ne'
  have hf : ((i + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i + 1)
  field_simp

private def limitOrder (k : Type u) [Field k] : Limit k → ℚ :=
  DirectLimit.lift (transition k) stageOrder (fun _ _ h x ↦ stageOrder_compatible h x)

private theorem limitOrder_stage (i : ℕ) (x : RatFunc k) :
    limitOrder k (includeStage k i x) = stageOrder i x :=
  rfl

private theorem stage_representatives (x y : Limit k) :
    ∃ (i : ℕ) (a b : RatFunc k), x = includeStage k i a ∧ y = includeStage k i b :=
  DirectLimit.exists_eq_mk₂ (transition k) x y

private theorem limitOrder_one : limitOrder k (1 : Limit k) = 0 := by
  rw [← (includeStage k 0).map_one, limitOrder_stage, stageOrder]
  have h := order_mul (one_ne_zero : (1 : RatFunc k) ≠ 0) one_ne_zero
  rw [one_mul, left_eq_add] at h
  rw [h, zero_div]

private theorem limitOrder_mul {x y : Limit k} (hx : x ≠ 0) (hy : y ≠ 0) :
    limitOrder k (x * y) = limitOrder k x + limitOrder k y := by
  obtain ⟨i, a, b, rfl, rfl⟩ := stage_representatives x y
  have ha : a ≠ 0 := fun h ↦ hx (by rw [h, map_zero])
  have hb : b ≠ 0 := fun h ↦ hy (by rw [h, map_zero])
  rw [← map_mul, limitOrder_stage, limitOrder_stage, limitOrder_stage]
  simp only [stageOrder, order_mul ha hb, add_div]

/-- The compatible normalized valuations on the stages give an additive valuation on the union. -/
def limitValue (k : Type u) [Field k] : Additive (Limit k)ˣ →+ ℚ where
  toFun a := limitOrder k (a.toMul : Limit k)
  map_zero' := limitOrder_one
  map_add' a b := limitOrder_mul a.toMul.ne_zero b.toMul.ne_zero

theorem limitValue_inequality (k : Type u) [Field k] : AddValuationInequality (limitValue k) := by
  intro x y hxy
  change min (limitOrder k (x : Limit k)) (limitOrder k (y : Limit k)) ≤
    limitOrder k ((x : Limit k) + (y : Limit k))
  have hx := x.ne_zero
  have hy := y.ne_zero
  generalize hx' : (x : Limit k) = a at hx hxy ⊢
  generalize hy' : (y : Limit k) = b at hy hxy ⊢
  obtain ⟨i, a', b', rfl, rfl⟩ := stage_representatives a b
  have ha : a' ≠ 0 := fun h ↦ hx (by rw [h, map_zero])
  have hb : b' ≠ 0 := fun h ↦ hy (by rw [h, map_zero])
  have hab : a' + b' ≠ 0 := fun h ↦ hxy (by rw [← map_add, h, map_zero])
  rw [← map_add, limitOrder_stage, limitOrder_stage, limitOrder_stage]
  have hf : (0 : ℚ) ≤ ((i + 1).factorial : ℚ) := Nat.cast_nonneg _
  rcases min_le_iff.mp (min_order_le_add ha hb hab) with h | h
  · exact min_le_iff.mpr (Or.inl (div_le_div_of_nonneg_right h hf))
  · exact min_le_iff.mpr (Or.inr (div_le_div_of_nonneg_right h hf))

theorem limitValue_fraction (i : ℕ) (p q : Polynomial k) (hp : p ≠ 0) (hq : q ≠ 0)
    (h : includeStage k i (algebraMap (Polynomial k) (RatFunc k) p /
      algebraMap (Polynomial k) (RatFunc k) q) ≠ 0) :
    limitValue k (ofMul (Units.mk0 _ h)) = normalizedOrder i p q := by
  change limitOrder k (includeStage k i (algebraMap (Polynomial k) (RatFunc k) p /
    algebraMap (Polynomial k) (RatFunc k) q)) = normalizedOrder i p q
  rw [limitOrder_stage, stageOrder, order_fraction hp hq]
  rfl

private theorem limitValue_X (i : ℕ) :
    limitValue k (ofMul (Units.mk0 (includeStage k i RatFunc.X)
      (by simpa using (includeStage k i).injective.ne RatFunc.X_ne_zero))) =
      1 / ((i + 1).factorial : ℚ) := by
  change limitOrder k (includeStage k i RatFunc.X) = _
  have h : orderAtGenerator (RatFunc.X : RatFunc k) = 1 := by
    simpa using (order_fraction (Polynomial.X_ne_zero : (Polynomial.X : Polynomial k) ≠ 0)
      (one_ne_zero : (1 : Polynomial k) ≠ 0))
  rw [limitOrder_stage, stageOrder, h]

theorem limitValue_surjective (k : Type u) [Field k] : Function.Surjective (limitValue k) := by
  intro q
  let i := q.den - 1
  have hi : i + 1 = q.den := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr q.den_ne_zero)
  have hd : q.den ∣ (i + 1).factorial := Nat.dvd_factorial q.den_pos hi.ge
  obtain ⟨m, hm⟩ := hd
  let a : Additive (Limit k)ˣ := ofMul (Units.mk0 (includeStage k i RatFunc.X) (by
    simpa using (includeStage k i).injective.ne RatFunc.X_ne_zero))
  refine ⟨(q.num * (m : ℤ)) • a, ?_⟩
  rw [map_zsmul, show limitValue k a = _ from limitValue_X i, zsmul_eq_mul, Int.cast_mul,
    Int.cast_natCast]
  have hm' : ((i + 1).factorial : ℚ) = (q.den : ℚ) * (m : ℚ) := by exact_mod_cast hm
  have hd' : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hm0 : (m : ℚ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm'
    exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) hm'
  conv_rhs => rw [← Rat.num_div_den q]
  rw [hm']
  field_simp

private theorem convex_subgroup_eq_bot_or_top {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (e : Γ ≃+o ℚ) (H : ConvexAddSubgroup Γ) :
    H.1 = ⊥ ∨ H.1 = ⊤ := by
  by_cases hb : H.1 = ⊥
  · exact Or.inl hb
  right
  obtain ⟨g, hg, hgn⟩ : ∃ g ∈ H.1, g ≠ 0 := by
    by_contra! he
    apply hb
    exact le_antisymm (fun a ha ↦ AddSubgroup.mem_bot.mpr (he a ha)) bot_le
  obtain ⟨r, hr, hrp⟩ : ∃ r ∈ H.1, 0 < r := by
    rcases lt_or_gt_of_ne hgn with hneg | hpos
    · exact ⟨-g, H.1.neg_mem hg, neg_pos.mpr hneg⟩
    · exact ⟨g, hg, hpos⟩
  have hrq : 0 < e r := by simpa using e.strictMono hrp
  have hnonneg (s : Γ) (hs : 0 ≤ s) : s ∈ H.1 := by
    obtain ⟨n, hn⟩ := Archimedean.arch (e s) hrq
    have hle : s ≤ n • r := (map_le_map_iff e).mp (by simpa only [map_nsmul] using hn)
    exact H.2 H.1.zero_mem (H.1.nsmul_mem hr n) hs hle
  apply top_unique
  intro s _
  by_cases hs : 0 ≤ s
  · exact hnonneg s hs
  · simpa using H.1.neg_mem (hnonneg (-s) (neg_nonneg.mpr (le_of_not_ge hs)))

theorem convex_subgroups_rat : ConvexSubgroups :=
  convex_subgroup_eq_bot_or_top (OrderAddMonoidIso.refl ℚ)

private theorem rank_eq_one {K : Type u} [Field K] (V : ValuationSubring K)
    (e : ValueGroup V ≃+o ℚ) : ringKrullDim V = 1 := by
  change ValuationPrimesAndConvexSubgroups.valuationRank V = 1
  rw [ValuationPrimesAndConvexSubgroups.rank_eq_krullDim_convexAddSubgroups]
  apply le_antisymm
  · apply Order.krullDim_le_one_iff.mpr
    intro H
    rcases convex_subgroup_eq_bot_or_top e H with hb | ht
    · exact Or.inl (fun _ _ ↦ show H.1 ≤ _ from hb ▸ bot_le)
    · exact Or.inr (fun _ _ ↦ show _ ≤ H.1 from ht ▸ le_top)
  · apply Order.one_le_krullDim_iff.mpr
    let B : ConvexAddSubgroup (ValueGroup V) := ⟨⊥, by
      intro a b c ha hc hab hbc
      rw [AddSubgroup.mem_bot] at ha hc ⊢
      exact le_antisymm (hc ▸ hbc) (ha ▸ hab)⟩
    let T : ConvexAddSubgroup (ValueGroup V) := ⟨⊤, by
      intros
      exact AddSubgroup.mem_top _⟩
    let a := e.symm 1
    have ha : a ≠ 0 := fun h ↦ (one_ne_zero : (1 : ℚ) ≠ 0) (by simpa [a] using congrArg e h)
    refine ⟨B, T, lt_of_le_not_ge (show B.1 ≤ T.1 from bot_le) ?_⟩
    intro h
    exact ha (AddSubgroup.mem_bot.mp ((show T.1 ≤ B.1 from h) (AddSubgroup.mem_top a)))

private theorem not_noetherian {K : Type u} [Field K] (V : ValuationSubring K)
    (e : ValueGroup V ≃+o ℚ) : ¬ IsNoetherianRing V := by
  intro h
  rcases (NoetherianValuationRings.noetherian_iff V).mp h with hfield | hi
  · let := (NoetherianValuationRings.isField_iff_subsingleton_valueGroup V).mp hfield
    exact zero_ne_one (e.surjective.subsingleton.elim (0 : ℚ) 1)
  · obtain ⟨ei⟩ := hi
    let f := ei.symm.trans e
    have h01 : f 0 < f 1 := f.strictMono Int.zero_lt_one
    obtain ⟨q, h0q, hq1⟩ := exists_between h01
    obtain ⟨n, rfl⟩ := f.surjective q
    have hn0 : (0 : ℤ) < n := (map_lt_map_iff f).mp h0q
    have hn1 : n < (1 : ℤ) := (map_lt_map_iff f).mp hq1
    omega

/-- Over any field the factorial tower carries a rank-one non-Noetherian valuation ring. -/
theorem rational_value_group_example : Example := by
  intro k inst
  let F := limitValue k
  let hF := limitValue_inequality k
  let V := OrderedValuationGroups.valuationSubring F hF
  obtain ⟨e, he⟩ := OrderedValuationGroups.ordered_image F hF
  let g : F.range ≃+o ℚ :=
    { AddEquiv.ofBijective F.range.subtype
        ⟨Subtype.val_injective, fun q ↦ by
          obtain ⟨a, rfl⟩ := limitValue_surjective k q
          exact ⟨F.rangeRestrict a, rfl⟩⟩ with
      map_le_map_iff' := Iff.rfl }
  let eQ : ValueGroup V ≃+o ℚ := e.trans g
  refine ⟨Limit k, inferInstance, transition k, includeStage k, F, V, ?_, ?_, ?_, ?_, ?_, hF,
    limitValue_fraction, limitValue_surjective k, OrderedValuationGroups.mem_valuationSubring_iff F hF,
    ⟨eQ, ?_⟩, rank_eq_one V eQ, not_noetherian V eQ⟩
  · exact fun i j h p ↦ substitute_polynomial (exponent_pos h) p
  · intro i
    unfold transition
    rw [← RatFunc.algebraMap_X, substitute_polynomial, expand_X, map_pow, RatFunc.algebraMap_X,
      exponent_succ]
  · exact fun i ↦ (includeStage k i).injective
  · exact fun _ _ h x ↦ DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ RatFunc k) (f := transition k) h x
  · intro x
    obtain ⟨i, y, hy⟩ := DirectLimit.exists_eq_mk (transition k) x
    exact ⟨i, y, hy.symm⟩
  · intro a
    exact congrArg Subtype.val (he a)

end CommutativeAlgebraNotes.RationalValueGroupExample
