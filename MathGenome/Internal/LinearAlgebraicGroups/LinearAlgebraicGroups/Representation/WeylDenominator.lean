import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.WeylDenominator
import Mathlib.Algebra.BigOperators.Ring.Finset

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.DominantOrder
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.WeylDenominator

open Specs.WeylDenominator
open Specs.DominantOrder (IsBaseFor IsDominant twoRhoCoroot)
open AddMonoidAlgebra

noncomputable section

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
variable (P : RootPairing I ℤ X Y)

private theorem weight_mul (w v : P.weylGroup) (x : X) :
    (w * v).val.weightEquiv x = w.val.weightEquiv (v.val.weightEquiv x) := rfl

private theorem weight_inv (w : P.weylGroup) (x : X) :
    w⁻¹.val.weightEquiv x = w.val.weightEquiv.symm x := rfl

private theorem on_monomial (w : P.weylGroup) (x : X) :
    onGroupRing P w (monomial x) = monomial (w.val.weightEquiv x) := by
  simp [onGroupRing]

private theorem on_coeff (w : P.weylGroup) (f : GroupRing X) (x : X) :
    (onGroupRing P w f).coeff (w.val.weightEquiv x) = f.coeff x := by
  simp [onGroupRing]

private theorem on_one (f : GroupRing X) : onGroupRing P 1 f = f := by
  apply AddMonoidAlgebra.ext
  ext x
  exact on_coeff P 1 f x

private theorem on_mul (w v : P.weylGroup) (f : GroupRing X) :
    onGroupRing P (w * v) f = onGroupRing P w (onGroupRing P v f) := by
  apply AddMonoidAlgebra.ext
  ext x
  obtain ⟨y, rfl⟩ := (w * v).val.weightEquiv.surjective x
  rw [on_coeff, weight_mul, on_coeff, on_coeff]

private theorem coeff_zsmul (a : ℤ) (f : GroupRing X) (x : X) :
    (a • f).coeff x = a * f.coeff x := by
  change a • f.coeff x = _
  exact zsmul_eq_mul _ _

private theorem monomial_mul (x y : X) :
    monomial x * monomial y = monomial (x + y) := by
  simp

private theorem weight_injective :
    Function.Injective (fun w : P.weylGroup => w.val.weightEquiv) := by
  intro w v h
  apply Subtype.ext
  exact RootPairing.Equiv.weightHom_injective P h

private theorem reflection_opposite (i : I) :
    RootPairing.weylGroup.ofIdx P (P.reflectionPerm i i) =
      RootPairing.weylGroup.ofIdx P i := by
  let := P.indexNeg
  apply weight_injective P
  ext x
  change P.reflection (-i) x = P.reflection i x
  have hroot : P.root (-i) = -P.root i :=
    (P.root_eq_neg_iff).mpr rfl
  have hcoroot : P.coroot (-i) = -P.coroot i :=
    (P.coroot_eq_neg_iff).mpr rfl
  rw [P.reflection_apply, P.reflection_apply]
  change x - P.toLinearMap x (P.coroot (-i)) • P.root (-i) =
    x - P.toLinearMap x (P.coroot i) • P.root i
  rw [hroot, hcoroot, map_neg, neg_smul, smul_neg, neg_neg]

private theorem reflection_conjugate (i j : I) :
    RootPairing.weylGroup.ofIdx P (P.reflectionPerm j i) =
      RootPairing.weylGroup.ofIdx P j * RootPairing.weylGroup.ofIdx P i *
        RootPairing.weylGroup.ofIdx P j := by
  apply weight_injective P
  ext x
  change P.reflection (P.reflectionPerm j i) x = P.reflection j (P.reflection i (P.reflection j x))
  rw [P.reflection_reflectionPerm]
  rfl

variable [Finite I] [P.IsReduced]

private theorem exists_word (b : P.Base) (w : P.weylGroup) :
    ∃ word : List b.support, wordProduct P b word = w := by
  classical
  suffices h : ∀ i, ∃ word : List b.support,
      wordProduct P b word = RootPairing.weylGroup.ofIdx P i by
    obtain ⟨w, hw⟩ := w
    induction hw using RootPairing.weylGroup.induction P with
    | mem i => exact h i
    | one => exact ⟨[], rfl⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨xs, hxs⟩ := ihx
      obtain ⟨ys, hys⟩ := ihy
      refine ⟨xs ++ ys, ?_⟩
      rw [← Submonoid.mk_mul_mk _ _ _ hx hy]
      simpa only [wordProduct, List.map_append, List.prod_append] using congrArg₂ (· * ·) hxs hys
  intro i
  induction i using b.induction_reflect with
  | h₀ i ih => simpa only [reflection_opposite] using ih
  | h₁ i hi => exact ⟨[⟨i, hi⟩], by simp [wordProduct]⟩
  | h₂ i j ih hj =>
    obtain ⟨word, hw⟩ := ih
    refine ⟨⟨j, hj⟩ :: (word ++ [⟨j, hj⟩]), ?_⟩
    rw [reflection_conjugate, mul_assoc]
    simpa only [wordProduct, List.map_cons, List.map_append, List.map_nil,
      List.prod_cons, List.prod_append, List.prod_nil, mul_one] using
        congrArg (fun w ↦ RootPairing.weylGroup.ofIdx P j *
          (w * RootPairing.weylGroup.ofIdx P j)) hw

private theorem length_word (b : P.Base) (w : P.weylGroup) :
    ∃ word : List b.support, wordProduct P b word = w ∧ word.length = weylLength P b w := by
  obtain ⟨word, hw⟩ := exists_word P b w
  exact Nat.sInf_mem (s := {n | ∃ word : List b.support,
    wordProduct P b word = w ∧ word.length = n}) ⟨word.length, word, hw, rfl⟩

private theorem mem_positiveRoots {S : Set I} {i : I} :
    i ∈ positiveRoots S ↔ i ∈ S := by classical exact Finset.mem_filter.trans (by simp)

variable {S : Set I} {b : P.Base}

variable [DecidableEq I] in
private theorem reflection_mem_erase (hbase : IsBaseFor P S b) {i j : I}
    (hi : i ∈ b.support) (hj : j ∈ (positiveRoots S).erase i) :
    P.reflectionPerm i j ∈ (positiveRoots S).erase i := by
  classical
  obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
  have hjpos := (hbase j).mpr (mem_positiveRoots.mp hj)
  have hpos := hjpos.reflectionPerm hi hne
  refine Finset.mem_erase.mpr ⟨?_, mem_positiveRoots.mpr ((hbase _).mp hpos)⟩
  intro he
  have hop : j = P.reflectionPerm i i := by
    rw [← P.reflectionPerm_self i j, he]
  rw [hop] at hjpos
  exact (RootPairing.Base.IsPos.neg_iff_not b i).mp hjpos (b.isPos_of_mem_support hi)

variable [DecidableEq I] in
private theorem reflection_prod_erase {M : Type*} [CommMonoid M]
    (hbase : IsBaseFor P S b) {i : I} (hi : i ∈ b.support) (f : I → M) :
    ∏ j ∈ (positiveRoots S).erase i, f (P.reflectionPerm i j) =
      ∏ j ∈ (positiveRoots S).erase i, f j := by
  classical
  refine Finset.prod_bij (fun j _ ↦ P.reflectionPerm i j)
    (fun _ hj ↦ reflection_mem_erase P hbase hi hj)
    (fun _ _ _ _ h ↦ (P.reflectionPerm i).injective h) ?_ (fun _ _ ↦ rfl)
  intro j hj
  exact ⟨P.reflectionPerm i j, reflection_mem_erase P hbase hi hj, P.reflectionPerm_self i j⟩

private theorem reflection_rho (hbase : IsBaseFor P S b) {i : I} (hi : i ∈ b.support) :
    P.reflection i (rho P S) = rho P S - 2 • P.root i := by
  classical
  have hiS := mem_positiveRoots.mpr ((hbase _).mp (b.isPos_of_mem_support hi))
  have hsum : ∑ j ∈ (positiveRoots S).erase i, P.root (P.reflectionPerm i j) =
      ∑ j ∈ (positiveRoots S).erase i, P.root j :=
    reflection_prod_erase (M := Multiplicative X) P hbase hi
      (fun j ↦ Multiplicative.ofAdd (P.root j))
  rw [rho, ← Finset.sum_erase_add (positiveRoots S) P.root hiS, map_add, map_sum]
  have hneg : P.root (P.reflectionPerm i i) = -P.root i := P.root_eq_neg_iff.mpr rfl
  simp only [← RootPairing.root_reflectionPerm, hsum, hneg, two_nsmul]
  abel

private theorem rho_simple_pairing (hbase : IsBaseFor P S b) {i : I} (hi : i ∈ b.support) :
    P.toLinearMap (rho P S) (P.coroot i) = 2 := by
  have h := reflection_rho P hbase hi
  change P.coroot' i (rho P S) = 2
  change rho P S - P.coroot' i (rho P S) • P.root i = rho P S - 2 • P.root i at h
  let f := P.coroot' i
  have he : f (rho P S - f (rho P S) • P.root i) = f (rho P S - 2 • P.root i) :=
    congrArg f h
  have hf : f (P.root i) = 2 := P.coroot_root_two i
  simp only [two_nsmul, map_sub, map_add, map_zsmul, hf, zsmul_eq_mul, Int.cast_id] at he
  change f (rho P S) = 2
  omega

omit [P.IsReduced] in
private theorem shifted_product (S : Set I) :
    monomial (rho P S) * denominator P S =
      ∏ i ∈ positiveRoots S, (monomial (P.root i) - monomial (-P.root i)) := by
  classical
  have hm : (∏ i ∈ positiveRoots S, monomial (P.root i)) = monomial (rho P S) := by
    simp [rho]
  rw [denominator, ← hm, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_sub, mul_one, monomial_mul]
  congr 2
  abel

private theorem simple_on_shifted (hbase : IsBaseFor P S b) {i : I} (hi : i ∈ b.support) :
    onGroupRing P (RootPairing.weylGroup.ofIdx P i) (monomial (rho P S) * denominator P S) =
      -(monomial (rho P S) * denominator P S) := by
  classical
  let f := fun j : I => monomial (P.root j) - monomial (-P.root j)
  let s := RootPairing.weylGroup.ofIdx P i
  have hiS := mem_positiveRoots.mpr ((hbase _).mp (b.isPos_of_mem_support hi))
  have hf (j : I) : onGroupRing P s (f j) = f (P.reflectionPerm i j) := by
    have h : s.val.weightEquiv (P.root j) = P.root (P.reflectionPerm i j) :=
      (P.root_reflectionPerm i j).symm
    simp only [f, map_sub, on_monomial, map_neg, h]
  have hfi : f (P.reflectionPerm i i) = -f i := by
    simp [f, P.root_reflectionPerm, neg_sub]
  rw [shifted_product]
  change onGroupRing P s (∏ j ∈ positiveRoots S, f j) = -(∏ j ∈ positiveRoots S, f j)
  rw [← Finset.prod_erase_mul (positiveRoots S) f hiS, map_mul, map_prod]
  simp only [hf, hfi, mul_neg]
  rw [reflection_prod_erase P hbase hi f]

private theorem word_on_shifted (hbase : IsBaseFor P S b) (word : List b.support) :
    onGroupRing P (wordProduct P b word) (monomial (rho P S) * denominator P S) =
      (-1 : ℤ) ^ word.length • (monomial (rho P S) * denominator P S) := by
  induction word with
  | nil =>
    change onGroupRing P 1 _ = _
    rw [on_one]
    simp
  | cons i word ih =>
    change onGroupRing P (RootPairing.weylGroup.ofIdx P i.val * wordProduct P b word) _ = _
    rw [on_mul, ih, map_zsmul, simple_on_shifted P hbase i.property]
    simp only [List.length_cons, pow_succ, mul_neg, mul_one, neg_zsmul, smul_neg]

private theorem on_shifted (hbase : IsBaseFor P S b) (w : P.weylGroup) :
    onGroupRing P w (monomial (rho P S) * denominator P S) =
      weylSign P b w • (monomial (rho P S) * denominator P S) := by
  obtain ⟨word, hw, hlength⟩ := length_word P b w
  simpa only [hw, hlength, weylSign] using word_on_shifted P hbase word

omit [P.IsReduced] in
private theorem shifted_expansion (S : Set I) :
    monomial (rho P S) * denominator P S =
      ∑ T ∈ (positiveRoots S).powerset,
        single (rho P S - 2 • ∑ i ∈ T, P.root i) ((-1 : ℤ) ^ T.card) := by
  classical
  rw [denominator, Finset.prod_sub, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  simp only [Finset.prod_const_one, mul_one, prod_single]
  have hn : (-1 : GroupRing X) ^ T.card = single 0 ((-1 : ℤ) ^ T.card) := by
    change _ = singleZeroRingHom ((-1 : ℤ) ^ T.card)
    simp
  rw [hn, single_mul_single, single_mul_single]
  simp only [zero_add, one_mul, mul_one, Finset.sum_neg_distrib, ← Finset.smul_sum, sub_eq_add_neg]

omit [P.IsReduced] in
private theorem shifted_support {x : X}
    (hx : (monomial (rho P S) * denominator P S).coeff x ≠ 0) :
    ∃ T ⊆ positiveRoots S, x = rho P S - 2 • ∑ i ∈ T, P.root i := by
  classical
  rw [shifted_expansion, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at hx
  by_contra! h
  apply hx
  apply Finset.sum_eq_zero
  intro T hT
  simp [Ne.symm (h T (Finset.mem_powerset.mp hT))]

omit [P.IsReduced] in
private theorem positive_root_pairing (hbase : IsBaseFor P S b)
    (laws : Specs.DominantOrder.Laws P S b) {i : I} (hi : i ∈ positiveRoots S) :
    0 < P.toLinearMap (P.root i) (twoRhoCoroot P S) := by
  let f := P.toLinearMap.flip (twoRhoCoroot P S)
  change 0 < f (P.root i)
  have hi' := (hbase i).mpr (mem_positiveRoots.mp hi)
  refine hi'.induction_on_add (p := fun j ↦ 0 < f (P.root j)) ?_ ?_
  · intro j hj
    change 0 < P.toLinearMap (P.root j) (twoRhoCoroot P S)
    rw [laws.simplePairing j hj]
    decide
  · intro j k l he ih hk
    have hk' : f (P.root k) = 2 := laws.simplePairing k hk
    rw [he, map_add, hk']
    omega

omit [P.IsReduced] in
private theorem shifted_top (hbase : IsBaseFor P S b)
    (laws : Specs.DominantOrder.Laws P S b) :
    (monomial (rho P S) * denominator P S).coeff (rho P S) = 1 := by
  classical
  rw [shifted_expansion, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro T hT hne
    have hpos : 0 < ∑ i ∈ T, P.toLinearMap (P.root i) (twoRhoCoroot P S) :=
      Finset.sum_pos (fun i hi => positive_root_pairing P hbase laws (Finset.mem_powerset.mp hT hi))
        (Finset.nonempty_iff_ne_empty.mpr hne)
    have he : rho P S - 2 • ∑ i ∈ T, P.root i ≠ rho P S := by
      intro h
      let f := P.toLinearMap.flip (twoRhoCoroot P S)
      have ht := congrArg f h
      simp only [map_sub, map_nsmul, map_sum, nsmul_eq_mul, Nat.cast_ofNat] at ht
      change f (rho P S) - 2 * (∑ i ∈ T, P.toLinearMap (P.root i) (twoRhoCoroot P S)) =
        f (rho P S) at ht
      omega
    simp [he]
  · simp

omit [Finite I] [P.IsReduced] in
private theorem sign_sq (b : P.Base) (w : P.weylGroup) :
    weylSign P b w * weylSign P b w = 1 := by
  rw [weylSign, ← mul_pow]
  norm_num

omit [P.IsReduced] in
private theorem shifted_scalar_injective (hbase : IsBaseFor P S b)
    (laws : Specs.DominantOrder.Laws P S b) :
    Function.Injective (fun a : ℤ ↦ a • (monomial (rho P S) * denominator P S)) := by
  intro a c h
  have he := congrArg (fun f : GroupRing X ↦ f.coeff (rho P S)) h
  simpa only [coeff_zsmul, shifted_top P hbase laws, mul_one] using he

private theorem sign_mul (hbase : IsBaseFor P S b) (laws : Specs.DominantOrder.Laws P S b)
    (w v : P.weylGroup) : weylSign P b (w * v) = weylSign P b w * weylSign P b v := by
  apply shifted_scalar_injective P hbase laws
  dsimp only
  rw [← on_shifted P hbase, on_mul, on_shifted P hbase v, map_zsmul, on_shifted P hbase w,
    smul_smul, mul_comm (weylSign P b v)]

private theorem shifted_coeff_action (hbase : IsBaseFor P S b) (w : P.weylGroup) (x : X) :
    (monomial (rho P S) * denominator P S).coeff (w.val.weightEquiv x) =
      weylSign P b w * (monomial (rho P S) * denominator P S).coeff x := by
  have h := on_coeff P w (monomial (rho P S) * denominator P S) x
  rw [on_shifted P hbase, coeff_zsmul] at h
  rw [← h, ← mul_assoc, sign_sq, one_mul]

private theorem denominator_action (hbase : IsBaseFor P S b) (w : P.weylGroup) :
    onGroupRing P w (denominator P S) =
      weylSign P b w •
        (monomial (rho P S - w.val.weightEquiv (rho P S)) * denominator P S) := by
  let y := w.val.weightEquiv (rho P S)
  have h := on_shifted P hbase w
  rw [map_mul, on_monomial] at h
  have he := congrArg (fun f : GroupRing X ↦ monomial (-y) * f) h
  change monomial (-y) * (monomial y * _) =
    monomial (-y) * (weylSign P b w • (monomial (rho P S) * denominator P S)) at he
  rw [← mul_assoc, monomial_mul, neg_add_cancel, show monomial (0 : X) = 1 from rfl,
    one_mul, mul_smul_comm, ← mul_assoc, monomial_mul, add_comm (-y), ← sub_eq_add_neg] at he
  exact he

private theorem only_dominant_exponent (hbase : IsBaseFor P S b)
    (laws : Specs.DominantOrder.Laws P S b)
    (simpleSign : ∀ i ∈ b.support, weylSign P b (RootPairing.weylGroup.ofIdx P i) = -1)
    {x : X} (hx : IsDominant P b x)
    (hc : (monomial (rho P S) * denominator P S).coeff x ≠ 0) : x = rho P S := by
  classical
  obtain ⟨T, hT, hsub⟩ := shifted_support P hc
  have hdom : IsDominant P b (x - rho P S) := by
    intro i hi
    let f := P.coroot' i
    have hregular : f x ≠ 0 := by
      intro hz
      let s := RootPairing.weylGroup.ofIdx P i
      have hfix : s.val.weightEquiv x = x := by
        change P.reflection i x = x
        simp [P.reflection_apply, show P.coroot' i x = 0 from hz]
      have h := shifted_coeff_action P hbase s x
      rw [hfix, show weylSign P b s = -1 from simpleSign i hi] at h
      exact hc (by omega)
    have hnonneg : 0 ≤ f x := hx i hi
    have hρ : f (rho P S) = 2 := rho_simple_pairing P hbase hi
    have hval : f x = 2 - 2 * f (∑ j ∈ T, P.root j) := by
      rw [hsub, map_sub, hρ, map_nsmul, two_nsmul]
      omega
    change 0 ≤ f (x - rho P S)
    rw [map_sub, hρ]
    omega
  by_cases he : T = ∅
  · simpa [he] using hsub
  have hp : 0 < ∑ i ∈ T, P.toLinearMap (P.root i) (twoRhoCoroot P S) :=
    Finset.sum_pos (fun i hi => positive_root_pairing P hbase laws (hT hi))
      (Finset.nonempty_iff_ne_empty.mpr he)
  let f := P.toLinearMap.flip (twoRhoCoroot P S)
  have hn : 0 ≤ f (x - rho P S) := laws.nonnegative _ hdom
  have hd : x - rho P S = -(2 • ∑ i ∈ T, P.root i) := by rw [hsub]; abel
  rw [hd, map_neg, map_nsmul, map_sum] at hn
  change 0 ≤ -(2 • ∑ i ∈ T, P.toLinearMap (P.root i) (twoRhoCoroot P S)) at hn
  rw [two_nsmul] at hn
  omega

/-- A Weyl element fixing the strictly dominant `ρ` fixes every weight.
Adding a large multiple of `ρ` makes a weight and its translate both dominant. -/
private theorem rho_stabilizer (hbase : IsBaseFor P S b)
    (laws : Specs.DominantOrder.Laws P S b)
    (w : P.weylGroup) (hw : w.val.weightEquiv (rho P S) = rho P S) : w = 1 := by
  classical
  apply weight_injective P
  ext x
  change w.val.weightEquiv x = x
  let bound : b.support → ℕ := fun i ↦
    (P.coroot' i.val x).natAbs + (P.coroot' i.val (w.val.weightEquiv x)).natAbs
  let n := Finset.univ.sup bound
  let y := Int.ofNat n • rho P S + x
  have hwy : w.val.weightEquiv y = Int.ofNat n • rho P S + w.val.weightEquiv x := by
    simp only [y, map_add, map_zsmul, hw]
  have hy : IsDominant P b y := by
    intro i hi
    have hbound : bound ⟨i, hi⟩ ≤ n :=
      Finset.le_sup (f := bound) (Finset.mem_univ (⟨i, hi⟩ : b.support))
    change 0 ≤ P.coroot' i y
    have hρ : P.coroot' i (rho P S) = 2 := rho_simple_pairing P hbase hi
    simp only [y, map_add, map_zsmul, hρ, zsmul_eq_mul]
    change 0 ≤ Int.ofNat n * 2 + _
    rw [Int.ofNat_eq_natCast]
    dsimp only [n, bound] at hbound ⊢
    omega
  have hwy' : IsDominant P b (w.val.weightEquiv y) := by
    intro i hi
    have hbound : bound ⟨i, hi⟩ ≤ n :=
      Finset.le_sup (f := bound) (Finset.mem_univ (⟨i, hi⟩ : b.support))
    change 0 ≤ P.coroot' i (w.val.weightEquiv y)
    have hρ : P.coroot' i (rho P S) = 2 := rho_simple_pairing P hbase hi
    simp only [hwy, map_add, map_zsmul, hρ, zsmul_eq_mul]
    change 0 ≤ Int.ofNat n * 2 + _
    rw [Int.ofNat_eq_natCast]
    dsimp only [n, bound] at hbound ⊢
    omega
  have he : w.val.weightEquiv y = y :=
    (laws.orbitRepresentative y).unique ⟨hwy', w, rfl⟩ ⟨hy, 1, rfl⟩
  rw [hwy] at he
  exact add_left_cancel he

private theorem rho_orbit_injective (hbase : IsBaseFor P S b)
    (laws : Specs.DominantOrder.Laws P S b) :
    Function.Injective (fun w : P.weylGroup ↦ w.val.weightEquiv (rho P S)) := by
  intro w v he
  change w.val.weightEquiv (rho P S) = v.val.weightEquiv (rho P S) at he
  have hfix : (v⁻¹ * w).val.weightEquiv (rho P S) = rho P S := by
    rw [weight_mul, weight_inv, he, LinearEquiv.symm_apply_apply]
  exact (inv_mul_eq_one.mp (rho_stabilizer P hbase laws (v⁻¹ * w) hfix)).symm

variable [Finite P.weylGroup]

omit [Finite I] [P.IsReduced] in
private theorem alternant_action (b : P.Base)
    (hmul : ∀ w v, weylSign P b (w * v) = weylSign P b w * weylSign P b v)
    (w : P.weylGroup) (x : X) :
    onGroupRing P w (alternant P b x) = weylSign P b w • alternant P b x := by
  classical
  let := Fintype.ofFinite P.weylGroup
  unfold alternant
  simp only [map_sum, map_zsmul, on_monomial, Finset.smul_sum]
  calc
    _ = ∑ v : P.weylGroup, weylSign P b w •
        (weylSign P b (w * v) • monomial ((w * v).val.weightEquiv x)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hmul, smul_smul, ← mul_assoc, sign_sq, one_mul, weight_mul]
    _ = _ := Equiv.sum_comp (Equiv.mulLeft w)
      (fun v ↦ weylSign P b w • (weylSign P b v • monomial (v.val.weightEquiv x)))

private theorem denominator_identity (hbase : IsBaseFor P S b)
    (laws : Specs.DominantOrder.Laws P S b)
    (simpleSign : ∀ i ∈ b.support, weylSign P b (RootPairing.weylGroup.ofIdx P i) = -1) :
    alternant P b (rho P S) = monomial (rho P S) * denominator P S := by
  classical
  let := Fintype.ofFinite P.weylGroup
  apply AddMonoidAlgebra.ext
  ext x
  rw [alternant, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases he : ∃ w : P.weylGroup, w.val.weightEquiv (rho P S) = x
  · obtain ⟨w, rfl⟩ := he
    rw [shifted_coeff_action P hbase, shifted_top P hbase laws, mul_one, Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      have hn : v.val.weightEquiv (rho P S) ≠ w.val.weightEquiv (rho P S) :=
        fun h ↦ hv (rho_orbit_injective P hbase laws h)
      rw [coeff_zsmul, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
        ite_eq_right hn, mul_zero]
    · simp
  · have ha : (∑ w : P.weylGroup,
          (weylSign P b w • monomial (w.val.weightEquiv (rho P S))).coeff x) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      have hn : w.val.weightEquiv (rho P S) ≠ x := fun h ↦ he ⟨w, h⟩
      rw [coeff_zsmul, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
        ite_eq_right hn, mul_zero]
    rw [ha]
    by_contra! hn
    obtain ⟨y, ⟨hy, w, rfl⟩, _⟩ := laws.orbitRepresentative x
    have hc : (monomial (rho P S) * denominator P S).coeff (w.val.weightEquiv x) ≠ 0 := by
      rw [shifted_coeff_action P hbase]
      exact mul_ne_zero (pow_ne_zero _ (by decide)) (Ne.symm hn)
    have hr := only_dominant_exponent P hbase laws simpleSign hy hc
    exact he ⟨w⁻¹, by rw [weight_inv, ← hr, LinearEquiv.symm_apply_apply]⟩

omit [P.IsReduced] [Finite P.weylGroup] in
private theorem rootless_denominator (h : IsEmpty I) :
    rho P S = 0 ∧ denominator P S = 1 := by
  classical
  have he : positiveRoots S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i _ ↦ h.false i
  simp [rho, denominator, he]

private theorem formula (hbase : IsBaseFor P S b) (laws : Specs.DominantOrder.Laws P S b) :
    Laws P S b := by
  have hcancel := shifted_scalar_injective P hbase laws
  have hone : weylSign P b 1 = 1 := by
    apply hcancel
    dsimp only
    rw [← on_shifted P hbase, on_one, one_smul]
  have hs i (hi : i ∈ b.support) :
      weylSign P b (RootPairing.weylGroup.ofIdx P i) = -1 := by
    apply hcancel
    dsimp only
    rw [← on_shifted P hbase, simple_on_shifted P hbase hi, neg_one_zsmul]
  have hident := denominator_identity P hbase laws hs
  refine ⟨hone, sign_mul P hbase laws, hs, denominator_action P hbase, on_shifted P hbase,
    alternant_action P b (sign_mul P hbase laws), hident, ?_, ?_⟩
  · rw [hident, shifted_top P hbase laws]
  · intro h
    obtain ⟨hr, hd⟩ := rootless_denominator (P := P) (S := S) h
    rw [hident, hr, hd, mul_one]
    exact ⟨AddMonoidAlgebra.one_def.symm, rfl⟩

/-- Conditional version of the Weyl denominator identity on the actual
character lattice of the split reductive pair. -/
theorem weylDenominator_conditional (dominantOrder : Specs.DominantOrder.Statement.{u}) :
    Specs.WeylDenominator.Statement.{u} := by
  classical
  intro k _ G hG T hT hmax
  obtain ⟨hComm, h⟩ := dominantOrder G hG T hT hmax
  let := hComm
  obtain ⟨D, ⟨identification⟩, hD⟩ := h
  let := D.finiteRoots
  let := D.reduced
  let := identification.image.finite
  have hW : Finite D.rootDatum.weylGroup :=
    Finite.of_injective identification.labelEquiv identification.labelEquiv.injective
  let := hW
  refine ⟨hComm, D, ⟨identification⟩, hW, ?_⟩
  intro S hS
  obtain ⟨hb, hL⟩ := hD S hS
  exact ⟨hb, fun b hbase ↦ formula D.rootDatum hbase (hL b hbase)⟩

end

end LinearAlgebraicGroups.Representation.WeylDenominator

universe v8_closure_8b091affd534779c_u0
theorem _root_.«LinearAlgebraicGroups».«Representation».«WeylDenominator».«weylDenominator» : _root_.«LinearAlgebraicGroups».«Specs».«WeylDenominator».«Statement».{v8_closure_8b091affd534779c_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«WeylDenominator».«weylDenominator_conditional».{v8_closure_8b091affd534779c_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«DominantOrder».«dominantOrder».{v8_closure_8b091affd534779c_u0})
