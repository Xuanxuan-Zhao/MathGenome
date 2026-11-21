import MathGenome.Internal.Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample
import MathGenome.Internal.D07.Ch11.ReductionIrreducibility
import MathGenome.Internal.D07.Ch14.PolynomialRootAction
import MathGenome.Internal.D07.Ch15.NormalClosureCriterionQuadraticTowerNormalEnvelope
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

universe u

namespace D07.Ch15.DegreeObstructionQuarticS4Counterexample
open Polynomial IntermediateField
open Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample

lemma quarticInt_monic : quarticInt.Monic := by
  unfold quarticInt
  monicity <;> norm_num

lemma quartic_monic : quartic.Monic := by
  unfold quartic
  monicity <;> norm_num

lemma quartic_natDegree : quartic.natDegree = 4 := by
  unfold quartic
  compute_degree <;> norm_num

lemma reduction_eq : quarticInt.map (Int.castRingHom (ZMod 2)) =
    (X ^ 4 + X + 1 : (ZMod 2)[X]) := by
  simp only [quarticInt, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_one]
  simp [sub_eq_add_neg, CharTwo.neg_eq]

set_option maxHeartbeats 1000000 in
lemma mod_two_irreducible : Irreducible (X ^ 4 + X + 1 : (ZMod 2)[X]) := by
  let p : (ZMod 2)[X] := X^4+X+1
  have hm : p.Monic := by dsimp [p]; monicity <;> norm_num
  have hd : p.natDegree = 4 := by dsimp [p]; compute_degree <;> norm_num
  change Irreducible p
  apply (hm.irreducible_iff_lt_natDegree_lt (by intro h; have := congrArg natDegree h; simp_all)).mpr
  intro q hq hqd hqp
  have hqle : q.natDegree < 3 := by have h := (Finset.mem_Ioc.mp hqd).2; rw [hd] at h; omega
  have hr := q.as_sum_range' 3 hqle
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    mul_one, pow_one] at hr
  have h0 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h0 (q.coeff 0) with h0 | h0 <;>
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 from by decide) (q.coeff 1) with h1 | h1 <;>
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 from by decide) (q.coeff 2) with h2 | h2
  all_goals
    simp only [h0, h1, h2, monomial_zero_right] at hr
    dsimp [p] at hqp
    first
    | have hc : q.eval 0 = 0 := by rw [hr]; norm_num [eval_monomial] <;> decide
      have he := Polynomial.eval_dvd (x := 0) hqp
      simp [p, hc] at he
    | have hc : q.eval 1 = 0 := by rw [hr]; norm_num [eval_monomial] <;> decide
      have he := Polynomial.eval_dvd (x := 1) hqp
      simp [p, hc] at he
      exact (by decide : (1 : ZMod 2) + 1 + 1 ≠ 0) he
    | have h := (Finset.mem_Ioc.mp hqd).1
      rw [hr] at h
      norm_num at h
      done
    | have hid : (X^4+X+1 : (ZMod 2)[X]) -
          ((monomial 0) 1 + (monomial 1) 1 + (monomial 2) 1) * (X^2+X) = 1 := by
        simp only [monomial_zero_left, monomial_one_right_eq_X_pow]
        ring_nf
        simp [show (2 : (ZMod 2)[X]) = 0 from by change C (2 : ZMod 2) = 0; rw [show (2 : ZMod 2) = 0 by decide]; exact C_0]
      have hu : IsUnit q := isUnit_of_dvd_one (by
        rw [hr]
        conv_rhs => rw [← hid]
        exact dvd_sub (by simpa only [hr] using hqp) (dvd_mul_right _ _))
      have h := (Finset.mem_Ioc.mp hqd).1
      rw [Polynomial.natDegree_eq_zero_of_isUnit hu] at h
      omega

theorem reduction_irreducible : ReductionIrreducible := by
  change Irreducible (quarticInt.map (Int.castRingHom (ZMod 2)))
  rw [reduction_eq]
  exact mod_two_irreducible

theorem quartic_irreducible : QuarticIrreducible := by
  have h := (Ch11.ReductionIrreducibility.integerReduction 2 quarticInt
    quarticInt_monic reduction_irreducible).2
  simpa [QuarticIrreducible, quarticInt, quartic] using h

lemma root_side {x : ℝ} (hx : x^4-x-1=0) : x < 0 ∨ 1 < x := by
  by_contra! h
  have hc : x^3 ≤ 1 := pow_le_one₀ h.1 h.2
  have hc' := mul_nonneg h.1 (sub_nonneg.mpr hc)
  nlinarith
lemma root_unique_neg {x y : ℝ} (hx : x^4-x-1=0) (hy : y^4-y-1=0)
    (hx0 : x < 0) (hy0 : y < 0) : x=y := by
  have hp : (x+y)*(x^2+y^2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have he : (x-y)*((x+y)*(x^2+y^2)-1)=0 := by nlinarith [hx,hy]
  rcases mul_eq_zero.mp he with he | he <;> linarith
lemma root_unique_pos {x y : ℝ} (hx : x^4-x-1=0) (hy : y^4-y-1=0)
    (hx0 : 1 < x) (hy0 : 1 < y) : x=y := by
  have hx3 : 1 ≤ x^3 := one_le_pow₀ (by linarith : 1 ≤ x)
  have hy3 : 1 ≤ y^3 := one_le_pow₀ (by linarith : 1 ≤ y)
  have hp1 : 0 ≤ x^2*y := mul_nonneg (sq_nonneg x) (by linarith)
  have hp2 : 0 ≤ x*y^2 := mul_nonneg (by linarith) (sq_nonneg y)
  have he : (x-y)*(x^3+x^2*y+x*y^2+y^3-1)=0 := by nlinarith [hx,hy]
  rcases mul_eq_zero.mp he with he | he <;> linarith
theorem exactly_two_real_roots : ExactlyTwoRealRoots := by
  suffices h : ∃ a b : ℝ, a ∈ Set.Ioo (-1) 0 ∧ b ∈ Set.Ioo 1 2 ∧
      ∀ x, x^4-x-1=0 ↔ x=a ∨ x=b by
    simpa [ExactlyTwoRealRoots, quartic] using h
  let f : ℝ → ℝ := fun x => x^4-x-1
  have hc : Continuous f := by fun_prop
  obtain ⟨a, ha, hfa⟩ := intermediate_value_Icc' (by norm_num : (-1:ℝ) ≤ 0)
    hc.continuousOn (by norm_num [f] : (0:ℝ) ∈ Set.Icc (f 0) (f (-1)))
  obtain ⟨b, hb, hfb⟩ := intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2)
    hc.continuousOn (by norm_num [f] : (0:ℝ) ∈ Set.Icc (f 1) (f 2))
  have har : a^4-a-1=0 := hfa
  have hbr : b^4-b-1=0 := hfb
  have han : a < 0 := by rcases root_side har with h | h; exact h; linarith [ha.2]
  have hbp : 1 < b := by rcases root_side hbr with h | h; linarith [hb.1]; exact h
  refine ⟨a,b,⟨?_,han⟩,⟨hbp,?_⟩,?_⟩
  · rcases lt_or_eq_of_le ha.1 with h | h
    · exact h
    · rw [← h] at har; norm_num at har
  · rcases lt_or_eq_of_le hb.2 with h | h
    · exact h
    · rw [h] at hbr; norm_num at hbr
  · intro x
    constructor
    · intro hx
      rcases root_side hx with h | h
      · exact Or.inl (root_unique_neg hx har h han)
      · exact Or.inr (root_unique_pos hx hbr h hbp)
    · rintro (rfl | rfl) <;> assumption

lemma quartic_vieta {F : Type*} [Field F] [Algebra ℚ F] (r : Fin 4 → F)
    (hr : quartic.map (algebraMap ℚ F) = ∏ i, (X - C (r i))) :
    r 0+r 1+r 2+r 3=0 ∧
    r 0*r 1+r 0*r 2+r 0*r 3+r 1*r 2+r 1*r 3+r 2*r 3=0 ∧
    r 0*r 1*r 2+r 0*r 1*r 3+r 0*r 2*r 3+r 1*r 2*r 3=1 ∧
    r 0*r 1*r 2*r 3 = -1 := by
  have hprod : (∏ i, (X-C (r i)) : F[X]) =
      X^4-C (r 0+r 1+r 2+r 3)*X^3 +
      C (r 0*r 1+r 0*r 2+r 0*r 3+r 1*r 2+r 1*r 3+r 2*r 3)*X^2 -
      C (r 0*r 1*r 2+r 0*r 1*r 3+r 0*r 2*r 3+r 1*r 2*r 3)*X +
      C (r 0*r 1*r 2*r 3) := by
    norm_num [Fin.prod_univ_succ, map_add, map_mul]
    ring
  rw [hprod] at hr
  simp only [quartic, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_one] at hr
  have h1 := congrArg (fun p : F[X] => p.coeff 3) hr
  have h2 := congrArg (fun p : F[X] => p.coeff 2) hr
  have h3 := congrArg (fun p : F[X] => p.coeff 1) hr
  have h4 := congrArg (fun p : F[X] => p.coeff 0) hr
  norm_num only [coeff_sub, coeff_add, coeff_X_pow, coeff_X, coeff_one,
    coeff_C, coeff_C_mul_X_pow, coeff_C_mul_X] at h1 h2 h3 h4
  simp only [ite_true, ite_false, zero_sub, sub_zero, zero_add, add_zero] at h1 h2 h3 h4
  exact ⟨by linear_combination h1, by linear_combination -h2,
    by linear_combination h3, h4.symm⟩

lemma pairProducts_injective {F : Type*} [Field F] (r : Fin 4 → F)
    (hr : Function.Injective r) : Function.Injective (pairProducts r) := by
  have hne {i j : Fin 4} (h : i ≠ j) : r i - r j ≠ 0 :=
    sub_ne_zero.mpr (fun he => h (hr he))
  have h01 : pairProducts r 0 ≠ pairProducts r 1 := by
    intro h
    have hd : pairProducts r 0 - pairProducts r 1 = (r 0-r 3)*(r 1-r 2) := by
      simp [pairProducts]; ring
    exact (mul_ne_zero (hne (by decide)) (hne (by decide))) (hd.symm.trans (sub_eq_zero.mpr h))
  have h02 : pairProducts r 0 ≠ pairProducts r 2 := by
    intro h
    have hd : pairProducts r 0 - pairProducts r 2 = (r 0-r 2)*(r 1-r 3) := by
      simp [pairProducts]; ring
    exact (mul_ne_zero (hne (by decide)) (hne (by decide))) (hd.symm.trans (sub_eq_zero.mpr h))
  have h12 : pairProducts r 1 ≠ pairProducts r 2 := by
    intro h
    have hd : pairProducts r 1 - pairProducts r 2 = (r 0-r 1)*(r 2-r 3) := by
      simp [pairProducts]; ring
    exact (mul_ne_zero (hne (by decide)) (hne (by decide))) (hd.symm.trans (sub_eq_zero.mpr h))
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

lemma pairProducts_factorization {F : Type*} [Field F] [Algebra ℚ F] (r : Fin 4 → F)
    (hr : quartic.map (algebraMap ℚ F) = ∏ i, (X-C (r i))) :
    resolvent.map (algebraMap ℚ F) = ∏ i, (X-C (pairProducts r i)) := by
  obtain ⟨h1,h2,h3,h4⟩ := quartic_vieta r hr
  have hb1 : pairProducts r 0 + pairProducts r 1 + pairProducts r 2 = 0 := by
    dsimp [pairProducts]; linear_combination h2
  have hb2 : pairProducts r 0 * pairProducts r 1 +
      pairProducts r 0 * pairProducts r 2 + pairProducts r 1 * pairProducts r 2 = 4 := by
    dsimp [pairProducts]
    linear_combination (r 0*r 1*r 2+r 0*r 1*r 3+r 0*r 2*r 3+r 1*r 2*r 3)*h1 - 4*h4
  have hb3 : pairProducts r 0 * pairProducts r 1 * pairProducts r 2 = 1 := by
    dsimp [pairProducts]
    linear_combination (r 0+r 1+r 2+r 3)*(r 0*r 1*r 2*r 3)*h1 +
      (r 0*r 1*r 2+r 0*r 1*r 3+r 0*r 2*r 3+r 1*r 2*r 3+1)*h3 -
      4*(r 0*r 1*r 2*r 3)*h2
  have hprod : (∏ i, (X-C (pairProducts r i)) : F[X]) =
      X^3 - C (pairProducts r 0 + pairProducts r 1 + pairProducts r 2)*X^2 +
      C (pairProducts r 0 * pairProducts r 1 + pairProducts r 0 * pairProducts r 2 +
        pairProducts r 1 * pairProducts r 2)*X -
      C (pairProducts r 0 * pairProducts r 1 * pairProducts r 2) := by
    norm_num [Fin.prod_univ_succ, map_add, map_mul]
    ring
  rw [hprod,hb1,hb2,hb3]
  simp [Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample.resolvent]

theorem resolvent_roots : ResolventRoots.{u} := by
  intro F _ _ r hinj hroots
  refine ⟨pairProducts_injective r hinj, pairProducts_factorization r hroots, ?_⟩
  intro i
  change eval₂ (algebraMap ℚ F) (pairProducts r i)
    Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample.resolvent = 0
  rw [← eval_map, pairProducts_factorization r hroots, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

/-- The cubic has no root modulo seven, hence its integral and rational
models are irreducible. This supplies a separate irreducibility proof,
independent of any splitting-field group calculation. -/
theorem resolvent_irreducible : ResolventIrreducible := by
  let f : ℤ[X] := X^3+C 4*X-1
  have hf : f.Monic := by dsimp [f]; monicity <;> norm_num
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hmod : Irreducible (f.map (Int.castRingHom (ZMod 7))) := by
    have hm : f.map (Int.castRingHom (ZMod 7)) =
        (X^3+C 4*X-1 : (ZMod 7)[X]) := by simp [f, C_ofNat]
    rw [hm]
    apply irreducible_of_degree_le_three_of_not_isRoot
    · have hd : (X^3+C 4*X-1 : (ZMod 7)[X]).natDegree = 3 := by
        compute_degree <;> decide
      rw [hd]; decide
    · intro x hx
      have hn : ∀ x : ZMod 7, x^3+4*x-1 ≠ 0 := by decide
      exact hn x (by simpa [IsRoot] using hx)
  have h := (Ch11.ReductionIrreducibility.integerReduction 7 f hf hmod).2
  simpa [ResolventIrreducible, Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample.resolvent,
    f, C_ofNat] using h

lemma root_integral {F : Type*} [Field F] [Algebra ℚ F] (a : F)
    (ha : aeval a quartic = 0) : IsIntegral ℚ a :=
  ⟨quartic, quartic_monic, ha⟩

lemma root_minpoly {F : Type*} [Field F] [Algebra ℚ F] (a : F)
    (ha : aeval a quartic = 0) : minpoly ℚ a = quartic :=
  (minpoly.eq_of_irreducible_of_monic quartic_irreducible ha quartic_monic).symm

/-- Degree four follows from the actual irreducible minimal polynomial. -/
theorem real_root_degree : RealRootDegree := by
  intro a ha
  rw [adjoin.finrank (root_integral a ha), root_minpoly a ha, quartic_natDegree]

lemma normalClosure_simple_eq_adjoin_roots {K E L : Type*} [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [IsAlgClosed L] (a : E) (ha : IsIntegral K a) :
    normalClosure K K⟮a⟯ L = adjoin K ((minpoly K a).rootSet L) := by
  let A := (K⟮a⟯ : IntermediateField K E)
  let x : A := ⟨a, mem_adjoin_simple_self K a⟩
  have hx : minpoly K x = minpoly K a := by
    exact (minpoly.algHom_eq A.val A.val.injective x).symm
  let : FiniteDimensional K A := adjoin.finiteDimensional ha
  apply le_antisymm
  · apply normalClosure_le_iff.mpr
    intro f z hz
    obtain ⟨y, rfl⟩ := hz
    have hg : ∀ b (hb : b ∈ ({a} : Set E)),
        f ⟨b, subset_adjoin K {a} hb⟩ ∈ adjoin K ((minpoly K a).rootSet L) := by
      intro b hb
      have hba : b = a := Set.mem_singleton_iff.mp hb
      subst b
      apply subset_adjoin K _
      apply (mem_rootSet_of_ne (minpoly.ne_zero ha)).mpr
      change aeval (f x) (minpoly K a) = 0
      rw [← hx, aeval_algHom_apply, minpoly.aeval, map_zero]
    exact IntermediateField.adjoin_induction K
      (motive := fun b hb => f ⟨b,hb⟩ ∈ adjoin K ((minpoly K a).rootSet L))
      hg
      (fun k => by simpa using (adjoin K ((minpoly K a).rootSet L)).algebraMap_mem k)
      (fun b c hb hc hfb hfc => by
        change f (⟨b,hb⟩ + ⟨c,hc⟩) ∈ _
        rw [map_add]
        exact IntermediateField.add_mem _ hfb hfc)
      (fun b hb hfb => by
        change f ((⟨b,hb⟩ : A)⁻¹) ∈ _
        rw [map_inv₀]
        exact IntermediateField.inv_mem _ hfb)
      (fun b c hb hc hfb hfc => by
        change f (⟨b,hb⟩ * ⟨c,hc⟩) ∈ _
        rw [map_mul]
        exact IntermediateField.mul_mem _ hfb hfc) y.2
  · rw [Algebra.IsAlgebraic.normalClosure_eq_iSup_adjoin_of_splits
      (fun b : A => IsAlgClosed.splits ((minpoly K b).map (algebraMap K L)))]
    rw [← hx]
    exact le_iSup (fun b : A => adjoin K ((minpoly K b).rootSet L)) x

/-- The normal closure includes all conjugates in ℂ, rather than just the
real roots. It is exactly the field generated by the roots of the quartic. -/
theorem real_root_normal_closure : RealRootNormalClosure := by
  intro a ha
  rw [normalClosure_simple_eq_adjoin_roots a (root_integral a ha), root_minpoly a ha]
  rfl

lemma subgroup_eq_top_of_twelve_and_swap (G : Subgroup (Equiv.Perm (Fin 4)))
    (h4 : 4 ∣ Nat.card G) (h3 : 3 ∣ Nat.card G)
    (a b : Fin 4) (hab : a ≠ b) (hs : Equiv.swap a b ∈ G) : G = ⊤ := by
  have hd : Nat.card G ∣ 24 := by
    have hcard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_perm, Nat.card_fin]; rfl
    simpa only [hcard] using G.card_subgroup_dvd_card
  have hm : Nat.card G ∈ Nat.divisors 24 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hdivs : Nat.divisors 24 = {1,2,3,4,6,8,12,24} := by decide
  rw [hdivs] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hcases : Nat.card G = 12 ∨ Nat.card G = 24 := by omega
  have hi := G.index_mul_card
  rw [Nat.card_perm, Nat.card_fin] at hi
  norm_num at hi
  rcases hcases with h12 | h24
  · rw [h12] at hi
    have hi2 : G.index = 2 := by omega
    have hG := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi2
    rw [hG, Equiv.Perm.mem_alternatingGroup] at hs
    rw [Equiv.Perm.sign_swap hab] at hs
    exact False.elim ((by decide : (-1 : ℤˣ) ≠ 1) hs)
  · rw [h24] at hi
    have hi1 : G.index = 1 := by omega
    exact Subgroup.index_eq_one.mp hi1

namespace ComplexConjugation
local notation "S" => complexSplittingField
instance splittingField : quartic.IsSplittingField ℚ S :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
instance normalField : Normal ℚ S := Normal.of_isSplittingField quartic

noncomputable def sigma : S ≃ₐ[ℚ] S := (Complex.conjAe.restrictScalars ℚ).restrictNormal S
lemma sigma_apply (x : S) : (sigma x : ℂ) = star (x : ℂ) := by
  exact AlgEquiv.restrictNormal_commutes (Complex.conjAe.restrictScalars ℚ) S x

noncomputable def perm := Specs.D07.Ch14.PolynomialRootAction.rootPermutationValue ℚ S quartic sigma

lemma root_complex {x : S} (hx : x ∈ quartic.rootSet S) :
    aeval (x : ℂ) quartic = 0 := by
  have h := (mem_rootSet.mp hx).2
  change aeval (complexSplittingField.val x) quartic = 0
  rw [aeval_algHom_apply, h, map_zero]

noncomputable def realRoot (a : ℝ) (ha : aeval a quartic = 0) : quartic.rootSet S := by
  have hac : aeval (a : ℂ) quartic = 0 := by
    simp only [quartic, map_sub, map_pow, aeval_X, map_one] at ha ⊢
    exact_mod_cast ha
  have hm : (a : ℂ) ∈ S := subset_adjoin ℚ _ ((mem_rootSet_of_ne quartic_irreducible.ne_zero).mpr hac)
  refine ⟨⟨a,hm⟩, (mem_rootSet_of_ne quartic_irreducible.ne_zero).mpr ?_⟩
  apply complexSplittingField.val.injective
  change complexSplittingField.val (aeval (⟨a,hm⟩ : S) quartic) =
    complexSplittingField.val 0
  rw [← aeval_algHom_apply, map_zero]
  exact hac

lemma perm_apply (z : quartic.rootSet S) : ((perm z : S) : ℂ) = star ((z : S) : ℂ) :=
  sigma_apply z

theorem real_conjugation_transposition : RealConjugationTransposition := by
  classical
  obtain ⟨a,b,ha,hb,hroots⟩ := exactly_two_real_roots
  have hra : aeval a quartic = 0 := (hroots a).mpr (Or.inl rfl)
  have hrb : aeval b quartic = 0 := (hroots b).mpr (Or.inr rfl)
  let ar := realRoot a hra
  let br := realRoot b hrb
  have har : (((ar : quartic.rootSet S) : S) : ℂ) = a := rfl
  have hbr : (((br : quartic.rootSet S) : S) : ℂ) = b := rfl
  have hab : ar ≠ br := by
    intro h
    have h' := congrArg (fun z : quartic.rootSet S => ((z : S) : ℂ)) h
    rw [har,hbr] at h'
    have : a=b := Complex.ofReal_injective h'
    linarith [ha.2,hb.1]
  have hfix (z : quartic.rootSet S) : perm z = z ↔ z=ar ∨ z=br := by
    constructor
    · intro hz
      have hz' := congrArg (fun z : quartic.rootSet S => ((z : S) : ℂ)) hz
      rw [perm_apply] at hz'
      obtain ⟨r,hr⟩ := Complex.conj_eq_iff_real.mp hz'
      have hrroot : aeval r quartic = 0 := by
        have hh := root_complex z.2
        rw [hr] at hh
        simp only [quartic, map_sub, map_pow, aeval_X, map_one] at hh ⊢
        exact_mod_cast hh
      rcases (hroots r).mp hrroot with he | he
      · left
        apply Subtype.ext; apply Subtype.ext
        rw [har,hr,he]
      · right
        apply Subtype.ext; apply Subtype.ext
        rw [hbr,hr,he]
    · rintro (rfl | rfl)
      all_goals
        apply Subtype.ext; apply Subtype.ext
        rw [perm_apply]
        simp only [har,hbr,Complex.star_def, Complex.conj_ofReal]
  have hcard : Fintype.card (quartic.rootSet S) = 4 := by
    rw [Polynomial.card_rootSet_eq_natDegree quartic_irreducible.separable
      (Polynomial.IsSplittingField.splits S quartic), quartic_natDegree]
  have hsupport : perm.support = Finset.univ \ {ar,br} := by
    ext z
    simp only [Equiv.Perm.mem_support, Finset.mem_sdiff, Finset.mem_univ,
      Finset.mem_insert, Finset.mem_singleton, true_and, ne_eq, hfix, not_or]
  have hswap : Equiv.Perm.IsSwap perm := by
    apply Equiv.Perm.card_support_eq_two.mp
    rw [hsupport, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hcard,hab]
  obtain ⟨u,v,huv,hperm⟩ := hswap
  exact ⟨sigma, sigma_apply, u,v,huv,hperm⟩
end ComplexConjugation


local notation "S" => complexSplittingField
-- Factorization from a numbering of the distinct roots.
lemma numbered_factorization {F : Type*} [Field F] [Algebra ℚ F]
    (b : Fin 4 ≃ quartic.rootSet F) :
    quartic.map (algebraMap ℚ F) = ∏ i, (X-C ((b i).val)) := by
  classical
  have hinj : Function.Injective (fun i => (b i).val) :=
    Subtype.val_injective.comp b.injective
  have hdvd : (∏ i, (X-C ((b i).val)) : F[X]) ∣ quartic.map (algebraMap ℚ F) := by
    apply Finset.prod_dvd_of_coprime
    · exact (pairwise_coprime_X_sub_C hinj).set_pairwise _
    · intro i _
      apply dvd_iff_isRoot.mpr
      simpa only [IsRoot, eval_map, aeval_def] using (mem_rootSet.mp (b i).2).2
  apply eq_of_monic_of_dvd_of_natDegree_le
    (monic_prod_X_sub_C _ _) (quartic_monic.map _) hdvd
  rw [quartic_monic.natDegree_map, quartic_natDegree,
    natDegree_finsetProd_X_sub_C_eq_card]
  simp

lemma complex_group_s4 :
    ∃ b : Fin 4 ≃ quartic.rootSet S,
      ∃ e : (S ≃ₐ[ℚ] S) ≃* Equiv.Perm (Fin 4),
        ∀ σ i, (b (e σ i)).val = σ (b i).val := by
  classical
  let : quartic.IsSplittingField ℚ S := ComplexConjugation.splittingField
  let : FiniteDimensional ℚ S := Polynomial.IsSplittingField.finiteDimensional S quartic
  let : Normal ℚ S := Normal.of_isSplittingField quartic
  let : Algebra.IsSeparable ℚ S :=
    Algebra.isSeparable_of_separable_splitting_field ℚ S quartic_irreducible.separable
  let : IsGalois ℚ S := { }
  have hsplit := (D07.Ch12.SplittingDefinition.library_characterization
    ℚ S quartic quartic_irreducible.ne_zero).mpr inferInstance
  obtain ⟨b,ρ,hinj,happly⟩ := D07.Ch14.PolynomialRootAction.numberedEmbedding
    ℚ S quartic 4 (by rw [quartic_natDegree]; decide)
    quartic_irreducible.separable hsplit quartic_natDegree
  let G := ρ.range
  have hcardG : Nat.card G = Module.finrank ℚ S := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      IsGalois.card_aut_eq_finrank]
  have h4 : 4 ∣ Nat.card G := by
    rw [hcardG]
    have ha : aeval (b 0).val quartic = 0 := (mem_rootSet.mp (b 0).2).2
    have hd : Module.finrank ℚ ℚ⟮(b 0).val⟯ = 4 := by
      rw [adjoin.finrank (root_integral _ ha), root_minpoly _ ha, quartic_natDegree]
    rw [← hd]
    exact Module.finrank_dvd_finrank_right ℚ ℚ⟮(b 0).val⟯ S
  let r : Fin 4 → S := fun i => (b i).val
  have hr := numbered_factorization b
  have h3 : 3 ∣ Nat.card G := by
    rw [hcardG]
    have ha : aeval (pairProducts r 0) Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample.resolvent = 0 := by
      change eval₂ (algebraMap ℚ S) (pairProducts r 0)
        Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample.resolvent = 0
      rw [← eval_map, pairProducts_factorization r hr, eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ 0)
      simp
    have hm : Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample.resolvent.Monic := by
      unfold Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample.resolvent
      monicity <;> norm_num
    have hi : IsIntegral ℚ (pairProducts r 0) := ⟨_,hm,ha⟩
    have hmin := minpoly.eq_of_irreducible_of_monic resolvent_irreducible ha hm
    have hd : Module.finrank ℚ ℚ⟮pairProducts r 0⟯ = 3 := by
      rw [adjoin.finrank hi, ← hmin]
      unfold Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample.resolvent
      compute_degree <;> norm_num
    rw [← hd]
    exact Module.finrank_dvd_finrank_right ℚ ℚ⟮pairProducts r 0⟯ S
  obtain ⟨σ,hσ,u,v,huv,hperm⟩ := ComplexConjugation.real_conjugation_transposition
  have heq : ρ σ = Equiv.swap (b.symm u) (b.symm v) := by
    apply Equiv.ext
    intro i
    apply b.injective
    have hh : b (ρ σ i) = Specs.D07.Ch14.PolynomialRootAction.rootPermutationValue
        ℚ S quartic σ (b i) := Subtype.ext (happly σ i)
    rw [hh,hperm]
    by_cases hiu : b i = u
    · have hii : i=b.symm u := by simpa using congrArg b.symm hiu
      simp [hiu,hii]
    · by_cases hiv : b i = v
      · have hii : i=b.symm v := by simpa using congrArg b.symm hiv
        simp [hiv,hii]
      · have hiu' : i ≠ b.symm u := fun h => hiu (by simp [h])
        have hiv' : i ≠ b.symm v := fun h => hiv (by simp [h])
        simp [Equiv.swap_apply_of_ne_of_ne, hiu,hiv,hiu',hiv']
  have hG : G = ⊤ := subgroup_eq_top_of_twelve_and_swap G h4 h3
    (b.symm u) (b.symm v) (fun h => huv (b.symm.injective h)) ⟨σ,heq⟩
  exact ⟨b, MulEquiv.ofBijective ρ ⟨hinj,MonoidHom.range_eq_top.mp hG⟩, happly⟩

theorem galois_group_s4 : GaloisGroupS4.{u} := by
  intro F _ _ _
  classical
  obtain ⟨b,e,hact⟩ := complex_group_s4
  let k : S ≃ₐ[ℚ] F := (Polynomial.IsSplittingField.algEquiv S quartic).trans
    (Polynomial.IsSplittingField.algEquiv F quartic).symm
  let t : quartic.rootSet S ≃ quartic.rootSet F :=
    { toFun := fun x => ⟨k x, rootSet_mapsTo k.toAlgHom x.2⟩
      invFun := fun x => ⟨k.symm x, rootSet_mapsTo k.symm.toAlgHom x.2⟩
      left_inv := fun x => Subtype.ext (k.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (k.apply_symm_apply x) }
  refine ⟨b.trans t, k.autCongr.symm.trans e, ?_⟩
  intro σ i
  change k ((b (e (k.symm.autCongr σ) i)).val) = σ (k (b i).val)
  have h := congrArg k (hact (k.symm.autCongr σ) i)
  simpa [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply] using h

theorem splitting_degree : SplittingDegree.{u} := by
  intro F _ _ _
  let : FiniteDimensional ℚ F := Polynomial.IsSplittingField.finiteDimensional F quartic
  let : Normal ℚ F := Normal.of_isSplittingField quartic
  let : Algebra.IsSeparable ℚ F :=
    Algebra.isSeparable_of_separable_splitting_field ℚ F quartic_irreducible.separable
  let : IsGalois ℚ F := { }
  obtain ⟨b,e,he⟩ := galois_group_s4 F
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl


-- The supplied full root action is a hypothesis of this general helper;
-- its unconditional specialization will use the proved S₄ result.
lemma no_quadratic_of_full_action
    (b : Fin 4 ≃ quartic.rootSet S)
    (e : (S ≃ₐ[ℚ] S) ≃* Equiv.Perm (Fin 4))
    (hact : ∀ σ i, (b (e σ i)).val = σ (b i).val)
    (a : ℝ) (ha : aeval a quartic = 0)
    (E : IntermediateField ℚ ℚ⟮a⟯) (hE : Module.finrank ℚ E = 2) : False := by
  classical
  let : FiniteDimensional ℚ S := Polynomial.IsSplittingField.finiteDimensional S quartic
  let : Normal ℚ S := Normal.of_isSplittingField quartic
  let : Algebra.IsSeparable ℚ S :=
    Algebra.isSeparable_of_separable_splitting_field ℚ S quartic_irreducible.separable
  let : IsGalois ℚ S := { }
  let ar := ComplexConjugation.realRoot a ha
  let x : S := ar.val
  have hx : aeval x quartic = 0 := (mem_rootSet.mp ar.2).2
  let pb := adjoin.powerBasis (root_integral a ha)
  have hy : aeval x (minpoly ℚ pb.gen) = 0 := by
    rw [adjoin.powerBasis_gen, minpoly_gen, root_minpoly a ha]
    exact hx
  let f : ℚ⟮a⟯ →ₐ[ℚ] S := pb.lift x hy
  have hfgen : f (AdjoinSimple.gen ℚ a) = x := pb.lift_gen x hy
  let g : E →ₐ[ℚ] S := f.comp E.val
  let H := g.fieldRange.fixingSubgroup
  have hi : H.index = 2 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    rw [← g.equivFieldRange.toLinearEquiv.finrank_eq]
    exact hE
  have hmap : H.map e.toMonoidHom = alternatingGroup (Fin 4) := by
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    exact (Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective H).trans hi
  let i : Fin 4 := b.symm ar
  obtain ⟨j,k,hji,hki,hjk⟩ : ∃ j k : Fin 4, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
    have hex : ∀ i : Fin 4, ∃ j k : Fin 4, j ≠ i ∧ k ≠ i ∧ j ≠ k := by decide
    exact hex i
  let sigma := e.symm (Equiv.swap j k)
  have hsx : sigma x = x := by
    have hh := hact sigma i
    simp only [sigma, e.apply_symm_apply] at hh
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hji) (Ne.symm hki)] at hh
    simpa [i,x] using hh.symm
  have hsall (y : ℚ⟮a⟯) : sigma (f y) = f y := by
    refine adjoin_induction ℚ
      (motive := fun z hz => sigma (f ⟨z,hz⟩) = f ⟨z,hz⟩) ?_ ?_ ?_ ?_ ?_ y.2
    · intro z hz
      have he : z=a := Set.mem_singleton_iff.mp hz
      subst z
      change sigma (f (AdjoinSimple.gen ℚ a)) = f (AdjoinSimple.gen ℚ a)
      rw [hfgen,hsx]
    · intro c
      change sigma (f (algebraMap ℚ ℚ⟮a⟯ c)) = f (algebraMap ℚ ℚ⟮a⟯ c)
      rw [f.commutes,sigma.commutes]
    · intro z w hz hw hz' hw'
      change sigma (f (⟨z,hz⟩+⟨w,hw⟩)) = f (⟨z,hz⟩+⟨w,hw⟩)
      simp only [map_add,hz',hw']
    · intro z hz hz'
      change sigma (f ((⟨z,hz⟩ : ℚ⟮a⟯)⁻¹)) = f ((⟨z,hz⟩ : ℚ⟮a⟯)⁻¹)
      simp only [map_inv₀,hz']
    · intro z w hz hw hz' hw'
      change sigma (f (⟨z,hz⟩*⟨w,hw⟩)) = f (⟨z,hz⟩*⟨w,hw⟩)
      simp only [map_mul,hz',hw']
  have hsmem : sigma ∈ H := by
    apply (IntermediateField.mem_fixingSubgroup_iff g.fieldRange sigma).mpr
    rintro _ ⟨y,rfl⟩
    exact hsall y.val
  have hswapmem : Equiv.swap j k ∈ alternatingGroup (Fin 4) := by
    rw [← hmap]
    exact ⟨sigma,hsmem,e.apply_symm_apply _⟩
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hjk] at hswapmem
  exact (by decide : (-1 : ℤˣ) ≠ 1) hswapmem

/-- An index-two intermediate field would give A₄ as fixing subgroup,
but the stabilizer of this root contains a transposition of other roots. -/
theorem no_quadratic_intermediate : NoQuadraticIntermediate := by
  intro a ha E hE
  obtain ⟨b,e,hact⟩ := complex_group_s4
  exact no_quadratic_of_full_action b e hact a ha E hE

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- A real quadratic tower has a finite normal envelope of power-of-two
rational degree. Normality would put the whole degree-24 splitting field
inside that envelope, contradicting the factor three in its degree. -/
theorem real_root_not_constructible : RealRootNotConstructible := by
  intro a ha hconstruct
  obtain ⟨M,ht,haM⟩ := hconstruct
  let K : IntermediateField ℚ ℝ := ⊥
  let Ω := AlgebraicClosure K
  obtain ⟨hKM,ι,N,hι,hfin,hgal,⟨n,hn⟩,hN⟩ :=
    D07.Ch15.NormalClosureCriterionQuadraticTowerNormalEnvelope.exists_tower_normal_envelope
      K M ht Ω
  let : FiniteDimensional K N := hfin
  let : IsGalois K N := hgal
  let : FiniteDimensional ℚ N := FiniteDimensional.trans ℚ K N
  have hbase : Module.finrank ℚ K = 1 := by simp [K]
  have hdegree : Module.finrank ℚ N = 2^n := by
    rw [← Module.finrank_mul_finrank ℚ K N,hbase,one_mul]
    exact hn
  let eK : K ≃+* ℚ := (IntermediateField.botEquiv ℚ ℝ).toRingEquiv
  have hcomp : (algebraMap ℚ N).comp eK = (RingHom.id N).comp (algebraMap K N) := by
    apply RingHom.ext
    intro k
    obtain ⟨q,rfl⟩ := eK.symm.surjective k
    change algebraMap ℚ N (eK (eK.symm q)) = algebraMap K N (eK.symm q)
    rw [eK.apply_symm_apply]
    have heq : eK.symm q = algebraMap ℚ K q := rfl
    rw [heq, IsScalarTower.algebraMap_apply ℚ K N]
  let : IsGalois ℚ N := IsGalois.of_equiv_equiv
    (F := K) (E := N) (f := eK) (g := RingEquiv.refl N) hcomp
  let iA : M →ₐ[ℚ] Ω :=
    { toRingHom := ι
      commutes' := fun q => by simp }
  let iN : M →ₐ[ℚ] N := iA.codRestrict (N.restrictScalars ℚ).toSubalgebra (fun y => hN ⟨y,rfl⟩)
  have ham : aeval (⟨a,haM⟩ : M) quartic = 0 := by
    apply M.val.injective
    change M.val (aeval (⟨a,haM⟩ : M) quartic) = M.val 0
    rw [← aeval_algHom_apply,map_zero]
    exact ha
  let x : N := iN ⟨a,haM⟩
  have hx : aeval x quartic = 0 := by
    change aeval (iN ⟨a,haM⟩) quartic = 0
    rw [aeval_algHom_apply,ham,map_zero]
  have hsplit : (quartic.map (algebraMap ℚ N)).Splits := by
    rw [← root_minpoly x hx]
    exact (inferInstance : Normal ℚ N).splits x
  let T := adjoin ℚ (quartic.rootSet N)
  let : quartic.IsSplittingField ℚ T := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hdiv : 24 ∣ 2^n := by
    rw [← splitting_degree T, ← hdegree]
    exact Module.finrank_dvd_finrank_right ℚ T N
  have hthree : 3 ∣ 2^n := dvd_trans (by decide : 3 ∣ 24) hdiv
  have hbad := Nat.prime_three.dvd_of_dvd_pow hthree
  norm_num at hbad

end D07.Ch15.DegreeObstructionQuarticS4Counterexample
