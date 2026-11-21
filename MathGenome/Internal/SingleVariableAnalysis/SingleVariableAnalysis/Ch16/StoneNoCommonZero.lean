import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.StoneNoCommonZero
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.StoneReal
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.Weierstrass

/-!
K03.16.stone_real, no-common-zero variant. We first construct a finite
sum of squares with strictly positive lower bound. Weierstrass applied
to the reciprocal on its range gives polynomials X*p in the original
nonunital algebra approximating 1. Only then is its closed algebra
regarded as unital and the upstream real Stone–Weierstrass theorem used.
-/
noncomputable section
open scoped Topology

namespace SingleVariableAnalysis

open Specs.SingleVariableAnalysis.Ch16.StoneNoCommonZero

theorem nonunital_sumSquares_mem {K : Set ℝ}
    (A : NonUnitalSubalgebra ℝ C(K, ℝ)) (s : Finset A) :
    sumSquares A s ∈ A := by
  exact sum_mem fun u _ => A.mul_mem u.property u.property

theorem nonunital_positive_sumSquares :
    Specs.SingleVariableAnalysis.Ch16.StoneNoCommonZero.positiveSumSquares := by
  intro K _ A hA
  classical
  let U : A → Set K := fun u => {x | (u : C(K, ℝ)) x ≠ 0}
  have hU : ∀ u, IsOpen (U u) := fun u =>
    isOpen_ne.preimage (u : C(K, ℝ)).continuous
  have hcover : (Set.univ : Set K) ⊆ ⋃ u, U u := by
    intro x _
    obtain ⟨u, hu, hx⟩ := hA x
    exact Set.mem_iUnion.mpr ⟨⟨u, hu⟩, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let t := sumSquares A s
  have htpos : ∀ x : K, 0 < t x := by
    intro x
    obtain ⟨u, hu, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    have hsum : t x = ∑ u ∈ s, ((u : C(K, ℝ)) x) ^ 2 := by
      simp [t, sumSquares, ContinuousMap.sum_apply, pow_two]
    rw [hsum]
    exact Finset.sum_pos' (fun v _ => sq_nonneg _) ⟨u, hu, sq_pos_of_ne_zero hx⟩
  rcases isEmpty_or_nonempty K with hK | hK
  · exact ⟨s, 1, 1, by norm_num, le_rfl, fun x => isEmptyElim x⟩
  · obtain ⟨x₀, _, hx₀⟩ := isCompact_univ.exists_isMinOn
      Set.univ_nonempty t.continuous.continuousOn
    refine ⟨s, t x₀, max (t x₀) ‖t‖, htpos x₀, le_max_left _ _, fun x => ?_⟩
    refine ⟨hx₀ (Set.mem_univ x), ?_⟩
    have hxnorm : |t x| ≤ ‖t‖ := by
      simpa only [Real.norm_eq_abs] using t.norm_coe_le_norm x
    exact (le_abs_self (t x)).trans (hxnorm.trans (le_max_right _ _))

/-- Multiplication by t removes the constant term; no unit of A is used. -/
theorem nonunital_mul_polynomialMap_mem {K : Set ℝ}
    (A : NonUnitalSubalgebra ℝ C(K, ℝ)) (t : C(K, ℝ)) (ht : t ∈ A)
    (p : Polynomial ℝ) : t * polynomialMap p t ∈ A := by
  induction p using Polynomial.induction_on with
  | C a =>
    have heq : t * polynomialMap (Polynomial.C a) t = a • t := by
      ext x
      simp [polynomialMap, mul_comm]
    rw [heq]
    exact A.smul_mem a ht
  | add p q hp hq =>
    have heq : t * polynomialMap (p + q) t =
        t * polynomialMap p t + t * polynomialMap q t := by
      ext x
      simp [polynomialMap, mul_add]
    rw [heq]
    exact A.add_mem hp hq
  | monomial n a h =>
    have heq : t * polynomialMap (Polynomial.C a * Polynomial.X ^ (n + 1)) t =
        t * (t * polynomialMap (Polynomial.C a * Polynomial.X ^ n) t) := by
      ext x
      simp only [ContinuousMap.mul_apply, polynomialMap, ContinuousMap.coe_mk,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, pow_succ]
      ring
    rw [heq]
    exact A.mul_mem ht h

theorem nonunital_polynomial_unit_approximation :
    Specs.SingleVariableAnalysis.Ch16.StoneNoCommonZero.polynomialUnitApproximation := by
  intro K _ A t ht m M hm hmM hbounds ε hε
  have hM : 0 < M + 1 := by linarith
  let f : C(Set.Icc m M, ℝ) :=
    ⟨fun s => (s : ℝ)⁻¹,
      continuous_subtype_val.inv₀ (fun s => ne_of_gt (hm.trans_le s.property.1))⟩
  obtain ⟨p, hp⟩ := real_weierstrass_approximation m M hmM f
    (ε / (M + 1)) (div_pos hε hM)
  refine ⟨p, by simp, ?_, ?_⟩
  · have heq : polynomialMap (Polynomial.X * p) t = t * polynomialMap p t := by
      ext x
      simp [polynomialMap]
    rw [heq]
    exact nonunital_mul_polynomialMap_mem A t ht p
  · apply (ContinuousMap.norm_lt_iff _ hε).mpr
    intro x
    let s : Set.Icc m M := ⟨t x, hbounds x⟩
    have herr : |(t x)⁻¹ - p.eval (t x)| < ε / (M + 1) := by
      have he := (f - (⟨fun y => p.eval (y : ℝ),
        p.continuous.comp continuous_subtype_val⟩ : C(Set.Icc m M, ℝ))).norm_coe_le_norm s
      change ‖(t x)⁻¹ - p.eval (t x)‖ ≤ _ at he
      rw [Real.norm_eq_abs] at he
      exact he.trans_lt hp
    have htx : 0 < t x := hm.trans_le (hbounds x).1
    have hid : 1 - t x * p.eval (t x) = t x * ((t x)⁻¹ - p.eval (t x)) := by
      rw [mul_sub, mul_inv_cancel₀ (ne_of_gt htx)]
    change ‖1 - (Polynomial.X * p).eval (t x)‖ < ε
    rw [Polynomial.eval_mul, Polynomial.eval_X, hid, Real.norm_eq_abs, abs_mul,
      abs_of_pos htx]
    calc
      t x * |(t x)⁻¹ - p.eval (t x)| ≤
          (M + 1) * |(t x)⁻¹ - p.eval (t x)| :=
        mul_le_mul_of_nonneg_right (by linarith [(hbounds x).2]) (abs_nonneg _)
      _ < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left herr hM
      _ = ε := by field_simp

theorem nonunital_unit_in_uniform_closure :
    Specs.SingleVariableAnalysis.Ch16.StoneNoCommonZero.unitInClosure := by
  intro K _ A hA
  obtain ⟨s, m, M, hm, hmM, hbounds⟩ := nonunital_positive_sumSquares K A hA
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨p, _, hp, herr⟩ := nonunital_polynomial_unit_approximation K A
    (sumSquares A s) (nonunital_sumSquares_mem A s) m M hm hmM hbounds ε hε
  exact ⟨_, hp, by simpa only [dist_eq_norm] using herr⟩

theorem nonunital_unit_approximation_sequence :
    Specs.SingleVariableAnalysis.Ch16.StoneNoCommonZero.unitApproximationSequence := by
  intro K _ A hA
  classical
  obtain ⟨s, m, M, hm, hmM, hbounds⟩ := nonunital_positive_sumSquares K A hA
  have happrox := fun n : ℕ => nonunital_polynomial_unit_approximation K A
    (sumSquares A s) (nonunital_sumSquares_mem A s) m M hm hmM hbounds
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose p hp using happrox
  refine ⟨s, m, M, p, hm, hmM, hbounds, hp, ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_order.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 ε hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact (hp n).2.2.trans (hN n hn)

theorem nonunital_stone_weierstrass_uniform_closure :
    Specs.SingleVariableAnalysis.Ch16.StoneNoCommonZero.uniformClosureEqUniv := by
  intro K _ A hsep hzero
  have h1 : (1 : C(K, ℝ)) ∈ A.topologicalClosure :=
    nonunital_unit_in_uniform_closure K A hzero
  let B := A.topologicalClosure.toSubalgebra h1
  have hBsep : ∀ x y : K, x ≠ y → ∃ u ∈ B, u x ≠ u y := by
    intro x y hxy
    obtain ⟨u, hu, hune⟩ := hsep x y hxy
    exact ⟨u, A.le_topologicalClosure hu, hune⟩
  have hB := real_stone_weierstrass_uniform_closure K B hBsep
  have hclosed : IsClosed (B : Set C(K, ℝ)) := A.isClosed_topologicalClosure
  rw [hclosed.closure_eq] at hB
  exact hB

theorem nonunital_stone_weierstrass_closure :
    Specs.SingleVariableAnalysis.Ch16.StoneNoCommonZero.closureEqTop := by
  intro K _ A hsep hzero
  apply SetLike.coe_injective
  exact nonunital_stone_weierstrass_uniform_closure K A hsep hzero

theorem nonunital_stone_weierstrass_uniform_approximation :
    Specs.SingleVariableAnalysis.Ch16.StoneNoCommonZero.uniformApproximation := by
  intro K _ A hsep hzero f ε hε
  have hf : f ∈ closure (A : Set C(K, ℝ)) := by
    rw [nonunital_stone_weierstrass_uniform_closure K A hsep hzero]
    exact Set.mem_univ f
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf ε hε
  exact ⟨g, hg, by simpa only [dist_eq_norm] using hfg⟩

theorem nonunital_stone_weierstrass_pointwise_approximation :
    Specs.SingleVariableAnalysis.Ch16.StoneNoCommonZero.pointwiseApproximation := by
  intro K _ A hsep hzero f ε hε
  obtain ⟨g, hg, hfg⟩ :=
    nonunital_stone_weierstrass_uniform_approximation K A hsep hzero f ε hε
  refine ⟨g, hg, fun x => ?_⟩
  exact (show |f x - g x| ≤ ‖f - g‖ by
    simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using
      (f - g).norm_coe_le_norm x).trans_lt hfg

end SingleVariableAnalysis
