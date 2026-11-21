import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.AsymptoticScale
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.Composition
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
K03.17.operations, paper.tex:4335–4371. Exact errors retain all product
scales. Only the power-scale theorems discard terms, using their degrees.
Every finite order includes order zero. Filters and the function t record
the specified real or complex approach and its domain.
-/

noncomputable section
namespace SingleVariableAnalysis
open Filter Asymptotics Polynomial
open scoped Topology BigOperators
universe u v w

section General
variable {X : Type u} {K : Type v} [NormedField K]

theorem expansion_add_exact (P Q r s : X → K) (x : X) :
    (P x + r x) + (Q x + s x) = (P x + Q x) + (r x + s x) := by ring

theorem expansion_mul_exact (P Q r s : X → K) (x : X) :
    (P x + r x) * (Q x + s x) =
      P x * Q x + (P x * s x + Q x * r x + r x * s x) := by ring

theorem expansion_add (l : Filter X) (φ : ℕ → X → K)
    (a b : ℕ → K) (f g : X → K) (m : ℕ)
    (hf : HasScalarExpansionThrough l φ a f m)
    (hg : HasScalarExpansionThrough l φ b g m) :
    HasScalarExpansionThrough l φ (fun j => a j + b j) (fun x => f x + g x) m := by
  have h := scalarLittleO_add l _ _ _ hf hg
  change ScalarLittleO l _ _
  convert h using 1
  funext x
  simp only [AsymptoticPartialSum, add_mul, Finset.sum_add_distrib]
  ring

/-- No ordering of the product family is presumed. -/
theorem partialSum_mul_scales (φ ψ : ℕ → X → K) (a b : ℕ → K)
    (m n : ℕ) (x : X) :
    AsymptoticPartialSum φ a m x * AsymptoticPartialSum ψ b n x =
      ∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (n+1),
        (a i * b j) * (φ i x * ψ j x) := by
  simp only [AsymptoticPartialSum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Each of the three exact product errors keeps its own comparison scale. -/
theorem expansion_product_errors (l : Filter X) (P Q r s p q α β : X → K)
    (hP : ScalarBigO l P p) (hQ : ScalarBigO l Q q)
    (hr : ScalarLittleO l r α) (hs : ScalarLittleO l s β) :
    ScalarLittleO l (fun x => P x * s x) (fun x => p x * β x) ∧
    ScalarLittleO l (fun x => Q x * r x) (fun x => q x * α x) ∧
    ScalarLittleO l (fun x => r x * s x) (fun x => α x * β x) := by
  exact ⟨scalarBigO_mul_littleO l _ _ _ _ hP hs,
    scalarBigO_mul_littleO l _ _ _ _ hQ hr,
    scalarLittleO_mul_bigO l _ _ _ _ hr (scalarLittleO_isBigO l _ _ hs)⟩

/-- The finite geometric identity requires just a nonzero denominator. -/
theorem finite_reciprocal_identity (z : K) (m : ℕ) (hz : 1 + z ≠ 0) :
    (1 + z)⁻¹ = (∑ j ∈ Finset.range (m+1), (-z)^j) +
      (-z)^(m+1) / (1+z) := by
  have h := geom_sum_mul_neg (-z) (m+1)
  have hs : (∑ j ∈ Finset.range (m+1), (-z)^j) * (1+z) = 1 - (-z)^(m+1) := by
    simpa only [sub_neg_eq_add] using h
  apply (mul_right_cancel₀ hz)
  rw [inv_mul_cancel₀ hz, add_mul, div_mul_cancel₀ _ hz, hs]
  ring

/-- The normalized reciprocal error is little-o even at zeros of u. -/
theorem finite_reciprocal_remainder (l : Filter X) (u : X → K)
    (hu : Tendsto u l (𝓝 0)) (m : ℕ) :
    (∀ᶠ x in l, 1 + u x ≠ 0) ∧
    (fun x => (1 + u x)⁻¹ - ∑ j ∈ Finset.range (m+1), (-u x)^j)
      =o[l] (fun x => u x^m) := by
  have hden : Tendsto (fun x => 1 + u x) l (𝓝 (1 : K)) := by
    simpa using tendsto_const_nhds.add hu
  have hn := hden.eventually_ne one_ne_zero
  refine ⟨hn, ?_⟩
  have hp : (fun x => (-u x)^(m+1)) =o[l] (fun x => u x^m) := by
    have hh := (isLittleO_pow_pow (𝕜 := K) (Nat.lt_succ_self m)).comp_tendsto hu
    exact hh.norm_left.congr_left (fun x => by simp [norm_pow]) |>.of_norm_left
  have hi := (hden.inv₀ one_ne_zero).isBigO_one K
  have hr := hp.mul_isBigO hi
  simp only [mul_one] at hr
  apply hr.congr' _ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hn] with x hx
  have hh := finite_reciprocal_identity (u x) m hx
  simp only [div_eq_mul_inv] at hh
  linear_combination -hh

/-- Factor any eventually nonzero leading scale and coefficient first.
The numerator is arbitrary; its scale is retained in the error bound. -/
theorem factored_division (l : Filter X) (f g ψ u : X → K) (a : K) (m : ℕ)
    (ha : a ≠ 0) (hψ : ∀ᶠ x in l, ψ x ≠ 0)
    (hu : Tendsto u l (𝓝 0))
    (hg : ∀ᶠ x in l, g x = (a * ψ x) * (1 + u x)) :
    (∀ᶠ x in l, g x ≠ 0) ∧
    (fun x => f x / g x - (f x / (a * ψ x)) *
      (∑ j ∈ Finset.range (m+1), (-u x)^j))
      =o[l] (fun x => (f x / (a * ψ x)) * u x^m) := by
  obtain ⟨hn, hr⟩ := finite_reciprocal_remainder l u hu m
  refine ⟨?_, ?_⟩
  · filter_upwards [hψ, hn, hg] with x hx hu hg
    rw [hg]
    exact mul_ne_zero (mul_ne_zero ha hx) hu
  · have h := (isBigO_refl (fun x => f x / (a * ψ x)) l).mul_isLittleO hr
    apply h.congr' _ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hg] with x hx
    rw [hx]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- A leading little-o expansion supplies the normalized factorization;
neither the relative error nor invertibility is an assumed certificate. -/
theorem leading_scale_factorization (l : Filter X) (g ψ : X → K) (a : K)
    (ha : a ≠ 0) (hψ : ∀ᶠ x in l, ψ x ≠ 0)
    (hg : ScalarLittleO l (fun x => g x - a * ψ x) ψ) :
    ∃ u : X → K, Tendsto u l (𝓝 0) ∧
      (∀ᶠ x in l, g x = (a * ψ x) * (1 + u x)) ∧
      (∀ᶠ x in l, g x ≠ 0) := by
  let u := fun x => (g x - a * ψ x) / (a * ψ x)
  have hr := (scalarLittleO_iff_ratio_tendsto l _ ψ hψ).mp hg
  have hu : Tendsto u l (𝓝 0) := by
    simpa only [u, mul_comm a, div_mul_eq_div_div, zero_div] using hr.div_const a
  have he : ∀ᶠ x in l, g x = (a * ψ x) * (1 + u x) := by
    filter_upwards [hψ] with x hx
    dsimp [u]
    field_simp
    ring
  exact ⟨u, hu, he, (factored_division l (fun _ => 1) g ψ u a 0 ha hψ hu he).1⟩

/-- A finite expansion in an arbitrary asymptotic scale exposes its leading
term; this is the input needed for leading-scale factorization. -/
theorem expansion_leading_term (l : Filter X) (φ : ℕ → X → K)
    (hφ : IsScalarAsymptoticScale l φ) (a : ℕ → K) (f : X → K) (m : ℕ)
    (hf : HasScalarExpansionThrough l φ a f m) :
    ScalarLittleO l (fun x => f x - a 0 * φ 0 x) (φ 0) := by
  have htail : ∀ n, (fun x => AsymptoticPartialSum φ a n x - a 0 * φ 0 x) =o[l] φ 0 := by
    intro n
    induction n with
    | zero => simpa only [asymptoticPartialSum_zero, sub_self] using isLittleO_zero (φ 0) l
    | succ n ih =>
      have hstep := (scalarLittleO_iff_isLittleO l _ _).mp
        (isScalarAsymptoticScale_littleO l φ hφ (Nat.zero_lt_succ n))
      convert ih.add (hstep.const_mul_left (a (n+1))) using 1
      funext x
      rw [asymptoticPartialSum_succ]
      ring
  have hlast : (φ m) =O[l] (φ 0) := by
    by_cases hm : m = 0
    · subst m; exact isBigO_refl _ _
    · exact ((scalarLittleO_iff_isLittleO l _ _).mp
        (isScalarAsymptoticScale_littleO l φ hφ (Nat.pos_of_ne_zero hm))).isBigO
  have hr := ((scalarLittleO_iff_isLittleO l _ _).mp hf).trans_isBigO hlast
  apply (scalarLittleO_iff_isLittleO l _ _).mpr
  exact (hr.add (htail m)).congr_left (fun x => by ring)

end General

section Composition
variable {X : Type u} {K : Type v} {L : Type w} [NormedField K] [NormedField L]

/-- The outer remainder has its actual value zero at the expansion point.
Eventual membership in insert 0 D, rather than avoidance of zero, is enough. -/
theorem compose_remainder (l : Filter X) (D : Set K) (t u : X → K)
    (r : K → L) (m : ℕ) (ht : Tendsto t l (𝓝 0)) (hu : u =O[l] t)
    (hD : ∀ᶠ x in l, u x ∈ insert 0 D) (h0 : r 0 = 0)
    (hr : r =o[𝓝[D \ {0}] 0] (fun z => z^m)) :
    (fun x => r (u x)) =o[l] (fun x => t x^m) := by
  have hi : insert 0 (D \ {0}) = insert 0 D := by ext z; simp
  have hh := hr.insert h0
  rw [hi] at hh
  exact (hh.comp_tendsto (tendsto_nhdsWithin_iff.mpr
    ⟨hu.trans_tendsto ht, hD⟩)).trans_isBigO (hu.pow m)

end Composition

section Power
variable {X : Type u} {K : Type v} [RCLike K]

private theorem polynomial_eval_bounded {l : Filter X} {t : X → K}
    (ht : Tendsto t l (𝓝 0)) (P : Polynomial K) :
    (fun x => P.eval (t x)) =O[l] (fun _ => (1 : K)) :=
  ((P.differentiable.continuous.tendsto 0).comp ht).isBigO_one K

private theorem polynomial_eval_vanishing {l : Filter X} {t : X → K}
    (ht : Tendsto t l (𝓝 0)) (P : Polynomial K) (m : ℕ)
    (hP : Polynomial.X^m ∣ P) :
    (fun x => P.eval (t x)) =O[l] (fun x => t x^m) := by
  obtain ⟨Q, rfl⟩ := hP
  simpa only [eval_mul, eval_pow, eval_X, mul_one] using
    (isBigO_refl (fun x => t x^m) l).mul (polynomial_eval_bounded ht Q)

private theorem power_expansion_bounded {l : Filter X} {t : X → K}
    (ht : Tendsto t l (𝓝 0)) (m : ℕ) (f : X → K) (P : Polynomial K)
    (hf : (fun x => f x - P.eval (t x)) =o[l] (fun x => t x^m)) :
    f =O[l] (fun _ => (1 : K)) := by
  have hp := polynomial_eval_bounded ht P
  have htO := (ht.pow m).isBigO_one K
  exact ((hf.isBigO.trans htO).add hp).congr_left (fun x => sub_add_cancel _ _)

/-- Every discarded term of a finite polynomial is higher order. -/
theorem power_polynomial_truncation {l : Filter X} (t : X → K)
    (ht : Tendsto t l (𝓝 0)) (m : ℕ) (P : Polynomial K) :
    (fun x => P.eval (t x) - (TruncatePolynomial m P).eval (t x))
      =o[l] (fun x => t x^m) := by
  simpa only [Function.comp_def, eval_sub] using (polynomial_eval_vanishing ht
    (P - TruncatePolynomial m P) (m+1) (truncatePolynomial_dvd_remainder m P)).trans_isLittleO
      ((isLittleO_pow_pow (Nat.lt_succ_self m)).comp_tendsto ht)

/-- Finite polynomial multiplication along any real or complex approach to zero,
including order zero and points where t itself is zero. -/
theorem power_polynomial_mul {l : Filter X} (t : X → K) (ht : Tendsto t l (𝓝 0))
    (m : ℕ) (f g : X → K) (P Q : Polynomial K)
    (hf : (fun x => f x - P.eval (t x)) =o[l] (fun x => t x^m))
    (hg : (fun x => g x - Q.eval (t x)) =o[l] (fun x => t x^m)) :
    (fun x => f x * g x - (TruncatePolynomial m (P*Q)).eval (t x))
      =o[l] (fun x => t x^m) := by
  have hP := polynomial_eval_bounded ht P
  have hfg := hf.mul_isBigO (power_expansion_bounded ht m g Q hg)
  have hPs := hP.mul_isLittleO hg
  simp only [mul_one] at hfg
  simp only [one_mul] at hPs
  have htr := (polynomial_eval_vanishing ht (P*Q - TruncatePolynomial m (P*Q))
    (m+1) (truncatePolynomial_dvd_remainder m (P*Q))).trans_isLittleO
      ((isLittleO_pow_pow (Nat.lt_succ_self m)).comp_tendsto ht)
  convert (hfg.add hPs).add htr using 1
  funext x
  simp only [eval_sub, eval_mul]
  ring

/-- The coefficient at every retained degree is the finite convolution. -/
theorem power_product_coeff (m : ℕ) (P Q : Polynomial K) (k : ℕ) (hk : k ≤ m) :
    (TruncatePolynomial m (P*Q)).coeff k =
      ∑ j ∈ Finset.range (k+1), P.coeff j * Q.coeff (k-j) := by
  rw [truncatePolynomial_coeff, ite_eq_left hk, coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => P.coeff i * Q.coeff j) k

private theorem finite_power_polynomial_eval (m : ℕ) (a : ℕ → K) (z : K) :
    (∑ j ∈ Finset.range (m+1), monomial j (a j)).eval z =
      ∑ j ∈ Finset.range (m+1), a j * z^j := by
  simp [eval_finsetSum, eval_monomial]

private theorem finite_power_polynomial_coeff (m : ℕ) (a : ℕ → K) (k : ℕ) :
    (∑ j ∈ Finset.range (m+1), monomial j (a j)).coeff k =
      if k ≤ m then a k else 0 := by
  simp [coeff_monomial, Finset.mem_range]

/-- Coefficients of the product are convolved and all degrees above m discarded. -/
theorem power_expansion_mul {l : Filter X} (t : X → K) (ht : Tendsto t l (𝓝 0))
    (a b : ℕ → K) (f g : X → K) (m : ℕ)
    (hf : HasScalarExpansionThrough l (fun j x => t x^j) a f m)
    (hg : HasScalarExpansionThrough l (fun j x => t x^j) b g m) :
    HasScalarExpansionThrough l (fun j x => t x^j)
      (fun k => ∑ j ∈ Finset.range (k+1), a j * b (k-j)) (fun x => f x * g x) m := by
  let P : Polynomial K := ∑ j ∈ Finset.range (m+1), monomial j (a j)
  let Q : Polynomial K := ∑ j ∈ Finset.range (m+1), monomial j (b j)
  have hf' : (fun x => f x - P.eval (t x)) =o[l] (fun x => t x^m) := by
    simpa only [P, finite_power_polynomial_eval, AsymptoticPartialSum] using
      (scalarLittleO_iff_isLittleO l _ _).mp hf
  have hg' : (fun x => g x - Q.eval (t x)) =o[l] (fun x => t x^m) := by
    simpa only [Q, finite_power_polynomial_eval, AsymptoticPartialSum] using
      (scalarLittleO_iff_isLittleO l _ _).mp hg
  have he : TruncatePolynomial m (P*Q) =
      ∑ k ∈ Finset.range (m+1), monomial k
        (∑ j ∈ Finset.range (k+1), a j * b (k-j)) := by
    ext k
    by_cases hk : k ≤ m
    · rw [power_product_coeff m P Q k hk, finite_power_polynomial_coeff, ite_eq_left hk]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      simp only [P, Q, finite_power_polynomial_coeff,
        ite_eq_left (hjk.trans hk), ite_eq_left (le_trans (Nat.sub_le k j) hk)]
    · rw [truncatePolynomial_coeff, finite_power_polynomial_coeff, ite_eq_right hk, ite_eq_right hk]
  have h := power_polynomial_mul t ht m f g P Q hf' hg'
  rw [he] at h
  apply (scalarLittleO_iff_isLittleO l _ _).mpr
  simpa only [finite_power_polynomial_eval, AsymptoticPartialSum] using h

/-- Division through every finite order, after a nonzero constant has been
exposed by factoring the leading scale. -/
theorem power_polynomial_division {l : Filter X} (t : X → K) (ht : Tendsto t l (𝓝 0))
    (m : ℕ) (f g : X → K) (P Q : Polynomial K) (hq : Q.coeff 0 ≠ 0)
    (hf : (fun x => f x - P.eval (t x)) =o[l] (fun x => t x^m))
    (hg : (fun x => g x - Q.eval (t x)) =o[l] (fun x => t x^m)) :
    (∀ᶠ x in l, g x ≠ 0) ∧
    (fun x => f x / g x - (QuotientPolynomial m P Q).eval (t x))
      =o[l] (fun x => t x^m) := by
  have hr : Tendsto (fun x => g x - Q.eval (t x)) l (𝓝 0) :=
    (isLittleO_one_iff K).mp (hg.trans_isBigO ((ht.pow m).isBigO_one K))
  have hp : Tendsto (fun x => Q.eval (t x)) l (𝓝 (Q.coeff 0)) := by
    simpa only [Function.comp_def, coeff_zero_eq_eval_zero] using (Q.differentiable.continuous.tendsto 0).comp ht
  have hg0 : Tendsto g l (𝓝 (Q.coeff 0)) := by
    simpa only [zero_add, sub_add_cancel] using hr.add hp
  have hgnz := hg0.eventually_ne hq
  refine ⟨hgnz, ?_⟩
  have hS := polynomial_eval_bounded ht (QuotientPolynomial m P Q)
  have hinv := (hg0.inv₀ hq).isBigO_one K
  have hpoly := (polynomial_eval_vanishing ht (P - Q*QuotientPolynomial m P Q)
    (m+1) (quotientPolynomial_dvd_remainder m P Q hq)).trans_isLittleO
      ((isLittleO_pow_pow (Nat.lt_succ_self m)).comp_tendsto ht)
  have hprod := hS.mul_isLittleO hg
  simp only [one_mul] at hprod
  have hout := ((hf.sub hprod).add hpoly).mul_isBigO hinv
  simp only [mul_one] at hout
  apply hout.congr' _ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hgnz] with x hx
  simp only [eval_sub, eval_mul]
  field_simp
  ring

end Power

section FiniteComposition
variable {X : Type u} {K : Type v} {L : Type w}
  [RCLike K] [RCLike L] [NormedAlgebra K L]

open private map_isBigO polynomial_eval_sub_isBigO from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.Composition

/-- Finite substitution and truncation, with an explicit inner O(t) bound.
Real and complex approaches and compatible real/complex scalar domains are
included. The actual outer value handles inner zeros, at every finite order. -/
theorem power_polynomial_composition {l : Filter X} (t : X → K)
    (ht : Tendsto t l (𝓝 0)) (D : Set K) (m : ℕ) (u : X → K) (b : K)
    (P : Polynomial K) (Q : Polynomial L) (F : K → L)
    (hP : P.coeff 0 = 0) (hu : (fun x => u x - b) =O[l] t)
    (hi : (fun x => u x - b - P.eval (t x)) =o[l] (fun x => t x^m))
    (hF : (fun z => F (b+z) - Q.eval (algebraMap K L z))
      =o[𝓝[D \ {0}] 0] (fun z => z^m))
    (hF0 : F b = Q.eval 0) (hD : ∀ᶠ x in l, u x - b ∈ insert 0 D) :
    (fun x => F (u x) - (CompositionPolynomial m P Q).eval (algebraMap K L (t x)))
      =o[l] (fun x => t x^m) := by
  have hv : Tendsto (fun x => u x - b) l (𝓝 0) := hu.trans_tendsto ht
  have hp : Tendsto (fun x => P.eval (t x)) l (𝓝 0) := by
    simpa only [Function.comp_def, ← coeff_zero_eq_eval_zero, hP] using (P.differentiable.continuous.tendsto 0).comp ht
  have hvm := (map_isBigO (L := L) (fun x => u x-b)).trans_tendsto hv
  have hpm := (map_isBigO (L := L) (fun x => P.eval (t x))).trans_tendsto hp
  have hout := compose_remainder l D t (fun x => u x-b)
    (fun z => F (b+z) - Q.eval (algebraMap K L z)) m ht hu hD
    (by simpa using sub_eq_zero.mpr hF0) hF
  have hmap := (map_isBigO (L := L) (fun x => u x-b-P.eval (t x))).trans_isLittleO hi
  have hreplace := (polynomial_eval_sub_isBigO Q _ _ hvm hpm).trans_isLittleO
    (by simpa only [map_sub] using hmap)
  have htm := (map_isBigO (L := L) t).trans_tendsto ht
  have htr := (polynomial_eval_vanishing htm
    (Q.comp (P.map (algebraMap K L)) - CompositionPolynomial m P Q) (m+1)
    (truncatePolynomial_dvd_remainder m _)).trans_isLittleO
      ((isLittleO_pow_pow (Nat.lt_succ_self m)).comp_tendsto htm)
  have hcast : (fun x => (algebraMap K L (t x))^m) =O[l] (fun x => t x^m) := by
    simpa only [map_pow] using map_isBigO (L := L) (fun x => t x^m)
  have hh := (hout.add hreplace).add (htr.trans_isBigO hcast)
  convert hh using 1
  funext x
  have hb : b + (u x - b) = u x := by abel
  simp only [eval_sub, eval_comp, eval_map_apply, hb]
  ring

end FiniteComposition
end SingleVariableAnalysis
