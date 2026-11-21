import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.OAlgebra
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.TaylorPolynomial
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.GeomSum

/-!
K03.06.composition, paper.tex:2839–2855. Finite composition and division,
with separate Peano and next-order big-O remainder statements.

The approach filter is any filter of real increments refining the neighborhood
of zero. It therefore includes the source punctured approach and all restrictions
to compatible domains. RCLike generality includes both canonical real/complex scalar
interfaces. A compatible normed scalar tower also covers a real inner function
and complex-valued outer expansion. The outer function requires no derivatives.
Its relative punctured error is extended to zero using its actual value there,
so no eventual avoidance of inner zeros is imposed.

The finite truncation, reciprocal and quotient polynomials are explicit. Errors
are compared with the real function h ↦ h^n; its norm equals that of h^n embedded
in either scalar field. This is the source inequality meaning of O/o, as identified
by the accepted upstream bridges. There are no infinite-series assumptions.
-/

noncomputable section
namespace SingleVariableAnalysis
open Polynomial Filter Asymptotics
open scoped Topology
universe u v
variable {K : Type u} [RCLike K]

/-- Keep precisely the coefficients of degrees zero through n. -/
def TruncatePolynomial (n : ℕ) (p : Polynomial K) : Polynomial K :=
  ∑ k ∈ Finset.range (n+1), monomial k (p.coeff k)

@[simp] theorem truncatePolynomial_coeff (n : ℕ) (p : Polynomial K) (k : ℕ) :
    (TruncatePolynomial n p).coeff k = if k ≤ n then p.coeff k else 0 := by
  simp [TruncatePolynomial, coeff_monomial, Finset.mem_range]

theorem truncatePolynomial_degree_le (n : ℕ) (p : Polynomial K) :
    (TruncatePolynomial n p).degree ≤ (n : WithBot ℕ) := by
  apply degree_le_of_natDegree_le
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [not_le.mpr hk]

theorem truncatePolynomial_dvd_remainder (n : ℕ) (p : Polynomial K) :
    X ^ (n+1) ∣ p - TruncatePolynomial n p := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  simp [Nat.lt_succ_iff.mp hk]

private theorem realCast_tendsto {l : Filter ℝ} (hl : l ≤ 𝓝 0) :
    Tendsto (algebraMap ℝ K) l (𝓝 0) := by
  simpa using (RCLike.ofRealCLM : ℝ →L[ℝ] K).continuous.continuousAt.tendsto.mono_left hl

private theorem polynomial_bounded {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    (p : Polynomial K) : (fun h => RealPolynomialEval p h) =O[l] (fun _ => (1 : K)) := by
  exact (p.differentiable.continuous.tendsto 0 |>.comp (realCast_tendsto hl)).isBigO_one K

private theorem polynomial_zero_isBigO {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    (p : Polynomial K) (hp : p.coeff 0 = 0) :
    (fun h => RealPolynomialEval p h) =O[l] (algebraMap ℝ K) := by
  obtain ⟨q, rfl⟩ := X_dvd_iff.mpr hp
  simpa [RealPolynomialEval] using (isBigO_refl (algebraMap ℝ K) l).mul
    (polynomial_bounded hl q)

private theorem polynomial_vanishing_isBigO {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    (p : Polynomial K) (m : ℕ) (hp : X ^ m ∣ p) :
    (fun h => RealPolynomialEval p h) =O[l] (fun h => (algebraMap ℝ K h)^m) := by
  obtain ⟨q, rfl⟩ := hp
  simpa [RealPolynomialEval] using
    (isBigO_refl (fun h => (algebraMap ℝ K h)^m) l).mul (polynomial_bounded hl q)

private theorem power_isBigO_linear {l : Filter ℝ} (hl : l ≤ 𝓝 0) {m : ℕ}
    (hm : 1 ≤ m) :
    (fun h => (algebraMap ℝ K h)^m) =O[l] (algebraMap ℝ K) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  simpa [pow_add, mul_comm] using
    (isBigO_refl (algebraMap ℝ K) l).mul ((realCast_tendsto hl |>.pow k).isBigO_one K)

private theorem polynomial_eval_sub_isBigO {α : Type*} {l : Filter α}
    (p : Polynomial K) (v w : α → K)
    (hv : Tendsto v l (𝓝 0)) (hw : Tendsto w l (𝓝 0)) :
    (fun h => p.eval (v h) - p.eval (w h)) =O[l] (fun h => v h - w h) := by
  exact (p.hasStrictDerivAt 0).hasStrictFDerivAt.isBigO_sub.comp_tendsto (hv.prodMk_nhds hw)

private theorem cast_power_isBigO_real {l : Filter ℝ} (m : ℕ) :
    (fun h => (algebraMap ℝ K h)^m) =O[l] (fun h : ℝ => h^m) := by
  apply IsBigO.of_bound 1
  exact Filter.Eventually.of_forall fun h => by simp [norm_pow]

private theorem polynomial_vanishing_isBigO_real {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    (p : Polynomial K) (m : ℕ) (hp : X ^ m ∣ p) :
    (fun h => RealPolynomialEval p h) =O[l] (fun h : ℝ => h^m) :=
  (polynomial_vanishing_isBigO hl p m hp).trans (cast_power_isBigO_real m)

private theorem polynomial_zero_isBigO_real {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    (p : Polynomial K) (hp : p.coeff 0 = 0) :
    (fun h => RealPolynomialEval p h) =O[l] (fun h : ℝ => h) := by
  have hc : (algebraMap ℝ K) =O[l] (fun h : ℝ => h) := by
    simpa using cast_power_isBigO_real (K := K) (l := l) 1
  exact (polynomial_zero_isBigO hl p hp).trans hc

private theorem real_power_isBigO_linear {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    {m : ℕ} (hm : 1 ≤ m) : (fun h : ℝ => h^m) =O[l] (fun h : ℝ => h) := by
  simpa using! (power_isBigO_linear (K := ℝ) hl hm)

private theorem real_higher_power_isLittleO {l : Filter ℝ} (hl : l ≤ 𝓝 0) (m : ℕ) :
    (fun h : ℝ => h^(m+1)) =o[l] (fun h : ℝ => h^m) :=
  (isLittleO_pow_pow (Nat.lt_succ_self m)).mono hl

variable {L : Type v} [RCLike L] [NormedAlgebra K L] [IsScalarTower ℝ K L]

/-- Substitute the inner polynomial and discard all terms above the stated order. -/
def CompositionPolynomial (n : ℕ) (P : Polynomial K) (Q : Polynomial L) : Polynomial L :=
  TruncatePolynomial n (Q.comp (P.map (algebraMap K L)))

omit [IsScalarTower ℝ K L] in
private theorem map_isBigO {α : Type*} {l : Filter α} (v : α → K) :
    (fun h => algebraMap K L (v h)) =O[l] v := by
  apply IsBigO.of_bound 1
  exact Filter.Eventually.of_forall fun h => by simp

private theorem inner_isBigO {l : Filter ℝ} (hl : l ≤ 𝓝 0) (n : ℕ) (hn : 1 ≤ n)
    (u : ℝ → K) (b : K) (P : Polynomial K) (hP : P.coeff 0 = 0)
    (hi : (fun h => u h - b - RealPolynomialEval P h) =O[l] (fun h : ℝ => h^n)) :
    (fun h => u h - b) =O[l] (fun h : ℝ => h) := by
  have hr := hi.trans (real_power_isBigO_linear hl hn)
  have hp := polynomial_zero_isBigO_real hl P hP
  exact (hr.add hp).congr_left (fun h => sub_add_cancel _ _)

/-- Finite composition with Peano errors, on any compatible scalar domain.
The arbitrary filter approaching zero includes relative, one-sided, and two-sided real approaches.
The inner increment is allowed to be zero arbitrarily often. -/
theorem finite_composition_littleO {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    (D : Set K) (n : ℕ) (hn : 1 ≤ n) (u : ℝ → K) (b : K)
    (P : Polynomial K) (Q : Polynomial L) (F : K → L)
    (hP : P.coeff 0 = 0) (_hQ : Q.degree ≤ (n : WithBot ℕ))
    (hi : (fun h => u h - b - RealPolynomialEval P h) =o[l] (fun h : ℝ => h^n))
    (hF : (fun z => F (b+z) - Q.eval (algebraMap K L z)) =o[𝓝[D \ {0}] 0]
      (fun z => z^n))
    (hF0 : F b = Q.eval 0)
    (hD : ∀ᶠ h in l, u h - b ∈ insert 0 D) :
    (fun h => F (u h) - RealPolynomialEval (CompositionPolynomial n P Q) h)
      =o[l] (fun h : ℝ => h^n) := by
  have hvO := inner_isBigO hl n hn u b P hP hi.isBigO
  have hv : Tendsto (fun h => u h-b) l (𝓝 0) := hvO.trans_tendsto (tendsto_id.mono_left hl)
  have hp : Tendsto (RealPolynomialEval P) l (𝓝 0) :=
    (polynomial_zero_isBigO_real hl P hP).trans_tendsto (tendsto_id.mono_left hl)
  have hvm : Tendsto (fun h => algebraMap K L (u h-b)) l (𝓝 0) :=
    (map_isBigO (L := L) _).trans_tendsto hv
  have hpm : Tendsto (fun h => algebraMap K L (RealPolynomialEval P h)) l (𝓝 0) :=
    (map_isBigO (L := L) _).trans_tendsto hp
  have hF' := hF.insert (by simpa using sub_eq_zero.mpr hF0)
  have hsub : insert 0 (D \ {0}) = insert 0 D := by ext z; simp
  rw [hsub] at hF'
  have hout := (hF'.comp_tendsto (tendsto_nhdsWithin_iff.mpr ⟨hv, hD⟩)).trans_isBigO
    (hvO.pow n)
  have hmap := (map_isBigO (L := L) (fun h => u h-b-RealPolynomialEval P h)).trans_isLittleO hi
  have hreplace := (polynomial_eval_sub_isBigO Q _ _ hvm hpm).trans_isLittleO
    (by simpa only [map_sub] using hmap)
  have htr := (polynomial_vanishing_isBigO_real hl
    (Q.comp (P.map (algebraMap K L)) - CompositionPolynomial n P Q) (n+1)
    (truncatePolynomial_dvd_remainder n _)).trans_isLittleO (real_higher_power_isLittleO hl n)
  have hsum := (hout.add hreplace).add htr
  convert hsum using 1
  funext h
  have hb : b + (u h - b) = u h := by abel
  simp only [Function.comp_apply, RealPolynomialEval, eval_sub, eval_comp,
    IsScalarTower.algebraMap_apply ℝ K L, eval_map_apply, hb]
  ring

/-- Next-order big-O errors remain next-order after finite substitution. -/
theorem finite_composition_bigO {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    (D : Set K) (n : ℕ) (hn : 1 ≤ n) (u : ℝ → K) (b : K)
    (P : Polynomial K) (Q : Polynomial L) (F : K → L)
    (hP : P.coeff 0 = 0) (_hQ : Q.degree ≤ (n : WithBot ℕ))
    (hi : (fun h => u h - b - RealPolynomialEval P h) =O[l] (fun h : ℝ => h^(n+1)))
    (hF : (fun z => F (b+z) - Q.eval (algebraMap K L z)) =O[𝓝[D \ {0}] 0]
      (fun z => z^(n+1)))
    (hF0 : F b = Q.eval 0)
    (hD : ∀ᶠ h in l, u h - b ∈ insert 0 D) :
    (fun h => F (u h) - RealPolynomialEval (CompositionPolynomial n P Q) h)
      =O[l] (fun h : ℝ => h^(n+1)) := by
  have hvO := inner_isBigO hl (n+1) (by omega) u b P hP hi
  have hv : Tendsto (fun h => u h-b) l (𝓝 0) := hvO.trans_tendsto (tendsto_id.mono_left hl)
  have hp : Tendsto (RealPolynomialEval P) l (𝓝 0) :=
    (polynomial_zero_isBigO_real hl P hP).trans_tendsto (tendsto_id.mono_left hl)
  have hvm : Tendsto (fun h => algebraMap K L (u h-b)) l (𝓝 0) :=
    (map_isBigO (L := L) _).trans_tendsto hv
  have hpm : Tendsto (fun h => algebraMap K L (RealPolynomialEval P h)) l (𝓝 0) :=
    (map_isBigO (L := L) _).trans_tendsto hp
  obtain ⟨C, hC⟩ := isBigO_iff_isBigOWith.mp hF
  have hF' := (hC.insert (by simp [hF0])).isBigO
  have hsub : insert 0 (D \ {0}) = insert 0 D := by ext z; simp
  rw [hsub] at hF'
  have hout := (hF'.comp_tendsto (tendsto_nhdsWithin_iff.mpr ⟨hv, hD⟩)).trans
    (hvO.pow (n+1))
  have hmap := (map_isBigO (L := L) (fun h => u h-b-RealPolynomialEval P h)).trans hi
  have hreplace := (polynomial_eval_sub_isBigO Q _ _ hvm hpm).trans
    (by simpa only [map_sub] using hmap)
  have htr := (polynomial_vanishing_isBigO_real hl
    (Q.comp (P.map (algebraMap K L)) - CompositionPolynomial n P Q) (n+1)
    (truncatePolynomial_dvd_remainder n _))
  have hsum := (hout.add hreplace).add htr
  convert hsum using 1
  funext h
  have hb : b + (u h - b) = u h := by abel
  simp only [Function.comp_apply, RealPolynomialEval, eval_sub, eval_comp,
    IsScalarTower.algebraMap_apply ℝ K L, eval_map_apply, hb]
  ring

/-- The finite geometric reciprocal, before discarding high degrees. -/
def ReciprocalPolynomial (n : ℕ) (Q : Polynomial K) : Polynomial K :=
  C (Q.coeff 0)⁻¹ * ∑ j ∈ Finset.range (n+1), (1 - C (Q.coeff 0)⁻¹ * Q)^j

/-- Polynomial division of finite expansions, through degree n. -/
def QuotientPolynomial (n : ℕ) (P Q : Polynomial K) : Polynomial K :=
  TruncatePolynomial n (P * ReciprocalPolynomial n Q)

theorem reciprocalPolynomial_mul (n : ℕ) (Q : Polynomial K) :
    Q * ReciprocalPolynomial n Q = 1 - (1 - C (Q.coeff 0)⁻¹ * Q)^(n+1) := by
  calc
    Q * ReciprocalPolynomial n Q =
        (∑ j ∈ Finset.range (n+1), (1 - C (Q.coeff 0)⁻¹ * Q)^j) *
          (C (Q.coeff 0)⁻¹ * Q) := by unfold ReciprocalPolynomial; ring
    _ = _ := by simpa only [sub_sub_cancel] using
      geom_sum_mul_neg (1 - C (Q.coeff 0)⁻¹ * Q) (n+1)

theorem quotientPolynomial_dvd_remainder (n : ℕ) (P Q : Polynomial K)
    (hQ : Q.coeff 0 ≠ 0) : X^(n+1) ∣ P - Q * QuotientPolynomial n P Q := by
  have hx : X ∣ 1 - C (Q.coeff 0)⁻¹ * Q := X_dvd_iff.mpr (by simp [hQ])
  have hr : X^(n+1) ∣ 1 - Q * ReciprocalPolynomial n Q := by
    rw [reciprocalPolynomial_mul, sub_sub_cancel]
    exact pow_dvd_pow_of_dvd hx (n+1)
  have ht := truncatePolynomial_dvd_remainder n (P * ReciprocalPolynomial n Q)
  have h₁ : X^(n+1) ∣ P * (1-Q * ReciprocalPolynomial n Q) := dvd_mul_of_dvd_right hr P
  have h₂ : X^(n+1) ∣ Q * (P * ReciprocalPolynomial n Q - QuotientPolynomial n P Q) :=
    dvd_mul_of_dvd_right ht Q
  convert dvd_add h₁ h₂ using 1
  ring

private theorem expansion_tendsto {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    (n : ℕ) (hn : 1 ≤ n) (f : ℝ → K) (P : Polynomial K)
    (hf : (fun h => f h - RealPolynomialEval P h) =O[l] (fun h : ℝ => h^n)) :
    Tendsto f l (𝓝 (P.coeff 0)) := by
  have hr : Tendsto (fun h => f h-RealPolynomialEval P h) l (𝓝 0) :=
    (hf.trans (real_power_isBigO_linear hl hn)).trans_tendsto (tendsto_id.mono_left hl)
  have hp : Tendsto (RealPolynomialEval P) l (𝓝 (P.coeff 0)) := by
    rw [coeff_zero_eq_eval_zero]
    exact (P.differentiable.continuous.tendsto 0).comp (realCast_tendsto (K := K) hl)
  simpa only [zero_add, sub_add_cancel] using hr.add hp

/-- Finite division with Peano errors; the denominator is proved eventually nonzero. -/
theorem finite_division_littleO {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    (n : ℕ) (hn : 1 ≤ n) (f g : ℝ → K) (P Q : Polynomial K)
    (hq : Q.coeff 0 ≠ 0)
    (hf : (fun h => f h - RealPolynomialEval P h) =o[l] (fun h : ℝ => h^n))
    (hg : (fun h => g h - RealPolynomialEval Q h) =o[l] (fun h : ℝ => h^n)) :
    (∀ᶠ h in l, g h ≠ 0) ∧
      (fun h => f h / g h - RealPolynomialEval (QuotientPolynomial n P Q) h)
        =o[l] (fun h : ℝ => h^n) := by
  have hg0 := expansion_tendsto hl n hn g Q hg.isBigO
  have hgnz := hg0.eventually_ne hq
  refine ⟨hgnz, ?_⟩
  have hS : (fun h => RealPolynomialEval (QuotientPolynomial n P Q) h)
      =O[l] (fun _ => (1 : ℝ)) :=
    (polynomial_bounded hl _).trans (isBigO_const_one ℝ (1 : K) l)
  have hinv : (fun h => (g h)⁻¹) =O[l] (fun _ => (1 : ℝ)) :=
    (hg0.inv₀ hq).isBigO_one ℝ
  have hpoly := (polynomial_vanishing_isBigO_real hl
    (P-Q*QuotientPolynomial n P Q) (n+1) (quotientPolynomial_dvd_remainder n P Q hq)).trans_isLittleO
      (real_higher_power_isLittleO hl n)
  have hprod := hS.mul_isLittleO hg
  simp only [one_mul] at hprod
  have hnum := (hf.sub hprod).add hpoly
  have hout := hnum.mul_isBigO hinv
  simp only [mul_one] at hout
  apply hout.congr' _ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [hgnz] with h hne
  simp only [RealPolynomialEval, eval_sub, eval_mul]
  field_simp
  ring

/-- Finite division preserves next-order big-O input errors. -/
theorem finite_division_bigO {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    (n : ℕ) (hn : 1 ≤ n) (f g : ℝ → K) (P Q : Polynomial K)
    (hq : Q.coeff 0 ≠ 0)
    (hf : (fun h => f h - RealPolynomialEval P h) =O[l] (fun h : ℝ => h^(n+1)))
    (hg : (fun h => g h - RealPolynomialEval Q h) =O[l] (fun h : ℝ => h^(n+1))) :
    (∀ᶠ h in l, g h ≠ 0) ∧
      (fun h => f h / g h - RealPolynomialEval (QuotientPolynomial n P Q) h)
        =O[l] (fun h : ℝ => h^(n+1)) := by
  have hg0 := expansion_tendsto hl (n+1) (by omega) g Q hg
  have hgnz := hg0.eventually_ne hq
  refine ⟨hgnz, ?_⟩
  have hS : (fun h => RealPolynomialEval (QuotientPolynomial n P Q) h)
      =O[l] (fun _ => (1 : ℝ)) :=
    (polynomial_bounded hl _).trans (isBigO_const_one ℝ (1 : K) l)
  have hinv : (fun h => (g h)⁻¹) =O[l] (fun _ => (1 : ℝ)) :=
    (hg0.inv₀ hq).isBigO_one ℝ
  have hpoly := (polynomial_vanishing_isBigO_real hl
    (P-Q*QuotientPolynomial n P Q) (n+1) (quotientPolynomial_dvd_remainder n P Q hq))
  have hprod := hS.mul hg
  simp only [one_mul] at hprod
  have hnum := (hf.sub hprod).add hpoly
  have hout := hnum.mul hinv
  simp only [mul_one] at hout
  apply hout.congr' _ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [hgnz] with h hne
  simp only [RealPolynomialEval, eval_sub, eval_mul]
  field_simp
  ring

omit [IsScalarTower ℝ K L] in
theorem compositionPolynomial_degree_le (n : ℕ) (P : Polynomial K) (Q : Polynomial L) :
    (CompositionPolynomial n P Q).degree ≤ (n : WithBot ℕ) :=
  truncatePolynomial_degree_le n _

theorem quotientPolynomial_degree_le (n : ℕ) (P Q : Polynomial K) :
    (QuotientPolynomial n P Q).degree ≤ (n : WithBot ℕ) :=
  truncatePolynomial_degree_le n _

end SingleVariableAnalysis
