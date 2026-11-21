import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TangentAddition
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.TorusCubicBiholomorphism
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.DivisorSumConstraint
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Tangent intersections and doubling are proved from analytic elliptic divisors.
The cubic group law is not used. The triple pole fixes total intersection degree,
and the divisor sum fixes the residual torus class, even when it coincides with
both prescribed zeros. -/
noncomputable section
open Set Filter
open scoped Topology Classical BigOperators
namespace D12Complex.TangentAddition
open TorusSurface CubicFiniteCharts
open Ch22.WeierstrassSeries (periodPair)
open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)
open Specs.D12Complex.Ch22.WeierstrassEquations (g₂ g₃)
open TorusCubicLocalMap (phi phi_finite phi_zero)

/-- Pulling an affine line back by the finite Weierstrass chart. -/
def linePullback (L : PeriodPair) (m b : ℂ) (t : ℂ) : ℂ :=
  deriv L.weierstrassP t - m * L.weierstrassP t - b

lemma line_meromorphic (L : PeriodPair) (m b : ℂ) :
    Meromorphic (linePullback L m b) := by
  intro a
  exact ((L.meromorphic_weierstrassP.deriv a).sub
    ((analyticAt_const (v := m)).meromorphicAt.mul (L.meromorphic_weierstrassP a))).sub
      (analyticAt_const (v := b)).meromorphicAt

lemma line_analytic (L : PeriodPair) (m b : ℂ) {a : ℂ} (ha : a ∉ L.lattice) :
    AnalyticAt ℂ (linePullback L m b) a := by
  have hp := L.analyticOnNhd_weierstrassP a ha
  exact (hp.deriv.sub (analyticAt_const.mul hp)).sub analyticAt_const

lemma line_periodic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (m b : ℂ) : Periodic ω₁ ω₂ (linePullback (periodPair h₁ h₂) m b) := by
  intro z l hl
  let L := periodPair h₁ h₂
  change deriv L.weierstrassP (z + l) - m * L.weierstrassP (z + l) - b =
    deriv L.weierstrassP z - m * L.weierstrassP z - b
  rw [L.deriv_weierstrassP]
  rw [L.derivWeierstrassP_add_coe z ⟨l, hl⟩, L.weierstrassP_add_coe z ⟨l, hl⟩]

lemma line_pole_order (L : PeriodPair) (m b : ℂ) {a : ℂ} (ha : a ∈ L.lattice) :
    meromorphicOrderAt (linePullback L m b) a = (-3 : WithTop ℤ) := by
  have hp := L.order_weierstrassP a ha
  have hdp : meromorphicOrderAt (deriv L.weierstrassP) a = (-3 : WithTop ℤ) := by
    simpa using meromorphicOrderAt_deriv_eq_sub_one (f := L.weierstrassP)
      (n := -2) (by norm_num) hp
  have hm : (-2 : WithTop ℤ) ≤ meromorphicOrderAt (fun t => -m * L.weierstrassP t) a := by
    by_cases hm : m = 0
    · simp only [hm, neg_zero, zero_mul]
      exact le_trans (WithTop.coe_le_coe.mpr (by norm_num : (-2 : ℤ) ≤ 0))
        (analyticAt_const (𝕜 := ℂ) (x := a) (v := (0 : ℂ))).meromorphicOrderAt_nonneg
    · have hmo : meromorphicOrderAt (fun t => -m * L.weierstrassP t) a =
          meromorphicOrderAt L.weierstrassP a := by
        simpa only [smul_eq_mul] using
          (meromorphicOrderAt_fun_const_smul_eq_meromorphicOrderAt (f := L.weierstrassP)
            (x := a) (neg_ne_zero.mpr hm))
      rw [hmo, hp]
  have hmb : (-2 : WithTop ℤ) ≤ meromorphicOrderAt (fun t => -m * L.weierstrassP t - b) a := by
    have he := meromorphicOrderAt_add
      (f₁ := fun t => -m * L.weierstrassP t) (f₂ := fun _ => -b)
      ((analyticAt_const (v := -m)).meromorphicAt.mul (L.meromorphic_weierstrassP a))
      (analyticAt_const (v := -b)).meromorphicAt
    exact le_trans (le_min hm (le_trans (WithTop.coe_le_coe.mpr (by norm_num : (-2 : ℤ) ≤ 0))
      (analyticAt_const (𝕜 := ℂ) (x := a) (v := -b)).meromorphicOrderAt_nonneg)) he
  have hlt : meromorphicOrderAt (deriv L.weierstrassP) a <
      meromorphicOrderAt (fun t => -m * L.weierstrassP t - b) a := by
    rw [hdp]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num : (-3 : ℤ) < -2)) hmb
  have he := meromorphicOrderAt_add_eq_left_of_lt
    (f₁ := deriv L.weierstrassP) (f₂ := fun t => -m * L.weierstrassP t - b)
    (((analyticAt_const (v := -m)).meromorphicAt.mul (L.meromorphic_weierstrassP a)).sub
      (analyticAt_const (v := b)).meromorphicAt) hlt
  convert he.trans hdp using 1
  congr 1
  ext t
  simp only [linePullback, Pi.add_apply]
  ring

lemma line_order_finite (L : PeriodPair) (m b : ℂ) (a : ℂ) :
    meromorphicOrderAt (linePullback L m b) a ≠ ⊤ := by
  exact ((line_meromorphic L m b).meromorphicOn (s := univ)).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ 0) (mem_univ a)
    (by rw [line_pole_order L m b (zero_mem _)]; simp)

lemma order_at_least_two_of_double_zero {f : ℂ → ℂ} {a : ℂ}
    (ha : AnalyticAt ℂ f a) (hfin : meromorphicOrderAt f a ≠ ⊤)
    (hzero : f a = 0) (hdzero : deriv f a = 0) :
    2 ≤ (meromorphicOrderAt f a).untop₀.toNat := by
  have hder : (1 : ℕ∞) ≤ analyticOrderAt (deriv f) a := by
    exact Order.one_le_iff_ne_zero.mpr (ha.deriv.analyticOrderAt_ne_zero.mpr hdzero)
  have hord : (2 : ℕ∞) ≤ analyticOrderAt f a := by
    have he := ha.analyticOrderAt_deriv_add_one
    simp only [hzero, sub_zero] at he
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ analyticOrderAt (deriv f) a + 1 := add_le_add hder (le_refl 1)
      _ = analyticOrderAt f a := he
  rw [ha.meromorphicOrderAt_eq] at hfin ⊢
  cases he : analyticOrderAt f a with
  | top => simp [he] at hfin
  | coe n =>
    simp only [ENat.map_natCast, WithTop.untop₀_coe, Int.toNat_natCast]
    exact_mod_cast (show (2 : ℕ∞) ≤ (n : ℕ∞) by simpa [he] using hord)

lemma tangent_double_zero (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice)
    (hy : deriv L.weierstrassP z ≠ 0) :
    let m := (12 * L.weierstrassP z ^ 2 - L.g₂) / (2 * deriv L.weierstrassP z)
    let b := deriv L.weierstrassP z - m * L.weierstrassP z
    2 ≤ (meromorphicOrderAt (linePullback L m b) z).untop₀.toNat := by
  dsimp only
  let m := (12 * L.weierstrassP z ^ 2 - L.g₂) / (2 * deriv L.weierstrassP z)
  let b := deriv L.weierstrassP z - m * L.weierstrassP z
  have ha := L.analyticOnNhd_weierstrassP z hz
  apply order_at_least_two_of_double_zero (line_analytic L m b hz) (line_order_finite L m b z)
  · simp [linePullback, b]
  · have hd : HasDerivAt (linePullback L m b)
        (deriv (deriv L.weierstrassP) z - m * deriv L.weierstrassP z) z :=
      (ha.deriv.differentiableAt.hasDerivAt.sub
        (ha.differentiableAt.hasDerivAt.const_mul m)).sub_const b
    rw [hd.deriv, Ch22.WeierstrassEquations.second_equation_periodPair L hz]
    dsimp [m]
    field_simp
    ring

lemma zero_iff_order_nat_ne_zero {f : ℂ → ℂ} {a : ℂ}
    (ha : AnalyticAt ℂ f a) (hfin : meromorphicOrderAt f a ≠ ⊤) :
    (meromorphicOrderAt f a).untop₀.toNat ≠ 0 ↔ f a = 0 := by
  have hezero := ha.analyticOrderAt_ne_zero
  rw [ha.meromorphicOrderAt_eq] at hfin ⊢
  cases hn : analyticOrderAt f a with
  | top => simp [hn] at hfin
  | coe n =>
    rw [hn] at hezero
    simpa using hezero

lemma order_eq_nat_part {f : ℂ → ℂ} {a : ℂ}
    (ha : AnalyticAt ℂ f a) (hfin : meromorphicOrderAt f a ≠ ⊤) :
    meromorphicOrderAt f a = ((meromorphicOrderAt f a).untop₀.toNat : ℤ) := by
  rw [ha.meromorphicOrderAt_eq] at hfin ⊢
  cases hn : analyticOrderAt f a with
  | top => simp [hn] at hfin
  | coe n => simp

open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)
open Specs.D12Complex.Ch22.WeierstrassEquations (g₂)

lemma tangent_slope_canonical {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {z : ℂ} (hz : z ∉ lattice ω₁ ω₂) (hy : deriv (weierstrassP ω₁ ω₂) z ≠ 0) :
    (12 * weierstrassP ω₁ ω₂ z ^ 2 - g₂ ω₁ ω₂) /
        (2 * deriv (weierstrassP ω₁ ω₂) z) =
      deriv (deriv (weierstrassP ω₁ ω₂)) z / deriv (weierstrassP ω₁ ω₂) z := by
  rw [Ch22.WeierstrassEquations.second_equation ω₁ ω₂ h₁ h₂ z hz]
  field_simp
  ring

lemma affine_line_meromorphic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (m b : ℂ) :
    Meromorphic (fun t => deriv (weierstrassP ω₁ ω₂) t - m * weierstrassP ω₁ ω₂ t - b) := by
  exact line_meromorphic (periodPair h₁ h₂) m b

lemma affine_line_analytic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (m b : ℂ) {a : ℂ} (ha : a ∉ lattice ω₁ ω₂) :
    AnalyticAt ℂ (fun t => deriv (weierstrassP ω₁ ω₂) t - m * weierstrassP ω₁ ω₂ t - b) a := by
  exact line_analytic (periodPair h₁ h₂) m b ha

lemma affine_line_periodic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (m b : ℂ) :
    Periodic ω₁ ω₂ (fun t => deriv (weierstrassP ω₁ ω₂) t - m * weierstrassP ω₁ ω₂ t - b) := by
  exact line_periodic h₁ h₂ m b

lemma affine_line_pole_order {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (m b : ℂ) {a : ℂ} (ha : a ∈ lattice ω₁ ω₂) :
    meromorphicOrderAt
      (fun t => deriv (weierstrassP ω₁ ω₂) t - m * weierstrassP ω₁ ω₂ t - b) a =
        (-3 : WithTop ℤ) := by
  exact line_pole_order (periodPair h₁ h₂) m b ha

lemma affine_line_order_finite {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (m b a : ℂ) :
    meromorphicOrderAt
      (fun t => deriv (weierstrassP ω₁ ω₂) t - m * weierstrassP ω₁ ω₂ t - b) a ≠ ⊤ := by
  exact line_order_finite (periodPair h₁ h₂) m b a

lemma affine_tangent_double_zero {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {z : ℂ} (hz : z ∉ lattice ω₁ ω₂) (hy : deriv (weierstrassP ω₁ ω₂) z ≠ 0) :
    let m := (12 * weierstrassP ω₁ ω₂ z ^ 2 - g₂ ω₁ ω₂) /
      (2 * deriv (weierstrassP ω₁ ω₂) z)
    let b := deriv (weierstrassP ω₁ ω₂) z - m * weierstrassP ω₁ ω₂ z
    2 ≤ (meromorphicOrderAt
      (fun t => deriv (weierstrassP ω₁ ω₂) t - m * weierstrassP ω₁ ω₂ t - b) z).untop₀.toNat := by
  have ht := tangent_double_zero (periodPair h₁ h₂) hz hy
  dsimp only [linePullback] at ht
  rw [Ch22.WeierstrassEquations.periodPair_g₂] at ht
  exact ht


lemma tangent_slope_identity (x y g₂ : ℂ) (hy : y ≠ 0) :
    2 * y * ((12*x^2-g₂)/(2*y)) = 12*x^2-g₂ := by
  field_simp

lemma tangent_derivative_slope (x y g₂ : ℂ) :
    (12*x^2-g₂)/(2*y) = (6*x^2-g₂/2)/y := by
  ring

lemma tangent_factorization (g₂ g₃ x y m t : ℂ)
    (hcurve : y^2 = 4*x^3-g₂*x-g₃)
    (htangent : 2*y*m = 12*x^2-g₂) :
    4*t^3-g₂*t-g₃ - (y+m*(t-x))^2 =
      4*(t-x)^2*(t-(-2*x+m^2/4)) := by
  linear_combination -hcurve - (t-x)*htangent

lemma tangent_third_curve (g₂ g₃ x y m : ℂ)
    (hcurve : y^2 = 4*x^3-g₂*x-g₃)
    (htangent : 2*y*m = 12*x^2-g₂) :
    (y+m*((-2*x+m^2/4)-x))^2 =
      4*(-2*x+m^2/4)^3-g₂*(-2*x+m^2/4)-g₃ := by
  have h := tangent_factorization g₂ g₃ x y m (-2*x+m^2/4) hcurve htangent
  simpa using (sub_eq_zero.mp (by simpa using h)).symm

lemma tangent_reflected_curve (g₂ g₃ x y m : ℂ)
    (hcurve : y^2 = 4*x^3-g₂*x-g₃)
    (htangent : 2*y*m = 12*x^2-g₂) :
    (-y+m*(x-(-2*x+m^2/4)))^2 =
      4*(-2*x+m^2/4)^3-g₂*(-2*x+m^2/4)-g₃ := by
  have h := tangent_third_curve g₂ g₃ x y m hcurve htangent
  convert h using 1
  ring

lemma tangent_roots (g₂ g₃ x y m t : ℂ)
    (hcurve : y^2 = 4*x^3-g₂*x-g₃)
    (htangent : 2*y*m = 12*x^2-g₂) :
    4*t^3-g₂*t-g₃ = (y+m*(t-x))^2 ↔
      t = x ∨ t = -2*x+m^2/4 := by
  rw [← sub_eq_zero, tangent_factorization g₂ g₃ x y m t hcurve htangent]
  simp only [mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), sub_eq_zero]
  norm_num

lemma flex_iff (x m : ℂ) : -2*x+m^2/4 = x ↔ m^2 = 12*x := by
  constructor <;> intro h
  · linear_combination 4*h
  · linear_combination h/4

lemma tangent_flex_factorization (g₂ g₃ x y m t : ℂ)
    (hcurve : y^2 = 4*x^3-g₂*x-g₃)
    (htangent : 2*y*m = 12*x^2-g₂)
    (hflex : -2*x+m^2/4 = x) :
    4*t^3-g₂*t-g₃ - (y+m*(t-x))^2 = 4*(t-x)^3 := by
  rw [tangent_factorization g₂ g₃ x y m t hcurve htangent, hflex]
  ring

open Polynomial
lemma tangent_polynomial_factorization (g₂ g₃ x y m : ℂ)
    (hcurve : y^2 = 4*x^3-g₂*x-g₃)
    (htangent : 2*y*m = 12*x^2-g₂) :
    (4*X^3-C g₂*X-C g₃ - (C y+C m*(X-C x))^2 : Polynomial ℂ) =
      4*(X-C x)^2*(X-C (-2*x+m^2/4)) := by
  apply Polynomial.funext
  intro t
  simpa using tangent_factorization g₂ g₃ x y m t hcurve htangent

lemma tangent_polynomial_roots (g₂ g₃ x y m : ℂ)
    (hcurve : y^2 = 4*x^3-g₂*x-g₃)
    (htangent : 2*y*m = 12*x^2-g₂) :
    (4*X^3-C g₂*X-C g₃ - (C y+C m*(X-C x))^2 : Polynomial ℂ).roots =
      ({x} + {x} + {-2*x+m^2/4} : Multiset ℂ) := by
  classical
  rw [tangent_polynomial_factorization g₂ g₃ x y m hcurve htangent]
  have hfour : (4 : Polynomial ℂ) ≠ 0 := by norm_num
  rw [roots_mul (mul_ne_zero (mul_ne_zero hfour
    (pow_ne_zero _ (X_sub_C_ne_zero x))) (X_sub_C_ne_zero _))]
  rw [roots_mul (mul_ne_zero hfour (pow_ne_zero _ (X_sub_C_ne_zero x)))]
  have hr : (4 : Polynomial ℂ).roots = 0 := by
    simpa only [C_ofNat] using roots_C (4 : ℂ)
  simp only [hr, Multiset.zero_add, roots_pow, roots_X_sub_C, two_nsmul]

lemma tangent_polynomial_rootMultiplicity (g₂ g₃ x y m : ℂ)
    (hcurve : y^2 = 4*x^3-g₂*x-g₃)
    (htangent : 2*y*m = 12*x^2-g₂) :
    (4*X^3-C g₂*X-C g₃ - (C y+C m*(X-C x))^2 : Polynomial ℂ).rootMultiplicity x =
      if -2*x+m^2/4 = x then 3 else 2 := by
  classical
  rw [← count_roots, tangent_polynomial_roots g₂ g₃ x y m hcurve htangent]
  simp only [Multiset.count_add, Multiset.count_singleton, ite_true, Nat.reduceAdd]
  by_cases hu : -2*x+m^2/4 = x
  · simp only [hu, ite_true]
  · have hu' : x ≠ -2*x+m^2/4 := Ne.symm hu
    simp only [hu, hu', ite_false]



lemma affinePoint_injective {x y x' y' : ℂ}
    (h : affinePoint x y = affinePoint x' y') : x=x' ∧ y=y' := by
  exact ⟨by simpa only [finiteX_affinePoint] using congrArg finiteX h,
    by simpa only [finiteY_affinePoint] using congrArg finiteY h⟩

lemma phi_neg_finite {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂/ω₁).im)
    {z : ℂ} (hz : z ∉ TorusSurface.lattice ω₁ ω₂) :
    phi ω₁ ω₂ (-projection ω₁ ω₂ z) =
      affinePoint (weierstrassP ω₁ ω₂ z) (-deriv (weierstrassP ω₁ ω₂) z) := by
  rw [← map_neg]
  have hnz : -z ∉ TorusSurface.lattice ω₁ ω₂ := by simpa using hz
  rw [phi_finite h₁ h₂ hnz]
  have he : weierstrassP ω₁ ω₂ (-z) = weierstrassP ω₁ ω₂ z :=
    (Ch22.WeierstrassSeries.periodPair h₁ h₂).weierstrassP_neg z
  change affinePoint (weierstrassP ω₁ ω₂ (-z)) (deriv (weierstrassP ω₁ ω₂) (-z)) = _
  rw [he, TorusCubicBiholomorphism.Fibres.deriv_neg h₁ h₂ z]

lemma phi_neg_finite_of_coordinates {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂/ω₁).im) {t : Torus ω₁ ω₂} {x y : ℂ}
    (h : phi ω₁ ω₂ t = affinePoint x y) :
    phi ω₁ ω₂ (-t) = affinePoint x (-y) := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (TorusSurface.lattice ω₁ ω₂).toAddSubgroup t
  change phi ω₁ ω₂ (projection ω₁ ω₂ z) = affinePoint x y at h
  change phi ω₁ ω₂ (-projection ω₁ ω₂ z) = affinePoint x (-y)
  have hz : z ∉ TorusSurface.lattice ω₁ ω₂ := by
    intro hz
    have hp0 : projection ω₁ ω₂ z = 0 := (Ch22.HalfPeriodValues.projection_zero_iff z).mpr hz
    rw [hp0, phi_zero h₁ h₂] at h
    exact CubicInfinityChart.O_not_mem_finitePatch
      (h.symm ▸ affinePoint_mem_patch x y)
  have hxy := affinePoint_injective ((phi_finite h₁ h₂ hz).symm.trans h)
  change weierstrassP ω₁ ω₂ z = x ∧ deriv (weierstrassP ω₁ ω₂) z = y at hxy
  rw [phi_neg_finite h₁ h₂ hz, hxy.1, hxy.2]

lemma phi_neg_on_finite {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂/ω₁).im) {t : Torus ω₁ ω₂}
    (ht : t ≠ 0) :
    phi ω₁ ω₂ (-t) =
      affinePoint (finiteX (phi ω₁ ω₂ t)) (-finiteY (phi ω₁ ω₂ t)) := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (TorusSurface.lattice ω₁ ω₂).toAddSubgroup t
  change projection ω₁ ω₂ z ≠ 0 at ht
  change phi ω₁ ω₂ (-projection ω₁ ω₂ z) =
    affinePoint (finiteX (phi ω₁ ω₂ (projection ω₁ ω₂ z)))
      (-finiteY (phi ω₁ ω₂ (projection ω₁ ω₂ z)))
  have hz : z ∉ TorusSurface.lattice ω₁ ω₂ := by
    intro hz
    exact ht ((Ch22.HalfPeriodValues.projection_zero_iff z).mpr hz)
  rw [phi_finite h₁ h₂ hz]
  simp only [finiteX_affinePoint, finiteY_affinePoint]
  exact phi_neg_finite h₁ h₂ hz


/-- A scalar elliptic function with one triple pole has zero divisor of degree three,
and its zero classes sum to zero. -/
lemma triple_pole_divisor {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (F : ℂ → RiemannSphere)
    (hF : ScalarMeromorphicOn univ F) (hp : Periodic ω₁ ω₂ F)
    (hpol : ∀ a : ℂ, a ∈ lattice ω₁ ω₂ →
      meromorphicOrderAt (scalarFinitePart F) a = ((-3 : ℤ) : WithTop ℤ))
    (hreg : ∀ a : ℂ, a ∉ lattice ω₁ ω₂ →
      0 ≤ meromorphicOrderAt (scalarFinitePart F) a) :
    ∃ Z : Torus ω₁ ω₂ →₀ ℕ,
      (∀ a : ℂ, Z (projection ω₁ ω₂ a) =
        (meromorphicOrderAt (scalarFinitePart F) a).untop₀.toNat) ∧
      Z.sum (fun _ n => n) = 3 ∧ Z.sum (fun q n => n • q) = 0 := by
  classical
  have hn : ¬ ∃ c : ℂ, ∀ z, F z = sphereFinite c := by
    rintro ⟨c, hc⟩
    have hzero := hpol 0 (zero_mem _)
    have he : scalarFinitePart F = fun _ => c := by
      funext z
      simp [scalarFinitePart, hc z, finiteCoordinate_sphereFinite]
    rw [he] at hzero
    have hnonneg := (show AnalyticAt ℂ (fun _ : ℂ => c) 0 from analyticAt_const).meromorphicOrderAt_nonneg
    rw [hzero] at hnonneg
    have hbad : (0 : ℤ) ≤ -3 := by exact_mod_cast hnonneg
    omega
  obtain ⟨N, hN, Z, P, hZP, hZ, hP, hV⟩ :=
    DivisorDegree.divisor_degree ω₁ ω₂ h₁ h₂ F hF hp hn
  have hPeq : P = Finsupp.single 0 3 := by
    ext q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup q
    change P (projection ω₁ ω₂ a) =
      (Finsupp.single 0 3) (projection ω₁ ω₂ a)
    rw [(hZP a).2.2]
    by_cases ha : a ∈ lattice ω₁ ω₂
    · have hπ : projection ω₁ ω₂ a = 0 := (QuotientAddGroup.eq_zero_iff _).mpr ha
      simp [hpol a ha, hπ]
    · have hπ : projection ω₁ ω₂ a ≠ 0 := by
        intro h
        exact ha ((QuotientAddGroup.eq_zero_iff _).mp h)
      have he := WithTop.coe_untop₀_of_ne_top (hZP a).1
      have hi : 0 ≤ (meromorphicOrderAt (scalarFinitePart F) a).untop₀ := by
        exact_mod_cast (he ▸ hreg a ha)
      simp [hπ, Int.toNat_of_nonpos (neg_nonpos.mpr hi)]
  have hN3 : N = 3 := by
    rw [hPeq] at hP
    simpa using hP.symm
  refine ⟨Z, fun a => (hZP a).2.1, hZ.trans hN3, ?_⟩
  let π := projection ω₁ ω₂
  choose repr hrepr using (fun q : Torus ω₁ ω₂ =>
    QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup q)
  let A := Z.toMultiset.map repr
  let B : Multiset ℂ := 0 ::ₘ 0 ::ₘ 0 ::ₘ 0
  have hArepr : A.map π = Z.toMultiset := by
    simp only [A, Multiset.map_map]
    have he : π ∘ repr = id := funext hrepr
    rw [he, Multiset.map_id]
  have hab : DivisorSumConstraint.DivisorLists ω₁ ω₂ F A B := by
    intro a
    refine ⟨?_, ?_⟩
    · rw [hArepr, Finsupp.count_toMultiset]
      exact (hZP a).2.1
    · have he : (B.map π).count (π a) = P (π a) := by
        rw [hPeq]
        by_cases hzero : π a = 0
        · simp [B, π, hzero]
        · simp [B, hzero]
      exact he.trans (hZP a).2.2
  have hs := DivisorSumConstraint.divisor_sum_constraint ω₁ ω₂ h₁ h₂ F hF hp hn A B hab
  have hπsum : π (A.sum - B.sum) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr hs
  have hB : B.sum = 0 := by simp [B]
  rw [hB, sub_zero, π.map_multiset_sum, hArepr, Finsupp.sum_toMultiset] at hπsum
  exact hπsum

/-- The same conclusion for the scalar pullback, restoring only its canonical sphere values. -/
lemma triple_pole_divisor_fn {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (f : ℂ → ℂ)
    (hm : Meromorphic f) (hp : Periodic ω₁ ω₂ f)
    (hpol : ∀ a : ℂ, a ∈ lattice ω₁ ω₂ →
      meromorphicOrderAt f a = ((-3 : ℤ) : WithTop ℤ))
    (hreg : ∀ a : ℂ, a ∉ lattice ω₁ ω₂ → AnalyticAt ℂ f a) :
    ∃ Z : Torus ω₁ ω₂ →₀ ℕ,
      (∀ a : ℂ, Z (projection ω₁ ω₂ a) = (meromorphicOrderAt f a).untop₀.toNat) ∧
      Z.sum (fun _ n => n) = 3 ∧ Z.sum (fun q n => n • q) = 0 := by
  let F := LocalQuotientsArithmetic.fill f
  have hF : ScalarMeromorphicOn univ F :=
    LocalQuotientsArithmetic.scalarMeromorphicOn_fill univ isOpen_univ f
      (fun a _ => hm a)
  have hfill (a : ℂ) : F a =
      if a ∈ lattice ω₁ ω₂ then sphereInfty else sphereFinite (f a) := by
    by_cases ha : a ∈ lattice ω₁ ω₂
    · have hneg : ((-3 : ℤ) : WithTop ℤ) < 0 := by
        exact_mod_cast (by norm_num : (-3 : ℤ) < 0)
      rw [ite_eq_left ha]
      exact (LocalQuotientsArithmetic.fill_eq_infty_iff f a).mpr ((hpol a ha) ▸ hneg)
    · simpa only [ite_eq_right ha] using LocalQuotientsArithmetic.fill_of_analyticAt (hreg a ha)
  have hpF : Periodic ω₁ ω₂ F := by
    intro a l hl
    have he : a + l ∈ lattice ω₁ ω₂ ↔ a ∈ lattice ω₁ ω₂ := by
      constructor
      · intro h
        simpa only [add_sub_cancel_right] using sub_mem h hl
      · intro h
        exact add_mem h hl
    simp only [hfill, he, hp a l hl]
  have horder (a : ℂ) : meromorphicOrderAt (scalarFinitePart F) a = meromorphicOrderAt f a :=
    meromorphicOrderAt_congr (LocalQuotientsArithmetic.finitePart_fill_germ (hm a))
  obtain ⟨Z, hZ, hdeg, hsum⟩ := triple_pole_divisor h₁ h₂ F hF hpF
    (fun a ha => (horder a).trans (hpol a ha))
    (fun a ha => (horder a).symm ▸ (hreg a ha).meromorphicOrderAt_nonneg)
  exact ⟨Z, fun a => (hZ a).trans (congrArg (fun x : WithTop ℤ => x.untop₀.toNat) (horder a)),
    hdeg, hsum⟩

/-- Two of the three zeros prescribe the last zero, including coincidence at a flex. -/
lemma degree_three_double_zero {A : Type*} [AddCommGroup A]
    (Z : A →₀ ℕ) (hdeg : Z.sum (fun _ n => n) = 3)
    (hsum : Z.sum (fun q n => n • q) = 0) (q : A) (hq : 2 ≤ Z q) :
    Z = Finsupp.single q 2 + Finsupp.single (-(q + q)) 1 := by
  classical
  let M := Z.toMultiset
  have hcard : M.card = 3 := by simpa [M, Function.id_def] using hdeg
  have htwo : (q ::ₘ q ::ₘ 0 : Multiset A) ≤ M := by
    rw [Multiset.le_iff_count]
    intro a
    by_cases ha : a = q
    · subst a
      simpa [M] using hq
    · simp [ha]
  obtain ⟨R, hR⟩ := exists_add_of_le htwo
  have hRcard : R.card = 1 := by
    have := congrArg Multiset.card hR
    simp only [Multiset.card_add, Multiset.card_cons, Multiset.card_zero] at this
    omega
  obtain ⟨r, hr⟩ := Multiset.card_eq_one.mp hRcard
  have hM : M = (q ::ₘ q ::ₘ 0) + {r} := hR.trans (congrArg ((q ::ₘ q ::ₘ 0) + ·) hr)
  have hsumM : M.sum = 0 := by simpa [M] using hsum
  have hrvalue : r = -(q + q) := by
    rw [hM] at hsumM
    simp only [Multiset.sum_add, Multiset.sum_cons, Multiset.sum_zero, add_zero] at hsumM
    exact eq_neg_of_add_eq_zero_right (by simpa using hsumM)
  ext a
  have hc := congrArg (Multiset.count a) hM
  by_cases hqa : q = a <;> by_cases hra : -(q + q) = a <;>
    simp [M, hrvalue, Finsupp.single_apply, Multiset.count_singleton,
      hqa, hra, eq_comm] at hc ⊢ <;> omega


theorem tangent_slope : Specs.D12Complex.Ch22.TangentAddition.tangent_slope_type := by
  intro ω₁ ω₂ h₁ h₂ z hz hy
  exact tangent_slope_canonical h₁ h₂ hz hy

lemma two_single_support {A : Type*} [DecidableEq A] (t v a : A) :
    (Finsupp.single t 2 + Finsupp.single v 1 : A →₀ ℕ) a ≠ 0 ↔ a = t ∨ a = v := by
  by_cases ht : a = t <;> by_cases hv : a = v <;>
    simp [Finsupp.single_apply, ht, hv, eq_comm]

theorem tangent_intersections :
    Specs.D12Complex.Ch22.TangentAddition.tangent_intersections_type := by
  intro ω₁ ω₂ h₁ h₂ z hz hy
  dsimp only
  let x := weierstrassP ω₁ ω₂ z
  let y := deriv (weierstrassP ω₁ ω₂) z
  let m := (12*x^2-g₂ ω₁ ω₂)/(2*y)
  let b := y-m*x
  let f := fun w => deriv (weierstrassP ω₁ ω₂) w - m*weierstrassP ω₁ ω₂ w - b
  let t := projection ω₁ ω₂ z
  have hfin (w : ℂ) : meromorphicOrderAt f w ≠ ⊤ :=
    affine_line_order_finite h₁ h₂ m b w
  have ha (w : ℂ) (hw : w ∉ lattice ω₁ ω₂) : AnalyticAt ℂ f w :=
    affine_line_analytic h₁ h₂ m b hw
  obtain ⟨Z, hZ, hdeg, hsum⟩ := triple_pole_divisor_fn h₁ h₂ f
    (affine_line_meromorphic h₁ h₂ m b) (affine_line_periodic h₁ h₂ m b)
    (fun w hw => affine_line_pole_order h₁ h₂ m b hw) ha
  have htwo : 2 ≤ Z t := by
    rw [hZ z]
    exact affine_tangent_double_zero h₁ h₂ hz hy
  have hZe : Z = Finsupp.single t 2 + Finsupp.single (-(t+t)) 1 :=
    degree_three_double_zero Z hdeg hsum t htwo
  refine ⟨Z, fun w => ⟨hfin w, hZ w⟩, hdeg, hZe, ?_, ?_⟩
  · change meromorphicOrderAt f z = (↑(show ℤ from if -(t+t) = t then 3 else 2) : WithTop ℤ)
    have ho : meromorphicOrderAt f z = ((Z t : ℕ) : ℤ) := by
      rw [hZ z]
      exact order_eq_nat_part (ha z hz) (hfin z)
    rw [hZe] at ho
    by_cases he : -(t+t) = t
    · simpa [he] using ho
    · have he' : -t + -t ≠ t := by simpa only [neg_add] using he
      simpa [Finsupp.single_apply, he, he'] using ho
  · intro w hw
    have hs := zero_iff_order_nat_ne_zero (ha w hw) (hfin w)
    rw [← hZ w, hZe, two_single_support] at hs
    change (_ = _ ↔ _)
    rw [hs]
    dsimp only [f]
    constructor <;> intro h <;> linear_combination h

theorem tangent_polynomial :
    Specs.D12Complex.Ch22.TangentAddition.tangent_polynomial_type := by
  intro ω₁ ω₂ h₁ h₂ z hz hy
  dsimp only
  let x := weierstrassP ω₁ ω₂ z
  let y := deriv (weierstrassP ω₁ ω₂) z
  let m := (12*x^2-g₂ ω₁ ω₂)/(2*y)
  have hc : y^2 = 4*x^3-g₂ ω₁ ω₂*x-g₃ ω₁ ω₂ :=
    Ch22.WeierstrassEquations.first_equation ω₁ ω₂ h₁ h₂ z hz
  have ht : 2*y*m = 12*x^2-g₂ ω₁ ω₂ := tangent_slope_identity x y _ hy
  exact ⟨tangent_polynomial_factorization _ _ x y m hc ht,
    tangent_polynomial_roots _ _ x y m hc ht,
    tangent_polynomial_rootMultiplicity _ _ x y m hc ht⟩

lemma doubling_from_support {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) {z : ℂ} (hz : z ∉ TorusSurface.lattice ω₁ ω₂)
    (hy : deriv (weierstrassP ω₁ ω₂) z ≠ 0) (m : ℂ)
    (hm : 2 * deriv (weierstrassP ω₁ ω₂) z * m =
      12 * weierstrassP ω₁ ω₂ z ^ 2 - g₂ ω₁ ω₂)
    (hsupp : ∀ w : ℂ, w ∉ TorusSurface.lattice ω₁ ω₂ →
      (deriv (weierstrassP ω₁ ω₂) w = m * weierstrassP ω₁ ω₂ w +
        (deriv (weierstrassP ω₁ ω₂) z - m*weierstrassP ω₁ ω₂ z) ↔
        projection ω₁ ω₂ w = projection ω₁ ω₂ z ∨
        projection ω₁ ω₂ w = -(projection ω₁ ω₂ z + projection ω₁ ω₂ z))) :
    let x := weierstrassP ω₁ ω₂ z
    let y := deriv (weierstrassP ω₁ ω₂) z
    let x₂ := -2*x+m^2/4
    let y₂ := -y+m*(x-x₂)
    let t := projection ω₁ ω₂ z
    2*z ∉ TorusSurface.lattice ω₁ ω₂ ∧
      weierstrassP ω₁ ω₂ (2*z) = x₂ ∧ deriv (weierstrassP ω₁ ω₂) (2*z) = y₂ ∧
      phi ω₁ ω₂ (-(t+t)) = affinePoint x₂ (-y₂) ∧
      phi ω₁ ω₂ (t+t) = affinePoint x₂ y₂ := by
  let p := weierstrassP ω₁ ω₂
  let x := p z
  let y := deriv p z
  let x₂ := -2*x+m^2/4
  let y₂ := -y+m*(x-x₂)
  let t := projection ω₁ ω₂ z
  let v := -(t+t)
  have hcurve : y^2 = 4*x^3-g₂ ω₁ ω₂*x-g₃ ω₁ ω₂ :=
    Ch22.WeierstrassEquations.first_equation ω₁ ω₂ h₁ h₂ z hz
  have hm' : 2*y*m = 12*x^2-g₂ ω₁ ω₂ := hm
  have hd : 2*z ∉ TorusSurface.lattice ω₁ ω₂ := by
    intro hmem
    have hp := (Ch22.HalfPeriodValues.projection_zero_iff (2*z)).mpr hmem
    have hsum : t+t=0 := by simpa only [t, two_mul, map_add] using hp
    have hself : t = -t := eq_neg_of_add_eq_zero_left hsum
    exact hy ((TorusCubicBiholomorphism.derivative_separation ω₁ ω₂ h₁ h₂).2 z hz |>.mpr hself)
  let w := -(2*z)
  have hw : w ∉ TorusSurface.lattice ω₁ ω₂ := by simpa only [w, neg_mem_iff] using hd
  have hwv : projection ω₁ ω₂ w = v := by simp only [w, v, t, two_mul, map_neg, map_add]
  have hline : deriv p w = m * p w + (y-m*x) := (hsupp w hw).mpr (Or.inr hwv)
  have hline' : deriv p w = y+m*(p w-x) := by linear_combination hline
  have hresX : p w = x₂ := by
    by_cases hvt : v=t
    · have hthird : (y+m*(x₂-x))^2 = 4*x₂^3-g₂ ω₁ ω₂*x₂-g₃ ω₁ ω₂ :=
        tangent_third_curve (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) x y m hcurve hm'
      obtain ⟨a, ha, hax, hay⟩ := TorusCubicBiholomorphism.finite_values_surjective
        h₁ h₂ x₂ (y+m*(x₂-x)) hthird
      change p a = x₂ at hax
      change deriv p a = y+m*(x₂-x) at hay
      have haline : deriv p a = m*p a+(y-m*x) := by rw [hax, hay]; ring
      have hat : projection ω₁ ω₂ a = t := by
        rcases (hsupp a ha).mp haline with ht | hv
        · exact ht
        · exact hv.trans hvt
      have hx₂ : x₂=x := hax.symm.trans
        (TorusCubicBiholomorphism.Fibres.wp_eq_of_projection_eq h₁ h₂ hat)
      exact (TorusCubicBiholomorphism.Fibres.wp_eq_of_projection_eq h₁ h₂
        (hwv.trans hvt)).trans hx₂.symm
    · have hwcurve : (deriv p w)^2 = 4*(p w)^3-g₂ ω₁ ω₂*(p w)-g₃ ω₁ ω₂ :=
        Ch22.WeierstrassEquations.first_equation ω₁ ω₂ h₁ h₂ w hw
      have hroot : p w=x ∨ p w=x₂ :=
        (tangent_roots (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) x y m (p w) hcurve hm').mp
          (by rw [← hline']; exact hwcurve.symm)
      rcases hroot with hx | hx
      · have hwy : deriv p w=y := by rw [hline', hx]; ring
        have hwt : projection ω₁ ω₂ w = t :=
          TorusCubicBiholomorphism.Fibres.wp_deriv_separates h₁ h₂ hw hz hx hwy
        exact (hvt (hwv.symm.trans hwt)).elim
      · exact hx
  have hresY : deriv p w = -y₂ := by rw [hline', hresX]; dsimp only [y₂]; ring
  have hphi : phi ω₁ ω₂ v = affinePoint x₂ (-y₂) := by
    rw [← hwv, phi_finite h₁ h₂ hw]
    change affinePoint (p w) (deriv p w) = _
    rw [hresX, hresY]
  have hphiD : phi ω₁ ω₂ (t+t) = affinePoint x₂ y₂ := by
    have hr := phi_neg_finite_of_coordinates h₁ h₂ hphi
    simpa only [v, neg_neg] using hr
  have hp2 : phi ω₁ ω₂ (projection ω₁ ω₂ (2*z)) = phi ω₁ ω₂ (t+t) := by
    congr 1
    simp only [t, two_mul, map_add]
  have hc2 := affinePoint_injective
    ((phi_finite h₁ h₂ hd).symm.trans (hp2.trans hphiD))
  exact ⟨hd, hc2.1, hc2.2, hphi, hphiD⟩

theorem tangent_doubling :
    Specs.D12Complex.Ch22.TangentAddition.tangent_doubling_type := by
  intro ω₁ ω₂ h₁ h₂ z hz hy
  obtain ⟨Z, hZ, hdeg, heq, hflex, hsupp⟩ := tangent_intersections ω₁ ω₂ h₁ h₂ z hz hy
  let x := weierstrassP ω₁ ω₂ z
  let y := deriv (weierstrassP ω₁ ω₂) z
  let m := (12*x^2-g₂ ω₁ ω₂)/(2*y)
  exact doubling_from_support h₁ h₂ hz hy m (tangent_slope_identity x y _ hy) hsupp

section ProjectiveLine
open ProjectivePlaneTopology (HomogeneousVector ComplexProjectivePlane affineParam)
/-- The projective affine line Y-mX-bZ=0, with coordinate order Z,X,Y. -/
private def OnAffineLine (m b : ℂ) (p : ComplexProjectivePlane) : Prop :=
  ∃ v : HomogeneousVector, ProjectivePlaneTopology.projection v = p ∧ v.val 2 - m * v.val 1 - b * v.val 0 = 0

private def affineRep (x y : ℂ) : HomogeneousVector :=
  ⟨![1,x,y], by intro h; have h0 := congrFun h 0; simp at h0⟩

private def infinityRep : HomogeneousVector :=
  ⟨![0,0,1], by intro h; have h2 := congrFun h 2; simp at h2⟩

private lemma affineRep_projection (x y : ℂ) :
    ProjectivePlaneTopology.projection (affineRep x y) = affinePoint x y := by
  unfold affinePoint affineParam
  apply congrArg ProjectivePlaneTopology.projection
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [affineRep]

private lemma infinityRep_projection : ProjectivePlaneTopology.projection infinityRep = CubicInfinityChart.O := by
  unfold CubicInfinityChart.O affineParam
  apply congrArg ProjectivePlaneTopology.projection
  apply Subtype.ext
  ext i
  fin_cases i <;> norm_num [infinityRep, Fin.insertNth, Fin.succAboveCases]

lemma no_line_O (m b : ℂ) : ¬ OnAffineLine m b CubicInfinityChart.O := by
  rintro ⟨v, hv, he⟩
  have hm := (ProjectivePlaneTopology.projection_eq_iff_minors v infinityRep).mp
    (hv.trans infinityRep_projection.symm)
  have hv0 : v.val 0 = 0 := by simpa [infinityRep] using hm 0 2
  have hv1 : v.val 1 = 0 := by simpa [infinityRep] using hm 1 2
  have hv2 : v.val 2 = 0 := by simpa [hv0, hv1] using he
  apply v.property
  ext i
  fin_cases i <;> simp [hv0, hv1, hv2]

lemma iff_affinePoint (m b x y : ℂ) :
    OnAffineLine m b (affinePoint x y) ↔ y - m*x - b = 0 := by
  constructor
  · rintro ⟨v, hv, he⟩
    have hm := (ProjectivePlaneTopology.projection_eq_iff_minors v (affineRep x y)).mp
      (hv.trans (affineRep_projection x y).symm)
    have hv1 : v.val 1 = v.val 0 * x := by simpa [affineRep] using hm 1 0
    have hv2 : v.val 2 = v.val 0 * y := by simpa [affineRep] using hm 2 0
    have hv0 : v.val 0 ≠ 0 := by
      intro hz
      apply v.property
      ext i
      fin_cases i <;> simp [hz, hv1, hv2]
    have hzero : v.val 0 * (y - m*x - b) = 0 := by
      rw [hv1, hv2] at he
      convert he using 1
      ring
    exact (mul_eq_zero.mp hzero).resolve_left hv0
  · intro he
    refine ⟨affineRep x y, affineRep_projection x y, ?_⟩
    simpa [affineRep] using he

theorem projective_line : Specs.D12Complex.Ch22.TangentAddition.projective_line_type := by
  intro m b
  exact ⟨iff_affinePoint m b, no_line_O m b⟩
theorem tangent_projective_intersections :
    Specs.D12Complex.Ch22.TangentAddition.tangent_projective_intersections_type := by
  intro ω₁ ω₂ h₁ h₂ z hz hy
  dsimp only
  let x := weierstrassP ω₁ ω₂ z
  let y := deriv (weierstrassP ω₁ ω₂) z
  let m := (12*x^2-g₂ ω₁ ω₂)/(2*y)
  let b := y-m*x
  let t := projection ω₁ ω₂ z
  obtain ⟨Z, hZ, hdeg, heq, hflex, hsupp⟩ := tangent_intersections ω₁ ω₂ h₁ h₂ z hz hy
  intro u
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup u
  change OnAffineLine m b (phi ω₁ ω₂ (projection ω₁ ω₂ a)) ↔
    projection ω₁ ω₂ a=t ∨ projection ω₁ ω₂ a=-(t+t)
  by_cases ha : a ∈ lattice ω₁ ω₂
  · have hp0 : projection ω₁ ω₂ a = 0 := (QuotientAddGroup.eq_zero_iff _).mpr ha
    have hnone : ¬ OnAffineLine m b (phi ω₁ ω₂ (projection ω₁ ω₂ a)) := by
      rw [hp0, phi_zero h₁ h₂]
      exact no_line_O m b
    have hza : Z (projection ω₁ ω₂ a) = 0 := by
      rw [(hZ a).2, affine_line_pole_order h₁ h₂ m b ha]
      norm_num
    have hnone' : ¬ (projection ω₁ ω₂ a=t ∨ projection ω₁ ω₂ a=-(t+t)) := by
      rw [← two_single_support t (-(t+t)), ← heq]
      exact not_ne_iff.mpr hza
    exact iff_of_false hnone hnone'
  · rw [phi_finite h₁ h₂ ha, iff_affinePoint]
    have he := hsupp a ha
    change (_ ↔ projection ω₁ ω₂ a=t ∨ projection ω₁ ω₂ a=-(t+t)) at he
    rw [← he]
    dsimp only [b, m, x, y]
    constructor <;> intro h <;> linear_combination h

end ProjectiveLine

end D12Complex.TangentAddition
