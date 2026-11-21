import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.SecantAddition
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.TorusCubicBiholomorphism
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.DivisorSumConstraint
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! Generic secants for the literal lattice-associated projective cubic.
The line pullback has exactly one triple pole class. The divisor-degree and
sum constraints identify its residual zero as the negative torus sum. A cubic
factorization gives the coordinates. If the residual zero repeats an endpoint,
its order forces the pulled-back line derivative to vanish, giving the same
factorization with the repeated root. Finally periodic meromorphic germs extend
the scalar formula through the exceptional arguments without assigning them
pointwise values. See paper.tex:4070–4094 and research/addition-reference-notes.md. -/

noncomputable section
namespace D12Complex.SecantAddition
open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)

/-- Pullback of the affine line `y = m*x+b`. -/
def linePullback (ω₁ ω₂ m b t : ℂ) : ℂ :=
  deriv (weierstrassP ω₁ ω₂) t - m * weierstrassP ω₁ ω₂ t - b

/-- The scalar secant expression, interpreted only on its finite domain or
as a meromorphic germ. -/
def additionExpression (ω₁ ω₂ z w : ℂ) : ℂ :=
  -weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ w +
    ((deriv (weierstrassP ω₁ ω₂) z - deriv (weierstrassP ω₁ ω₂) w) /
      (weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ w)) ^ 2 / 4

end D12Complex.SecantAddition
end

namespace D12Complex.SecantAddition.Algebra

 theorem secant_incidence (x₁ y₁ x₂ y₂ : ℂ) (h : x₁ ≠ x₂) :
    ((y₁ - y₂) / (x₁ - x₂)) * x₂ +
      (y₁ - ((y₁ - y₂) / (x₁ - x₂)) * x₁) = y₂ := by
  field_simp [sub_ne_zero.mpr h]
  ring

 theorem cubic_secant_coefficient (G H x₁ x₂ m b : ℂ)
    (h₁ : (m * x₁ + b) ^ 2 = 4 * x₁ ^ 3 - G * x₁ - H)
    (h₂ : (m * x₂ + b) ^ 2 = 4 * x₂ ^ 3 - G * x₂ - H)
    (h : x₁ ≠ x₂) :
    G = 4 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) - m ^ 2 * (x₁ + x₂) - 2 * m * b := by
  have hz : (x₁ - x₂) *
      (4 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) - m ^ 2 * (x₁ + x₂) - 2 * m * b - G) = 0 := by
    linear_combination -h₁ + h₂
  have he := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr h)
  linear_combination -he

 theorem cubic_secant_constant (G H x₁ x₂ m b : ℂ)
    (h₁ : (m * x₁ + b) ^ 2 = 4 * x₁ ^ 3 - G * x₁ - H)
    (hG : G = 4 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) - m ^ 2 * (x₁ + x₂) - 2 * m * b) :
    H = x₁ * x₂ * m ^ 2 - 4 * x₁ * x₂ * (x₁ + x₂) - b ^ 2 := by
  linear_combination h₁ - x₁ * hG

 theorem cubic_secant_factorization (G H x₁ x₂ m b : ℂ)
    (h₁ : (m * x₁ + b) ^ 2 = 4 * x₁ ^ 3 - G * x₁ - H)
    (h₂ : (m * x₂ + b) ^ 2 = 4 * x₂ ^ 3 - G * x₂ - H)
    (h : x₁ ≠ x₂) (X : ℂ) :
    4 * X ^ 3 - G * X - H - (m * X + b) ^ 2 =
      4 * (X - x₁) * (X - x₂) * (X - (m ^ 2 / 4 - x₁ - x₂)) := by
  have hG := cubic_secant_coefficient G H x₁ x₂ m b h₁ h₂ h
  have hH := cubic_secant_constant G H x₁ x₂ m b h₁ hG
  rw [hG, hH]
  ring

 theorem third_on_cubic (G H x₁ x₂ m b : ℂ)
    (h₁ : (m * x₁ + b) ^ 2 = 4 * x₁ ^ 3 - G * x₁ - H)
    (h₂ : (m * x₂ + b) ^ 2 = 4 * x₂ ^ 3 - G * x₂ - H)
    (h : x₁ ≠ x₂) :
    (m * (m ^ 2 / 4 - x₁ - x₂) + b) ^ 2 =
      4 * (m ^ 2 / 4 - x₁ - x₂) ^ 3 - G * (m ^ 2 / 4 - x₁ - x₂) - H := by
  have hf := cubic_secant_factorization G H x₁ x₂ m b h₁ h₂ h
    (m ^ 2 / 4 - x₁ - x₂)
  simp only [sub_self, mul_zero] at hf
  linear_combination -hf

 theorem reflected_ordinate (x₁ y₁ x₃ m : ℂ) :
    -(m * x₃ + (y₁ - m * x₁)) = -y₁ + m * (x₁ - x₃) := by ring

 theorem third_eq_first_of_tangent (G H x₁ x₂ m b : ℂ)
    (h₁ : (m * x₁ + b) ^ 2 = 4 * x₁ ^ 3 - G * x₁ - H)
    (h₂ : (m * x₂ + b) ^ 2 = 4 * x₂ ^ 3 - G * x₂ - H)
    (h : x₁ ≠ x₂)
    (hD : 6 * x₁ ^ 2 - G / 2 - m * (m * x₁ + b) = 0) :
    m ^ 2 / 4 - x₁ - x₂ = x₁ := by
  have hG := cubic_secant_coefficient G H x₁ x₂ m b h₁ h₂ h
  have hz : 2 * (x₁ - x₂) * (x₁ - (m ^ 2 / 4 - x₁ - x₂)) = 0 := by
    linear_combination hD + hG / 2
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (by norm_num) (sub_ne_zero.mpr h)))).symm

 theorem third_eq_second_of_tangent (G H x₁ x₂ m b : ℂ)
    (h₁ : (m * x₁ + b) ^ 2 = 4 * x₁ ^ 3 - G * x₁ - H)
    (h₂ : (m * x₂ + b) ^ 2 = 4 * x₂ ^ 3 - G * x₂ - H)
    (h : x₁ ≠ x₂)
    (hD : 6 * x₂ ^ 2 - G / 2 - m * (m * x₂ + b) = 0) :
    m ^ 2 / 4 - x₁ - x₂ = x₂ := by
  have hG := cubic_secant_coefficient G H x₁ x₂ m b h₁ h₂ h
  have hz : 2 * (x₂ - x₁) * (x₂ - (m ^ 2 / 4 - x₁ - x₂)) = 0 := by
    linear_combination hD + hG / 2
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (by norm_num) (sub_ne_zero.mpr h.symm)))).symm

open Polynomial

 theorem cubic_secant_polynomial_factorization (G H x₁ x₂ m b : ℂ)
    (h₁ : (m * x₁ + b) ^ 2 = 4 * x₁ ^ 3 - G * x₁ - H)
    (h₂ : (m * x₂ + b) ^ 2 = 4 * x₂ ^ 3 - G * x₂ - H)
    (h : x₁ ≠ x₂) :
    (C 4 * X ^ 3 - C G * X - C H - (C m * X + C b) ^ 2 : ℂ[X]) =
      C 4 * (X - C x₁) * (X - C x₂) * (X - C (m ^ 2 / 4 - x₁ - x₂)) := by
  apply Polynomial.funext
  intro v
  simpa only [eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_add] using
    cubic_secant_factorization G H x₁ x₂ m b h₁ h₂ h v

 theorem cubic_secant_roots (G H x₁ x₂ m b : ℂ)
    (h₁ : (m * x₁ + b) ^ 2 = 4 * x₁ ^ 3 - G * x₁ - H)
    (h₂ : (m * x₂ + b) ^ 2 = 4 * x₂ ^ 3 - G * x₂ - H)
    (h : x₁ ≠ x₂) :
    (C 4 * X ^ 3 - C G * X - C H - (C m * X + C b) ^ 2 : ℂ[X]).roots =
      {x₁, x₂, m ^ 2 / 4 - x₁ - x₂} := by
  rw [cubic_secant_polynomial_factorization G H x₁ x₂ m b h₁ h₂ h,
    mul_assoc (C 4), mul_assoc (C 4), roots_C_mul _ (by norm_num)]
  rw [roots_mul (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _)
      (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))]
  simp only [roots_X_sub_C]
  rfl

 theorem secant_root_eq (G H x₁ x₂ m b v : ℂ)
    (h₁ : (m * x₁ + b) ^ 2 = 4 * x₁ ^ 3 - G * x₁ - H)
    (h₂ : (m * x₂ + b) ^ 2 = 4 * x₂ ^ 3 - G * x₂ - H)
    (h : x₁ ≠ x₂)
    (hv : (m * v + b) ^ 2 = 4 * v ^ 3 - G * v - H)
    (hv₁ : v ≠ x₁) (hv₂ : v ≠ x₂) : v = m ^ 2 / 4 - x₁ - x₂ := by
  have hf := cubic_secant_factorization G H x₁ x₂ m b h₁ h₂ h v
  have hz : 4 * (v - x₁) * (v - x₂) * (v - (m ^ 2 / 4 - x₁ - x₂)) = 0 := by
    linear_combination -hv - hf
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hv₁))
      (sub_ne_zero.mpr hv₂)))

end D12Complex.SecantAddition.Algebra

noncomputable section
namespace D12Complex.SecantAddition
open scoped BigOperators

lemma three_divisor_decomposition {G : Type*} (Z : G →₀ ℕ) {p q : G}
    (hZ : Z.sum (fun _ n => n) = 3) (hp : 0 < Z p) (hq : 0 < Z q)
    (hpq : p ≠ q) :
    ∃ r : G, Z = Finsupp.single p 1 + Finsupp.single q 1 + Finsupp.single r 1 := by
  classical
  let M := Z.toMultiset
  have hM : M.card = 3 := by simpa only [M, Finsupp.card_toMultiset, Function.id_def] using hZ
  have hpm : p ∈ M := by simpa [M, ← Multiset.count_pos] using hp
  have hqm : q ∈ M := by simpa [M, ← Multiset.count_pos] using hq
  obtain ⟨A, hA⟩ := Multiset.exists_cons_of_mem hpm
  have hqA : q ∈ A := by simpa [hA, hpq.symm] using hqm
  obtain ⟨B, hB⟩ := Multiset.exists_cons_of_mem hqA
  have hBcard : B.card = 1 := by rw [hA, hB] at hM; simp only [Multiset.card_cons] at hM; omega
  obtain ⟨r, hr⟩ := Multiset.card_eq_one.mp hBcard
  refine ⟨r, ?_⟩
  have he : M = ({p} : Multiset G) + {q} + {r} := by
    simp [hA, hB, hr]
  ext t
  have hc := congrArg (fun N : Multiset G => N.count t) he
  simpa [M, Finsupp.single_apply, Multiset.count_cons, Multiset.count_singleton, eq_comm, add_assoc, add_comm, add_left_comm] using hc

lemma three_divisor_third {G : Type*} [AddCommGroup G] (Z : G →₀ ℕ) {p q : G}
    (hZ : Z.sum (fun _ n => n) = 3) (hp : 0 < Z p) (hq : 0 < Z q)
    (hpq : p ≠ q) (hsum : Z.sum (fun t n => n • t) = 0) :
    Z = Finsupp.single p 1 + Finsupp.single q 1 + Finsupp.single (-p-q) 1 := by
  classical
  obtain ⟨r, hr⟩ := three_divisor_decomposition Z hZ hp hq hpq
  have hpr : p + q + r = 0 := by
    rw [hr] at hsum
    simpa [Finsupp.sum_add_index', add_nsmul] using hsum
  have he : r = -p-q := by
    calc
      r = (p+q+r) - (p+q) := by abel
      _ = -p-q := by rw [hpr]; abel
  exact he ▸ hr

end D12Complex.SecantAddition

noncomputable section
open Set Filter
open scoped Topology BigOperators Classical
namespace D12Complex.SecantAddition
open TorusSurface
open Ch22.WeierstrassSeries (weierstrassP periodPair)

lemma linePullback_meromorphic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (m b : ℂ) : Meromorphic (linePullback ω₁ ω₂ m b) := by
  intro a
  let L := periodPair h₁ h₂
  exact ((L.meromorphic_weierstrassP.deriv a).sub
    ((analyticAt_const.meromorphicAt).mul (L.meromorphic_weierstrassP a))).sub
      analyticAt_const.meromorphicAt

lemma linePullback_periodic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (m b : ℂ) : Periodic ω₁ ω₂ (linePullback ω₁ ω₂ m b) := by
  intro a l hl
  let L := periodPair h₁ h₂
  change deriv L.weierstrassP (a+l) - m * L.weierstrassP (a+l) - b =
    deriv L.weierstrassP a - m * L.weierstrassP a - b
  rw [L.deriv_weierstrassP, L.derivWeierstrassP_add_coe a ⟨l,hl⟩,
    L.weierstrassP_add_coe a ⟨l,hl⟩]

lemma linePullback_analyticAt {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (m b : ℂ) {a : ℂ} (ha : a ∉ lattice ω₁ ω₂) :
    AnalyticAt ℂ (linePullback ω₁ ω₂ m b) a := by
  let L := periodPair h₁ h₂
  exact ((L.analyticOnNhd_weierstrassP a ha).deriv.sub
    (analyticAt_const.mul (L.analyticOnNhd_weierstrassP a ha))).sub analyticAt_const

lemma linePullback_pole_order {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (m b : ℂ) {a : ℂ} (ha : a ∈ lattice ω₁ ω₂) :
    meromorphicOrderAt (linePullback ω₁ ω₂ m b) a = (-3 : ℤ) := by
  let L := periodPair h₁ h₂
  have hd := Ch22.HalfPeriodValues.derivative_pole_order L ha
  have hdm : MeromorphicAt (deriv L.weierstrassP) a := L.meromorphic_weierstrassP.deriv a
  by_cases hm : m = 0
  · subst m
    change meromorphicOrderAt (fun t => deriv L.weierstrassP t - 0 * L.weierstrassP t - b) a = _
    simp only [zero_mul, sub_zero]
    exact ((DivisorDegree.pole_order_sub_const hdm b).2
      (by rw [hd]; exact WithTop.coe_lt_coe.mpr (by norm_num : (-3 : ℤ) < 0))).trans hd
  · let g : ℂ → ℂ := fun t => (-m) * L.weierstrassP t - b
    have hgm : MeromorphicAt g a :=
      (analyticAt_const.meromorphicAt.mul (L.meromorphic_weierstrassP a)).sub
        analyticAt_const.meromorphicAt
    have hmo : meromorphicOrderAt (fun t => (-m) * L.weierstrassP t) a = (-2 : ℤ) := by
      have he : (fun t => (-m) * L.weierstrassP t) = (-m) • L.weierstrassP := rfl
      rw [he, meromorphicOrderAt_const_smul_eq_meromorphicOrderAt (neg_ne_zero.mpr hm),
        L.order_weierstrassP a ha]
      rfl
    have hgo : meromorphicOrderAt g a = (-2 : ℤ) := by
      exact ((DivisorDegree.pole_order_sub_const
        (analyticAt_const.meromorphicAt.mul (L.meromorphic_weierstrassP a)) b).2
          (by
            change meromorphicOrderAt (fun t => (-m) * L.weierstrassP t) a < 0
            rw [hmo]
            exact WithTop.coe_lt_coe.mpr (by norm_num : (-2 : ℤ) < 0))).trans hmo
    have he : linePullback ω₁ ω₂ m b = deriv L.weierstrassP + g := by
      funext t
      change deriv L.weierstrassP t - m * L.weierstrassP t - b = _
      dsimp [g]
      ring
    rw [he, meromorphicOrderAt_add_eq_left_of_lt hgm (by rw [hd,hgo]; exact WithTop.coe_lt_coe.mpr (by norm_num : (-3 : ℤ) < -2)), hd]

lemma linePullback_finite_order {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (m b a : ℂ) :
    meromorphicOrderAt (linePullback ω₁ ω₂ m b) a ≠ ⊤ := by
  exact ((linePullback_meromorphic h₁ h₂ m b).meromorphicOn (s := univ)).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ 0) (mem_univ a)
      (by rw [linePullback_pole_order h₁ h₂ m b (zero_mem _)]; simp)

lemma linePullback_zero_divisor {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (m b : ℂ) :
    ∃ Z : Torus ω₁ ω₂ →₀ ℕ,
      (∀ a, meromorphicOrderAt (linePullback ω₁ ω₂ m b) a ≠ ⊤ ∧
        Z (projection ω₁ ω₂ a) = (meromorphicOrderAt (linePullback ω₁ ω₂ m b) a).untop₀.toNat) ∧
      Z.sum (fun _ n => n) = 3 := by
  exact Ch22.HalfPeriodValues.zero_divisor h₁ h₂ (linePullback_meromorphic h₁ h₂ m b)
    (linePullback_periodic h₁ h₂ m b) 3
    (fun a ha => by simpa using linePullback_pole_order h₁ h₂ m b ha)
    (fun a ha => linePullback_analyticAt h₁ h₂ m b ha)

lemma linePullback_negative_part {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (m b a : ℂ) :
    (-(meromorphicOrderAt (linePullback ω₁ ω₂ m b) a).untop₀).toNat =
      (Finsupp.single 0 3 : Torus ω₁ ω₂ →₀ ℕ) (projection ω₁ ω₂ a) := by
  by_cases ha : a ∈ lattice ω₁ ω₂
  · rw [linePullback_pole_order h₁ h₂ m b ha,
      (Ch22.HalfPeriodValues.projection_zero_iff a).mpr ha]
    simp
  · have hq : projection ω₁ ω₂ a ≠ 0 :=
      (Ch22.HalfPeriodValues.projection_zero_iff a).not.mpr ha
    have hn := WithTop.untop₀_nonneg.mpr
      (linePullback_analyticAt h₁ h₂ m b ha).meromorphicOrderAt_nonneg
    simp [Finsupp.single_eq_of_ne hq, Int.toNat_of_nonpos (neg_nonpos.mpr hn)]

lemma linePullback_fill_periodic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (m b : ℂ) :
    Periodic ω₁ ω₂ (LocalQuotientsArithmetic.fill (linePullback ω₁ ω₂ m b)) := by
  intro a l hl
  have hlat : a + l ∈ lattice ω₁ ω₂ ↔ a ∈ lattice ω₁ ω₂ := add_mem_cancel_right hl
  by_cases ha : a ∈ lattice ω₁ ω₂
  · have hinf (x : ℂ) (hx : x ∈ lattice ω₁ ω₂) :
        LocalQuotientsArithmetic.fill (linePullback ω₁ ω₂ m b) x = sphereInfty := by
      apply (LocalQuotientsArithmetic.fill_eq_infty_iff _ _).mpr
      rw [linePullback_pole_order h₁ h₂ m b hx]
      exact WithTop.coe_lt_coe.mpr (by norm_num : (-3 : ℤ) < 0)
    rw [hinf a ha, hinf (a+l) (hlat.mpr ha)]
  · rw [LocalQuotientsArithmetic.fill_of_analyticAt
      (linePullback_analyticAt h₁ h₂ m b (hlat.not.mpr ha)),
      LocalQuotientsArithmetic.fill_of_analyticAt (linePullback_analyticAt h₁ h₂ m b ha)]
    exact congrArg sphereFinite (linePullback_periodic h₁ h₂ m b a l hl)

lemma linePullback_fill_nonconstant {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (m b : ℂ) :
    ¬ ∃ c : ℂ, ∀ z, LocalQuotientsArithmetic.fill (linePullback ω₁ ω₂ m b) z = sphereFinite c := by
  rintro ⟨c,hc⟩
  have hi : LocalQuotientsArithmetic.fill (linePullback ω₁ ω₂ m b) 0 = sphereInfty := by
    apply (LocalQuotientsArithmetic.fill_eq_infty_iff _ _).mpr
    rw [linePullback_pole_order h₁ h₂ m b (zero_mem _)]
    exact WithTop.coe_lt_coe.mpr (by norm_num : (-3 : ℤ) < 0)
  exact OnePoint.coe_ne_infty c ((hc 0).symm.trans hi)

end D12Complex.SecantAddition

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace D12Complex.SecantAddition
open TorusSurface
open LocalQuotientsArithmetic

lemma triple_pole_divisor_sum {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) {f : ℂ → ℂ}
    (hm : Meromorphic f) (hf : Periodic ω₁ ω₂ f)
    (hpole : ∀ a ∈ lattice ω₁ ω₂, meromorphicOrderAt f a = (-3 : ℤ))
    (han : ∀ a ∉ lattice ω₁ ω₂, AnalyticAt ℂ f a)
    (Z : Torus ω₁ ω₂ →₀ ℕ)
    (hZ : ∀ a, Z (projection ω₁ ω₂ a) = (meromorphicOrderAt f a).untop₀.toNat) :
    Z.sum (fun t n => n • t) = 0 := by
  classical
  let F := fill f
  have hF : ScalarMeromorphicOn univ F :=
    scalarMeromorphicOn_fill univ isOpen_univ f (hm.meromorphicOn (s := univ))
  have hper : Periodic ω₁ ω₂ F := by
    intro z l hl
    have hzl : z + l ∈ lattice ω₁ ω₂ ↔ z ∈ lattice ω₁ ω₂ := by
      constructor
      · intro h; simpa using sub_mem h hl
      · intro h; exact add_mem h hl
    by_cases hz : z ∈ lattice ω₁ ω₂
    · have hpz : F z = sphereInfty := (fill_eq_infty_iff f z).mpr (by rw [hpole z hz]; exact WithTop.coe_lt_coe.mpr (by norm_num : (-3 : ℤ) < 0))
      have hpzl : F (z+l) = sphereInfty := (fill_eq_infty_iff f (z+l)).mpr (by
        rw [hpole (z+l) (hzl.mpr hz)]; exact WithTop.coe_lt_coe.mpr (by norm_num : (-3 : ℤ) < 0))
      exact hpzl.trans hpz.symm
    · change fill f (z+l) = fill f z
      rw [fill_of_analyticAt (han (z+l) (hzl.not.mpr hz)), fill_of_analyticAt (han z hz), hf z l hl]
  have hn : ¬ ∃ c : ℂ, ∀ z, F z = sphereFinite c := by
    rintro ⟨c, hc⟩
    have hp0 : F 0 = sphereInfty := (fill_eq_infty_iff f 0).mpr (by
      rw [hpole 0 (zero_mem _)]; exact WithTop.coe_lt_coe.mpr (by norm_num : (-3 : ℤ) < 0))
    rw [hc 0] at hp0
    exact OnePoint.coe_ne_infty c hp0
  have hord (a : ℂ) : meromorphicOrderAt (scalarFinitePart F) a = meromorphicOrderAt f a :=
    meromorphicOrderAt_congr (finitePart_fill_germ (hm a))
  let π := projection ω₁ ω₂
  let a : Multiset ℂ := Z.toMultiset.map Quotient.out
  let b : Multiset ℂ := Multiset.replicate 3 0
  have hamap : a.map π = Z.toMultiset := by
    change (Z.toMultiset.map Quotient.out).map π = Z.toMultiset
    rw [Multiset.map_map]
    have he : (π ∘ Quotient.out) = id := by
      funext t
      exact Quotient.out_eq t
    rw [he, Multiset.map_id]
  have hab : DivisorSumConstraint.DivisorLists ω₁ ω₂ F a b := by
    intro z
    constructor
    · rw [hamap, Finsupp.count_toMultiset, hord, hZ]
    · rw [hord]
      by_cases hz : z ∈ lattice ω₁ ω₂
      · have hz0 : π z = 0 := Ch22.HalfPeriodValues.projection_zero_iff z |>.mpr hz
        simp [b, π, hz0, hpole z hz]
      · have hz0 : π z ≠ 0 := Ch22.HalfPeriodValues.projection_zero_iff z |>.not.mpr hz
        have ho : 0 ≤ (meromorphicOrderAt f z).untop₀ :=
          WithTop.untop₀_nonneg.mpr (han z hz).meromorphicOrderAt_nonneg
        simp [b, π, hz0, Int.toNat_of_nonpos (neg_nonpos.mpr ho)]
  have hs := DivisorSumConstraint.divisor_sum_constraint ω₁ ω₂ h₁ h₂ F hF hper hn a b hab
  have hclass : π a.sum = 0 := by
    have he : π (a.sum - b.sum) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr hs
    simpa [b, π] using he
  have hsum : (a.map π).sum = 0 := by
    rw [← π.map_multiset_sum]
    exact hclass
  rw [hamap, Finsupp.sum_toMultiset] at hsum
  exact hsum

end D12Complex.SecantAddition

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.SecantAddition

open D12Complex.Ch22
open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)

/-- A constant cannot be a local value of ℘, because ℘ has a pole. -/
theorem eventually_wp_ne_const {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (c a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, weierstrassP ω₁ ω₂ z ≠ c := by
  have hm := WeierstrassSeries.meromorphic ω₁ ω₂ h₁ h₂
  have hmc : Meromorphic (fun z => weierstrassP ω₁ ω₂ z - c) :=
    hm.sub (Meromorphic.const c)
  have hp : meromorphicOrderAt (weierstrassP ω₁ ω₂) 0 = ((-2 : ℤ) : WithTop ℤ) :=
    WeierstrassSeries.pole_order ω₁ ω₂ h₁ h₂ 0 (zero_mem _)
  have hpc : meromorphicOrderAt (fun z => weierstrassP ω₁ ω₂ z - c) 0 =
      ((-2 : ℤ) : WithTop ℤ) := by
    rw [(DivisorDegree.pole_order_sub_const (hm 0) c).2 (by rw [hp]; exact_mod_cast (by norm_num : (-2 : ℤ) < 0)), hp]
  have hfin := (hmc.meromorphicOn (s := Set.univ)).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ 0) (mem_univ a) (by rw [hpc]; simp)
  simpa only [sub_ne_zero] using
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmc a)).mp hfin

/-- The secant expression is symmetric even at its totalized exceptional values. -/
theorem additionExpression_comm (ω₁ ω₂ z w : ℂ) :
    additionExpression ω₁ ω₂ z w = additionExpression ω₁ ω₂ w z := by
  unfold additionExpression
  have h : (deriv (weierstrassP ω₁ ω₂) w - deriv (weierstrassP ω₁ ω₂) z) /
      (weierstrassP ω₁ ω₂ w - weierstrassP ω₁ ω₂ z) =
      (deriv (weierstrassP ω₁ ω₂) z - deriv (weierstrassP ω₁ ω₂) w) /
      (weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ w) := by
    rw [← neg_sub (deriv (weierstrassP ω₁ ω₂) z),
      ← neg_sub (weierstrassP ω₁ ω₂ z), neg_div_neg_eq]
  rw [h]
  ring

/-- Pointwise secant addition determines all punctured meromorphic germs. -/
theorem meromorphic_identity_of_addition_formula
    (hadd : Specs.D12Complex.Ch22.SecantAddition.addition_formula_type) :
    Specs.D12Complex.Ch22.SecantAddition.meromorphic_identity_type := by
  intro ω₁ ω₂ h₁ h₂ w hw
  have hm := WeierstrassSeries.meromorphic ω₁ ω₂ h₁ h₂
  have hleft : Meromorphic (fun z => weierstrassP ω₁ ω₂ (z + w)) :=
    Meromorphic.meromorphic_fun_comp_add_const_iff_meromorphic.mpr hm
  have hright : Meromorphic (fun z => additionExpression ω₁ ω₂ z w) := by
    unfold additionExpression
    exact (hm.neg.sub (Meromorphic.const _)).add
      (((hm.deriv.sub (Meromorphic.const _)).div (hm.sub (Meromorphic.const _))).pow.div
        (Meromorphic.const _))
  have he (a : ℂ) : (fun z => weierstrassP ω₁ ω₂ (z + w)) =ᶠ[𝓝[≠] a]
      (fun z => additionExpression ω₁ ω₂ z w) := by
    filter_upwards [WeierstrassEquations.eventually_notMem_lattice
      (WeierstrassSeries.periodPair h₁ h₂) a,
      eventually_wp_ne_const h₁ h₂ (weierstrassP ω₁ ω₂ w) a] with z hz hzw
    exact (hadd ω₁ ω₂ h₁ h₂ z w hz hw hzw).2
  refine ⟨⟨hleft, hright, he⟩, ?_⟩
  have hleft' : (fun z => weierstrassP ω₁ ω₂ (w + z)) =
      (fun z => weierstrassP ω₁ ω₂ (z + w)) := by
    funext z; rw [add_comm w z]
  have hright' :
      (fun z => Specs.D12Complex.Ch22.SecantAddition.additionExpression ω₁ ω₂ w z) =
      (fun z => additionExpression ω₁ ω₂ z w) := by
    funext z; exact additionExpression_comm ω₁ ω₂ w z
  rw [hleft', hright']
  exact ⟨hleft, hright, he⟩

end D12Complex.SecantAddition

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.SecantAddition
open TorusSurface
open Ch22.WeierstrassSeries (weierstrassP periodPair)

lemma deriv_eq_zero_of_nat_order_ge_two {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hz : f a = 0)
    (ho : 2 ≤ (meromorphicOrderAt f a).untop₀.toNat) : deriv f a = 0 := by
  by_contra hd
  have hao : analyticOrderAt f a = 1 := hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hd
  have hm : meromorphicOrderAt f a = (1 : ℤ) := by
    rw [hf.meromorphicOrderAt_eq, hao]
    rfl
  rw [hm] at ho
  norm_num at ho

lemma linePullback_deriv {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (m b : ℂ) {a : ℂ} (ha : a ∉ lattice ω₁ ω₂) :
    deriv (linePullback ω₁ ω₂ m b) a =
      6 * weierstrassP ω₁ ω₂ a ^ 2 -
        Specs.D12Complex.Ch22.WeierstrassEquations.g₂ ω₁ ω₂ / 2 -
        m * deriv (weierstrassP ω₁ ω₂) a := by
  let L := periodPair h₁ h₂
  have hp := (L.analyticOnNhd_weierstrassP a ha).differentiableAt.hasDerivAt
  have hq := (L.analyticOnNhd_weierstrassP a ha).deriv.differentiableAt.hasDerivAt
  have hd := (hq.sub (hp.const_mul m)).sub_const b
  have he : deriv (linePullback ω₁ ω₂ m b) a =
      deriv (deriv (weierstrassP ω₁ ω₂)) a - m * deriv (weierstrassP ω₁ ω₂) a := hd.deriv
  rw [he, Ch22.WeierstrassEquations.second_equation ω₁ ω₂ h₁ h₂ a ha]

end D12Complex.SecantAddition


noncomputable section
open Set Filter
open scoped Topology BigOperators Classical
namespace D12Complex.SecantAddition
open TorusSurface
open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)
open Specs.D12Complex.Ch22.WeierstrassEquations (g₂ g₃)
open Ch22.WeierstrassSeries (periodPair)
open Ch22.HalfPeriodValues
open TorusCubicBiholomorphism.Fibres

/-- The residual zero of the secant line, with its full multiplicity, is the
negative torus sum. Repeated zeros use the derivative of the pulled-back line. -/
lemma secant_data {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {z w : ℂ} (hz : z ∉ lattice ω₁ ω₂) (hw : w ∉ lattice ω₁ ω₂)
    (hneq : weierstrassP ω₁ ω₂ z ≠ weierstrassP ω₁ ω₂ w)
    (m b : ℂ)
    (hlz : m * weierstrassP ω₁ ω₂ z + b = deriv (weierstrassP ω₁ ω₂) z)
    (hlw : m * weierstrassP ω₁ ω₂ w + b = deriv (weierstrassP ω₁ ω₂) w) :
    z+w ∉ lattice ω₁ ω₂ ∧
    (∀ a : ℂ, meromorphicOrderAt (linePullback ω₁ ω₂ m b) a ≠ ⊤ ∧
      (meromorphicOrderAt (linePullback ω₁ ω₂ m b) a).untop₀.toNat =
        (Finsupp.single (projection ω₁ ω₂ z) 1 +
          Finsupp.single (projection ω₁ ω₂ w) 1 +
          Finsupp.single (-projection ω₁ ω₂ z - projection ω₁ ω₂ w) 1 :
            Torus ω₁ ω₂ →₀ ℕ) (projection ω₁ ω₂ a)) ∧
    weierstrassP ω₁ ω₂ (z+w) = m^2/4 - weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ w ∧
    deriv (weierstrassP ω₁ ω₂) (z+w) = -deriv (weierstrassP ω₁ ω₂) z +
      m * (weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ (z+w)) := by
  let p := weierstrassP ω₁ ω₂
  let π := projection ω₁ ω₂
  let v := -(z+w)
  have hz0 : linePullback ω₁ ω₂ m b z = 0 := by dsimp [linePullback]; linear_combination -hlz
  have hw0 : linePullback ω₁ ω₂ m b w = 0 := by dsimp [linePullback]; linear_combination -hlw
  obtain ⟨Z, hZ, htotal⟩ := linePullback_zero_divisor h₁ h₂ m b
  have hpos (a : ℂ) (ha : a ∉ lattice ω₁ ω₂) :
      0 < Z (π a) ↔ linePullback ω₁ ω₂ m b a = 0 := by
    rw [(hZ a).2, nat_order_pos (hZ a).1]
    exact (analytic_zero_iff_order_pos (linePullback_analyticAt h₁ h₂ m b ha)).symm
  have hpq : π z ≠ π w := by
    intro he
    exact hneq (wp_eq_of_projection_eq h₁ h₂ he)
  have hsum : Z.sum (fun t n => n • t) = 0 :=
    triple_pole_divisor_sum h₁ h₂ (linePullback_meromorphic h₁ h₂ m b)
      (linePullback_periodic h₁ h₂ m b)
      (fun a ha => linePullback_pole_order h₁ h₂ m b ha)
      (fun a ha => linePullback_analyticAt h₁ h₂ m b ha) Z (fun a => (hZ a).2)
  have hD : Z = Finsupp.single (π z) 1 + Finsupp.single (π w) 1 +
      Finsupp.single (-π z - π w) 1 :=
    three_divisor_third Z htotal ((hpos z hz).mpr hz0) ((hpos w hw).mpr hw0) hpq hsum
  have hvπ : π v = -π z - π w := by dsimp [v]; simp only [map_neg, map_add]; abel
  have hvpos : 0 < Z (π v) := by
    rw [hvπ, hD]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  have hZ0 : Z 0 = 0 := by
    have he := (hZ 0).2
    rw [linePullback_pole_order h₁ h₂ m b (zero_mem _)] at he
    norm_num at he
    exact he
  have hvnot : v ∉ lattice ω₁ ω₂ := by
    intro hv
    have hπ0 := (projection_zero_iff v).mpr hv
    change π v = 0 at hπ0
    rw [hπ0, hZ0] at hvpos
    omega
  have hsnot : z+w ∉ lattice ω₁ ω₂ := by
    intro hs
    exact hvnot (neg_mem hs)
  have hv0 : linePullback ω₁ ω₂ m b v = 0 := (hpos v hvnot).mp hvpos
  have hlv : m * p v + b = deriv p v := by
    change deriv p v - m * p v - b = 0 at hv0
    linear_combination -hv0
  have hc₁ : (m * p z + b)^2 = 4*(p z)^3 - g₂ ω₁ ω₂*p z - g₃ ω₁ ω₂ := by
    rw [hlz]; exact Ch22.WeierstrassEquations.first_equation ω₁ ω₂ h₁ h₂ z hz
  have hc₂ : (m * p w + b)^2 = 4*(p w)^3 - g₂ ω₁ ω₂*p w - g₃ ω₁ ω₂ := by
    rw [hlw]; exact Ch22.WeierstrassEquations.first_equation ω₁ ω₂ h₁ h₂ w hw
  have hcv : (m * p v + b)^2 = 4*(p v)^3 - g₂ ω₁ ω₂*p v - g₃ ω₁ ω₂ := by
    rw [hlv]; exact Ch22.WeierstrassEquations.first_equation ω₁ ω₂ h₁ h₂ v hvnot
  have hroot : p v = m^2/4 - p z - p w := by
    by_cases hvz : π v = π z
    · have hmult : 2 ≤ (meromorphicOrderAt (linePullback ω₁ ω₂ m b) z).untop₀.toNat := by
        rw [← (hZ z).2, hD, ← hvπ, hvz]
        dsimp only [π]
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]
        omega
      have hd0 := deriv_eq_zero_of_nat_order_ge_two (linePullback_analyticAt h₁ h₂ m b hz) hz0 hmult
      rw [linePullback_deriv h₁ h₂ m b hz] at hd0
      have ht := Algebra.third_eq_first_of_tangent (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)
        (p z) (p w) m b hc₁ hc₂ hneq (by rw [hlz]; exact hd0)
      exact (wp_eq_of_projection_eq h₁ h₂ hvz).trans ht.symm
    by_cases hvw : π v = π w
    · have hmult : 2 ≤ (meromorphicOrderAt (linePullback ω₁ ω₂ m b) w).untop₀.toNat := by
        rw [← (hZ w).2, hD, ← hvπ, hvw]
        dsimp only [π]
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]
        omega
      have hd0 := deriv_eq_zero_of_nat_order_ge_two (linePullback_analyticAt h₁ h₂ m b hw) hw0 hmult
      rw [linePullback_deriv h₁ h₂ m b hw] at hd0
      have ht := Algebra.third_eq_second_of_tangent (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)
        (p z) (p w) m b hc₁ hc₂ hneq (by rw [hlw]; exact hd0)
      exact (wp_eq_of_projection_eq h₁ h₂ hvw).trans ht.symm
    · apply Algebra.secant_root_eq (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) (p z) (p w) m b (p v)
        hc₁ hc₂ hneq hcv
      · intro hx
        exact hvz (wp_deriv_separates h₁ h₂ hvnot hz hx (by rw [← hlv, ← hlz, hx]))
      · intro hx
        exact hvw (wp_deriv_separates h₁ h₂ hvnot hw hx (by rw [← hlv, ← hlw, hx]))
  have hpeven : p v = p (z+w) := (periodPair h₁ h₂).weierstrassP_neg (z+w)
  have hpodd : deriv p v = -deriv p (z+w) := deriv_neg h₁ h₂ (z+w)
  refine ⟨hsnot, fun a => ⟨(hZ a).1, (hZ a).2.symm.trans (congrArg (fun D => D (π a)) hD)⟩,
    hpeven.symm.trans hroot, ?_⟩
  rw [hpeven, hpodd] at hlv
  change m * p (z+w) + b = -deriv p (z+w) at hlv
  change m * p z + b = deriv p z at hlz
  linear_combination hlv - hlz

end D12Complex.SecantAddition


noncomputable section
open Set Filter
open scoped Topology Classical
namespace D12Complex.SecantAddition
open TorusSurface CubicFiniteCharts
open TorusCubicLocalMap (phi phi_finite)
open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)
open Specs.D12Complex.Ch22.WeierstrassEquations (g₂ g₃)
open Ch22.WeierstrassSeries (periodPair)
open TorusCubicBiholomorphism.Fibres

theorem secant_intersections :
    Specs.D12Complex.Ch22.SecantAddition.secant_intersections_type := by
  intro ω₁ ω₂ h₁ h₂ z w hz hw hneq
  let p := weierstrassP ω₁ ω₂
  let m := (deriv p z - deriv p w) / (p z - p w)
  let b := deriv p z - m * p z
  have hlz : m * p z + b = deriv p z := by dsimp [b]; ring
  have hlw : m * p w + b = deriv p w :=
    Algebra.secant_incidence (p z) (deriv p z) (p w) (deriv p w) hneq
  obtain ⟨hsnot, hdiv, hx, hy⟩ := secant_data h₁ h₂ hz hw hneq m b hlz hlw
  refine ⟨hsnot, hdiv, ?_, hy, ?_, ?_⟩
  · have hvnot : -(z+w) ∉ lattice ω₁ ω₂ := by simpa only [neg_mem_iff] using hsnot
    have hcl : -projection ω₁ ω₂ z - projection ω₁ ω₂ w = projection ω₁ ω₂ (-(z+w)) := by
      simp only [map_neg, map_add]; abel
    have heven : weierstrassP ω₁ ω₂ (-(z+w)) = weierstrassP ω₁ ω₂ (z+w) :=
      (periodPair h₁ h₂).weierstrassP_neg (z+w)
    rw [hcl, phi_finite h₁ h₂ hvnot]
    exact congrArg₂ affinePoint heven (deriv_neg h₁ h₂ (z+w))
  · have hc₁ : (m*p z+b)^2 = 4*(p z)^3 - g₂ ω₁ ω₂*p z - g₃ ω₁ ω₂ := by
      rw [hlz]; exact Ch22.WeierstrassEquations.first_equation ω₁ ω₂ h₁ h₂ z hz
    have hc₂ : (m*p w+b)^2 = 4*(p w)^3 - g₂ ω₁ ω₂*p w - g₃ ω₁ ω₂ := by
      rw [hlw]; exact Ch22.WeierstrassEquations.first_equation ω₁ ω₂ h₁ h₂ w hw
    intro x
    rw [hx]
    exact Algebra.cubic_secant_factorization (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) (p z) (p w) m b hc₁ hc₂ hneq x
  · rw [← map_add, phi_finite h₁ h₂ hsnot, hy]

theorem addition_formula : Specs.D12Complex.Ch22.SecantAddition.addition_formula_type := by
  intro ω₁ ω₂ h₁ h₂ z w hz hw hneq
  let p := weierstrassP ω₁ ω₂
  let m := (deriv p z - deriv p w) / (p z - p w)
  let b := deriv p z - m * p z
  have hlz : m * p z + b = deriv p z := by dsimp [b]; ring
  have hlw : m * p w + b = deriv p w :=
    Algebra.secant_incidence (p z) (deriv p z) (p w) (deriv p w) hneq
  obtain ⟨hsnot, _, hx, _⟩ := secant_data h₁ h₂ hz hw hneq m b hlz hlw
  refine ⟨hsnot, ?_⟩
  rw [hx]
  change m^2/4 - p z - p w = -p z - p w + m^2/4
  ring

theorem meromorphic_identity : Specs.D12Complex.Ch22.SecantAddition.meromorphic_identity_type :=
  meromorphic_identity_of_addition_formula addition_formula

end D12Complex.SecantAddition
