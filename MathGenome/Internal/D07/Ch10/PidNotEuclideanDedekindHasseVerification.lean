import MathGenome.Internal.Specs.D07.Ch10.PidNotEuclideanDedekindHasseVerification
import MathGenome.Internal.D07.Ch10.PidNotEuclideanQuadraticIntegerNorm
import MathGenome.Internal.D07.Ch10.DedekindHasseSufficient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases

/-! The Dedekind–Hasse construction for the complex ring of discriminant -19.
The denominator estimates follow paper.tex:2091–2121. Rationalization and gcd
reduction are proved here; the PID implication uses the independent upstream
sufficient criterion, rather than presupposing ideal principality. -/

noncomputable section
namespace D07.Ch10.PidNotEuclideanDedekindHasseVerification
open PidNotEuclideanQuadraticIntegerNorm

lemma sqrtMinus19_sq : sqrtMinus19 ^ 2 = (-19 : ℂ) := squareRootPresentation.1

lemma quadratic_mem (a b : ℤ) : (a : ℂ) + (b : ℂ) * sqrtMinus19 ∈ integerRing := by
  apply (coordinateMembership _).2
  refine ⟨a - b, 2 * b, ?_⟩
  simp only [expression, omega, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  ring

lemma half_quadratic_mem (a b : ℤ) (h : a % 2 = b % 2) :
    ((a : ℂ) + (b : ℂ) * sqrtMinus19) / 2 ∈ integerRing := by
  have hd : 2 ∣ a - b := by omega
  apply (coordinateMembership _).2
  refine ⟨(a-b)/2, b, ?_⟩
  have he : (a-b)/2 * 2 = a-b := Int.ediv_mul_cancel hd
  have hc : (((a-b)/2 : ℤ) : ℂ) * 2 = (a : ℂ) - b := by exact_mod_cast he
  simp only [expression, omega]
  linear_combination -hc / 2

lemma primitive_bezout (A B c : ℤ) (h : Primitive A B c) :
    ∃ x y h : ℤ, A*x+B*y+c*h = 1 := by
  have h₁ := Int.gcd_eq_gcd_ab A B
  have h₂ := Int.gcd_eq_gcd_ab (Int.gcd A B : ℤ) c
  change Int.gcd (Int.gcd A B : ℤ) c = 1 at h
  rw [h] at h₂
  refine ⟨Int.gcdA A B * Int.gcdA (Int.gcd A B : ℤ) c,
    Int.gcdB A B * Int.gcdA (Int.gcd A B : ℤ) c,
    Int.gcdB (Int.gcd A B : ℤ) c, ?_⟩
  linear_combination -h₁ * Int.gcdA (Int.gcd A B : ℤ) c - h₂

lemma quotient_not_mem (a b : R) (hb : b ≠ 0) (h : ¬ b ∣ a) :
    (a : ℂ) / (b : ℂ) ∉ integerRing := by
  intro hz
  apply h
  refine ⟨⟨_, hz⟩, ?_⟩
  apply Subtype.ext
  change (a : ℂ) = (b : ℂ) * ((a : ℂ) / (b : ℂ))
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  field_simp

lemma normSq_quadraticFraction (A B c : ℤ) :
    Complex.normSq (quadraticFraction A B c) =
      ((A : ℝ)^2 + 19 * (B : ℝ)^2) / (c : ℝ)^2 := by
  simp only [quadraticFraction, map_div₀]
  congr 1
  · simp [Complex.normSq_apply, sqrtMinus19, pow_two]
    nlinarith [sqrt19_sq]
  · simp [Complex.normSq_apply, pow_two]

lemma quadratic_mul_conj (A B : ℤ) :
    ((A : ℂ) + (B : ℂ) * sqrtMinus19) *
      ((A : ℂ) - (B : ℂ) * sqrtMinus19) = ((A^2 + 19*B^2 : ℤ) : ℂ) := by
  push_cast
  linear_combination -(B : ℂ)^2 * sqrtMinus19_sq

lemma small_rational_difference (z : ℂ) (s t : R) (r c : ℤ)
    (hr : 0 < r) (hc : r < c)
    (he : z * (s : ℂ) - (t : ℂ) = (r : ℂ) / (c : ℂ)) : HasSmallRemainder z := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (lt_trans hr hc)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hrc : (r : ℝ) < c := by exact_mod_cast hc
  refine ⟨s, t, ?_, ?_⟩ <;>
    rw [he, map_div₀] <;> simp only [Complex.normSq_intCast, ← pow_two]
  · exact div_pos (sq_pos_of_pos hr0) (sq_pos_of_pos hc0)
  · apply (div_lt_one (sq_pos_of_pos hc0)).2
    nlinarith

lemma conjugate_remainder (A B c q r : ℤ) (hr : 0 < r) (hc : r < c)
    (he : A^2 + 19*B^2 = c*q+r) : HasSmallRemainder (quadraticFraction A B c) := by
  let s : R := ⟨(A : ℂ) - (B : ℂ) * sqrtMinus19, by simpa [sub_eq_add_neg] using quadratic_mem A (-B)⟩
  let t : R := q
  apply small_rational_difference _ s t r c hr hc
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans hr hc))
  change quadraticFraction A B c * ((A : ℂ) - (B : ℂ) * sqrtMinus19) - q = _
  unfold quadraticFraction
  rw [div_mul_eq_mul_div, quadratic_mul_conj]
  have hec : ((A^2+19*B^2 : ℤ) : ℂ) = (c : ℂ)*q+r := by exact_mod_cast he
  rw [hec]
  field_simp
  ring

theorem denominatorTwo : Specs.DenominatorTwo := by
  intro A B _hprim hnot
  have hp : (A-1) % 2 = B % 2 := by
    have hn : A % 2 ≠ B % 2 := by
      intro h
      exact hnot (half_quadratic_mem A B h)
    omega
  let t : R := ⟨((A-1 : ℤ) + (B : ℂ)*sqrtMinus19)/2, half_quadratic_mem (A-1) B hp⟩
  apply small_rational_difference _ 1 t 1 2 (by norm_num) (by norm_num)
  change quadraticFraction A B 2 * 1 - (((A-1 : ℤ) + (B : ℂ)*sqrtMinus19)/2) = _
  simp only [quadraticFraction, Int.cast_sub, Int.cast_one, Int.cast_ofNat]
  ring

theorem denominatorThree : Specs.DenominatorThree := by
  intro A B hp
  obtain ⟨x,y,h,hbez⟩ := primitive_bezout A B 3 hp
  have hn : (A^2 + 19*B^2) % 3 ≠ 0 := by
    intro he
    have hab : A % 3 = 0 ∧ B % 3 = 0 := by
      have ha0 := Int.emod_nonneg A (by norm_num : (3 : ℤ) ≠ 0)
      have hb0 := Int.emod_nonneg B (by norm_num : (3 : ℤ) ≠ 0)
      have ha1 := Int.emod_lt_of_pos A (by norm_num : (0 : ℤ) < 3)
      have hb1 := Int.emod_lt_of_pos B (by norm_num : (0 : ℤ) < 3)
      have hm : ((A%3)^2 + 19*(B%3)^2)%3 = 0 := by
        simpa [Int.add_emod, Int.mul_emod, pow_two] using he
      interval_cases A % 3 <;> interval_cases B % 3 <;> norm_num at *
    obtain ⟨ha,hb⟩ := hab
    have hd : 3 ∣ A*x+B*y+3*h := by
      exact dvd_add (dvd_add (dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero ha) x)
        (dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero hb) y)) (dvd_mul_right 3 h)
    rw [hbez] at hd
    norm_num at hd
  apply conjugate_remainder A B 3 ((A^2+19*B^2)/3) ((A^2+19*B^2)%3)
  · have := Int.emod_nonneg (A^2+19*B^2) (by norm_num : (3 : ℤ) ≠ 0); omega
  · exact Int.emod_lt_of_pos _ (by norm_num)
  · omega

theorem denominatorFourOpposite : Specs.DenominatorFourOpposite := by
  intro A B hp
  have hn : (A^2+19*B^2)%2 = 1 := by
    have he : (A^2+19*B^2)%2 = ((A%2)^2+19*(B%2)^2)%2 := by
      simp [Int.add_emod, Int.mul_emod, pow_two]
    rw [he]
    have ha0 := Int.emod_nonneg A (by norm_num : (2 : ℤ) ≠ 0)
    have ha1 := Int.emod_lt_of_pos A (by norm_num : (0 : ℤ) < 2)
    have hb0 := Int.emod_nonneg B (by norm_num : (2 : ℤ) ≠ 0)
    have hb1 := Int.emod_lt_of_pos B (by norm_num : (0 : ℤ) < 2)
    interval_cases A%2 <;> interval_cases B%2 <;> norm_num at *
  apply conjugate_remainder A B 4 ((A^2+19*B^2)/4) ((A^2+19*B^2)%4)
  · omega
  · exact Int.emod_lt_of_pos _ (by norm_num)
  · omega

lemma odd_square_mod_eight (A : ℤ) (ha : A%2 = 1) : A^2 % 8 = 1 := by
  have he : A^2 % 8 = (A%8)^2 % 8 := by simp [pow_two, Int.mul_emod]
  rw [he]
  have ha0 := Int.emod_nonneg A (by norm_num : (8 : ℤ) ≠ 0)
  have ha1 := Int.emod_lt_of_pos A (by norm_num : (0 : ℤ) < 8)
  have ha2 : A%8%2 = 1 := by omega
  interval_cases A%8 <;> norm_num at *

theorem denominatorFourOdd : Specs.DenominatorFourOdd := by
  intro A B ha hb
  have hA := odd_square_mod_eight A ha
  have hB := odd_square_mod_eight B hb
  have hn : (A^2+19*B^2)%8 = 4 := by
    norm_num [Int.add_emod, Int.mul_emod, hA, hB]
  let q := (A^2+19*B^2)/8
  have he : A^2+19*B^2 = 8*q+4 := by omega
  let s : R := ⟨((A : ℂ) - (B : ℂ)*sqrtMinus19)/2, by
    simpa [sub_eq_add_neg] using half_quadratic_mem A (-B) (by omega)⟩
  let t : R := q
  apply small_rational_difference _ s t 1 2 (by norm_num) (by norm_num)
  change quadraticFraction A B 4 * (((A : ℂ) - (B : ℂ)*sqrtMinus19)/2) - q = _
  have hec : ((A^2+19*B^2 : ℤ) : ℂ) = 8*(q : ℂ)+4 := by exact_mod_cast he
  unfold quadraticFraction
  rw [div_mul_div_comm, quadratic_mul_conj, hec]
  norm_num
  ring

/-- Division by a nearest integer multiple, with an integral bound valid at c=5. -/
lemma nearest_multiple (v c : ℤ) (hc : 0 < c) :
    ∃ q r : ℤ, v = c*q+r ∧ 2*|r| ≤ c := by
  have h0 := Int.emod_nonneg v (ne_of_gt hc)
  have h1 := Int.emod_lt_of_pos v hc
  have hdiv := Int.mul_ediv_add_emod v c
  by_cases h : 2*(v%c) ≤ c
  · refine ⟨v/c, v%c, by omega, ?_⟩
    rw [abs_of_nonneg h0]
    exact h
  · refine ⟨v/c+1, v%c-c, by nlinarith [Int.mul_ediv_add_emod v c], ?_⟩
    rw [abs_of_neg (by omega)]
    omega

lemma large_denominator_bound (r c : ℤ) (hc : 5 ≤ c) (hr : 2*|r| ≤ c) :
    0 < r^2+19 ∧ r^2+19 < c^2 := by
  constructor
  · nlinarith [sq_nonneg r]
  · have hc0 : 0 ≤ c := by omega
    have habs : 0 ≤ |r| := abs_nonneg r
    have hs : 4*r^2 ≤ c^2 := by
      nlinarith [sq_abs r, mul_nonneg (by omega : 0 ≤ c-2*|r|) (by omega : 0 ≤ c+2*|r|)]
    by_cases he : c = 5
    · subst c
      have hl : -2 ≤ r ∧ r ≤ 2 := abs_le.mp (by omega)
      nlinarith [mul_nonneg (by omega : 0 ≤ 2-r) (by omega : 0 ≤ r+2)]
    · have : 6 ≤ c := by omega
      nlinarith [sq_nonneg (c-6)]

theorem largeDenominator : Specs.LargeDenominator := by
  intro A B c hc hp
  obtain ⟨x,y,h,hbez⟩ := primitive_bezout A B c hp
  obtain ⟨q,r,hqr,hr⟩ := nearest_multiple (A*y-19*B*x) c (by omega)
  let s : R := ⟨(y : ℂ)+(x : ℂ)*sqrtMinus19, quadratic_mem y x⟩
  let t : R := ⟨(q : ℂ)-(h : ℂ)*sqrtMinus19, by
    simpa [sub_eq_add_neg] using quadratic_mem q (-h)⟩
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (show c ≠ 0 by omega)
  have he : quadraticFraction A B c * (s : ℂ) - (t : ℂ) = quadraticFraction r 1 c := by
    have hbez' : (A : ℂ)*x+(B : ℂ)*y+(c : ℂ)*h = 1 := by exact_mod_cast hbez
    have hqr' : (A : ℂ)*y-19*(B : ℂ)*x = (c : ℂ)*q+r := by exact_mod_cast hqr
    change quadraticFraction A B c * ((y : ℂ)+(x : ℂ)*sqrtMinus19) -
      ((q : ℂ)-(h : ℂ)*sqrtMinus19) = quadraticFraction r 1 c
    unfold quadraticFraction
    push_cast
    field_simp
    linear_combination (B : ℂ)*(x : ℂ)*sqrtMinus19_sq + sqrtMinus19*hbez' + hqr'
  obtain ⟨hpos,hlt⟩ := large_denominator_bound r c hc hr
  have hpos' : (0 : ℝ) < (r : ℝ)^2+19 := by exact_mod_cast hpos
  have hlt' : (r : ℝ)^2+19 < (c : ℝ)^2 := by exact_mod_cast hlt
  have hcsq : (0 : ℝ) < (c : ℝ)^2 := by exact_mod_cast (show (0 : ℤ) < c^2 by nlinarith)
  refine ⟨s,t,?_,?_⟩ <;> rw [he, normSq_quadraticFraction] <;> norm_num only [Int.cast_one, one_pow, mul_one]
  · exact div_pos hpos' hcsq
  · exact (div_lt_one hcsq).2 hlt'

/-- Clear the common gcd of three integer coordinates. -/
lemma reduce_quadraticFraction (A B c : ℤ) (hc : 0 < c) :
    ∃ A' B' c' : ℤ, 0 < c' ∧ Primitive A' B' c' ∧
      quadraticFraction A B c = quadraticFraction A' B' c' := by
  let d := Int.gcd (Int.gcd A B : ℤ) c
  have hd : 0 < d := Int.gcd_pos_iff.mpr (Or.inr (ne_of_gt hc))
  have hd0 : (0 : ℤ) < d := by exact_mod_cast hd
  have hdg : (d : ℤ) ∣ (Int.gcd A B : ℤ) := Int.gcd_dvd_left _ _
  have hdA : (d : ℤ) ∣ A := dvd_trans hdg (Int.gcd_dvd_left _ _)
  have hdB : (d : ℤ) ∣ B := dvd_trans hdg (Int.gcd_dvd_right _ _)
  have hdC : (d : ℤ) ∣ c := Int.gcd_dvd_right _ _
  have hc' : 0 < c / (d : ℤ) := Int.ediv_pos_of_pos_of_dvd hc hd0.le hdC
  refine ⟨A/d, B/d, c/d, hc', ?_, ?_⟩
  · unfold Primitive
    rw [Int.gcd_ediv hdA hdB, Int.natAbs_natCast, Int.natCast_ediv]
    exact Int.gcd_ediv_gcd_ediv_gcd hd
  · have hA : ((A/(d:ℤ) : ℤ) : ℂ)*(d:ℂ) = (A:ℂ) := by
      exact_mod_cast Int.ediv_mul_cancel hdA
    have hB : ((B/(d:ℤ) : ℤ) : ℂ)*(d:ℂ) = (B:ℂ) := by
      exact_mod_cast Int.ediv_mul_cancel hdB
    have hC : ((c/(d:ℤ) : ℤ) : ℂ)*(d:ℂ) = (c:ℂ) := by
      exact_mod_cast Int.ediv_mul_cancel hdC
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
    have hc'0 : ((c/(d:ℤ) : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc')
    unfold quadraticFraction
    apply (div_eq_div_iff hc0 hc'0).2
    linear_combination ((c/(d:ℤ) : ℤ) : ℂ)*(-hA-sqrtMinus19*hB) +
      (((A/(d:ℤ) : ℤ) : ℂ)+((B/(d:ℤ) : ℤ) : ℂ)*sqrtMinus19)*hC

lemma conjugate_mem (z : R) : star (z : ℂ) ∈ integerRing := by
  obtain ⟨a,b,hz⟩ := (coordinateMembership (z : ℂ)).mp z.property
  apply (coordinateMembership _).2
  refine ⟨a+b, -b, ?_⟩
  rw [hz]
  apply Complex.ext <;> simp [expression_re, expression_im] <;> ring

/-- Rationalization supplies integer coordinates before their common gcd is removed. -/
lemma fraction_integer_coordinates (a b : R) (hb : b ≠ 0) :
    ∃ A B c : ℤ, 0 < c ∧ (a : ℂ)/(b : ℂ) = quadraticFraction A B c := by
  let bconj : R := ⟨star (b : ℂ), conjugate_mem b⟩
  obtain ⟨u,v,hnum⟩ := (coordinateMembership ((a*bconj : R) : ℂ)).mp (a*bconj).property
  change (a : ℂ)*star (b : ℂ) = expression u v at hnum
  have hnum' : ((2*u+v : ℤ) : ℂ)+(v : ℂ)*sqrtMinus19 =
      2*((a : ℂ)*star (b : ℂ)) := by
    rw [hnum]
    simp only [expression, omega, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    ring
  have hNb := positiveNorm.2.2 b hb
  refine ⟨2*u+v, v, 2*PidNotEuclideanQuadraticIntegerNorm.norm b, by omega, ?_⟩
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have hN0 : ((2*PidNotEuclideanQuadraticIntegerNorm.norm b : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (2*PidNotEuclideanQuadraticIntegerNorm.norm b : ℤ) ≠ 0 by omega)
  unfold quadraticFraction
  apply (div_eq_div_iff hb0 hN0).2
  rw [hnum']
  push_cast
  rw [normConjugate b]
  ring

theorem reducedRepresentation : Specs.ReducedRepresentation := by
  intro a b hb hdiv
  obtain ⟨A,B,c,hc,hrep⟩ := fraction_integer_coordinates a b hb
  obtain ⟨A',B',c',hc',hp,hred⟩ := reduce_quadraticFraction A B c hc
  refine ⟨A',B',c',?_,hp,hrep.trans hred⟩
  have hn := quotient_not_mem a b hb hdiv
  have hne : c' ≠ 1 := by
    intro he
    rw [hrep, hred, he] at hn
    apply hn
    simpa [quadraticFraction] using quadratic_mem A' B'
  omega

theorem fractionApproximation : Specs.FractionApproximation := by
  intro a b hb hdiv
  obtain ⟨A,B,c,hc,hp,hrep⟩ := reducedRepresentation a b hb hdiv
  rw [hrep]
  by_cases hc5 : 5 ≤ c
  · exact largeDenominator A B c hc5 hp
  have hcCases : c = 2 ∨ c = 3 ∨ c = 4 := by omega
  rcases hcCases with rfl | rfl | rfl
  · apply denominatorTwo A B hp
    rw [← hrep]
    exact quotient_not_mem a b hb hdiv
  · exact denominatorThree A B hp
  · by_cases hpar : A%2 = B%2
    · have ha : A%2 = 1 := by
        obtain ⟨x,y,h,hbez⟩ := primitive_bezout A B 4 hp
        have he : A%2 = 0 → B%2 = 0 → (A*x+B*y+4*h)%2 = 0 := by
          intros ha hb
          simp [Int.add_emod, Int.mul_emod, ha, hb]
        have hnot : A%2 ≠ 0 := by
          intro ha
          have hm := he ha (hpar ▸ ha)
          rw [hbez] at hm
          norm_num at hm
        omega
      exact denominatorFourOdd A B ha (hpar ▸ ha)
    · exact denominatorFourOpposite A B hpar

theorem dedekindHasseVerification : Specs.DedekindHasseVerification := by
  intro a b _ha hb hdiv
  obtain ⟨s,t,hpos,hlt⟩ := fractionApproximation a b hb hdiv
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have hid : ((s*a-t*b : R) : ℂ) =
      ((a : ℂ)/(b : ℂ)*(s : ℂ)-(t : ℂ))*(b : ℂ) := by
    push_cast
    field_simp
  have hbpos : 0 < Complex.normSq (b : ℂ) := Complex.normSq_pos.mpr hb0
  have hn : (PidNotEuclideanQuadraticIntegerNorm.norm (s*a-t*b) : ℝ) =
      Complex.normSq ((a : ℂ)/(b : ℂ)*(s : ℂ)-(t : ℂ))*Complex.normSq (b : ℂ) := by
    rw [norm_cast, hid, map_mul]
  refine ⟨s,t,?_,?_⟩
  · exact_mod_cast (show (0 : ℝ) < (PidNotEuclideanQuadraticIntegerNorm.norm (s*a-t*b) : ℝ) by
      rw [hn]; exact mul_pos hpos hbpos)
  · exact_mod_cast (show (PidNotEuclideanQuadraticIntegerNorm.norm (s*a-t*b) : ℝ) < (PidNotEuclideanQuadraticIntegerNorm.norm b : ℝ) by
      rw [hn, norm_cast]
      nlinarith)

theorem principalIdealDomain : Specs.PrincipalIdealDomain := by
  apply D07.Ch10.DedekindHasseSufficient.dedekind_hasse_pid R (fun x => (PidNotEuclideanQuadraticIntegerNorm.norm x).toNat)
  · simp [multiplicativeNorm.1]
  · intro x hx
    exact Int.pos_iff_toNat_pos.mp (positiveNorm.2.2 x hx)
  · intro a b ha hb hdiv
    obtain ⟨s,t,hpos,hlt⟩ := dedekindHasseVerification a b ha hb hdiv
    exact ⟨s,t,Int.pos_iff_toNat_pos.mp hpos, (Int.toNat_lt_toNat (positiveNorm.2.2 b hb)).2 hlt⟩

end D07.Ch10.PidNotEuclideanDedekindHasseVerification
