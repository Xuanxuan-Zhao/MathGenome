import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.QuadraticUnitRoots
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch02.SimpleRootLifting
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch02.LegendreGauss
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch02.TwoPowerUnits
import Batteries.Tactic.OpenPrivate

noncomputable section
namespace P203.Ch02
open P203Specs.Ch02 P203Specs.Ch02.UnitQuadratic

namespace UnitQuadratic
open private expression_injective from MathGenome.Internal.ElementaryNumberTheory.P203.Ch02.TwoPowerUnits

/-- Evaluation of the quadratic polynomial used for Hensel lifting. -/
private def squarePolynomial (a : ℤ) : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C a

private theorem squarePolynomial_eval (a x : ℤ) :
    (squarePolynomial a).eval x = x ^ 2 - a := by simp [squarePolynomial]

private theorem squarePolynomial_derivative (a x : ℤ) :
    (squarePolynomial a).derivative.eval x = 2 * x := by
  simp [squarePolynomial, Polynomial.derivative_pow]

/-- Each root modulo an odd prime lifts uniquely to every positive power.
This statement concerns residue classes rather than chosen lift parameters. -/
theorem quadratic_root_unique_lift (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ℤ) (ha : ¬(p : ℤ) ∣ a) (x : ℤ) (hx : (p : ℤ) ∣ x ^ 2 - a)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ r : ℤ, (p : ℤ)^j ∣ r^2-a ∧ (p : ℤ) ∣ r-x ∧
      ∀ b : ℤ, (p : ℤ) ∣ b-x →
        ((p : ℤ)^j ∣ b^2-a ↔ (p : ℤ)^j ∣ b-r) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hxunit : ¬(p : ℤ) ∣ x := by
    intro h
    apply ha
    have hsq : (p : ℤ) ∣ x ^ 2 := dvd_pow h (by decide)
    simpa using dvd_sub hsq hx
  have htwo : ¬(p : ℤ) ∣ (2 : ℤ) := by
    intro h
    have hnat : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hnat)
  have hD : ¬(p : ℤ) ∣ (squarePolynomial a).derivative.eval x := by
    rw [squarePolynomial_derivative]
    exact fun h => (hpZ.dvd_mul.mp h).elim htwo hxunit
  obtain ⟨r, _, hvalid, _, huniq⟩ := simpleRootTower p hp (squarePolynomial a) x
    (by simpa only [squarePolynomial_eval] using hx) hD
  refine ⟨r (j-1), ?_, (hvalid (j-1)).2.1, ?_⟩
  · simpa only [Nat.sub_add_cancel hj, squarePolynomial_eval] using (hvalid (j-1)).1
  · intro b hb
    simpa only [Nat.sub_add_cancel hj, squarePolynomial_eval] using huniq (j-1) b hb

/-- Integer congruences and roots in the ordinary residue ring agree. -/
theorem quadratic_root_iff (m : ℕ) (a x : ℤ) :
    (x : ZMod m)^2 = (a : ZMod m) ↔ (m : ℤ) ∣ x^2-a := by
  rw [← Int.cast_pow, ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
  exact dvd_sub_comm

private def rootReduction (p j : ℕ) (hj : 1 ≤ j) (a : ℤ) :
    QuadraticRoots (p^j) a → QuadraticRoots p a := fun x =>
  ⟨ZMod.castHom (dvd_pow_self p (by omega : j ≠ 0)) (ZMod p) x.val, by
    have h := congrArg (ZMod.castHom (dvd_pow_self p (by omega : j ≠ 0)) (ZMod p)) x.property
    simpa only [map_pow, map_intCast] using h⟩

/-- Reduction is a bijection on unit quadratic roots for odd primes. -/
theorem quadratic_root_reduction_bijective (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (j : ℕ) (hj : 1 ≤ j) (a : ℤ) (ha : ¬(p : ℤ) ∣ a) :
    Function.Bijective (rootReduction p j hj a) := by
  have hpow : ((p^j : ℕ) : ℤ) = (p : ℤ)^j := by simp
  constructor
  · intro u v huv
    obtain ⟨x, hx⟩ := ZMod.intCast_surjective u.val
    obtain ⟨y, hy⟩ := ZMod.intCast_surjective v.val
    have hxroot : (p : ℤ)^j ∣ x^2-a := by
      simpa only [hpow] using (quadratic_root_iff (p^j) a x).mp (hx ▸ u.property)
    have hyroot : (p : ℤ)^j ∣ y^2-a := by
      simpa only [hpow] using (quadratic_root_iff (p^j) a y).mp (hy ▸ v.property)
    have hxy : (p : ℤ) ∣ y-x := by
      have h := congrArg Subtype.val huv
      change ZMod.castHom _ (ZMod p) u.val = ZMod.castHom _ (ZMod p) v.val at h
      rw [← hx, ← hy, map_intCast, map_intCast] at h
      have hh := (ZMod.intCast_eq_intCast_iff y x p).mp h.symm
      simpa only [neg_sub] using (Int.modEq_iff_dvd.mp hh).neg_right
    have hxlow : (p : ℤ) ∣ x^2-a :=
      (dvd_pow_self _ (by omega : j ≠ 0)).trans hxroot
    obtain ⟨r, _, _, hr⟩ := quadratic_root_unique_lift p hp hp2 a ha x hxlow j hj
    have hxcong := (hr x (by simp)).mp hxroot
    have hycong := (hr y hxy).mp hyroot
    apply Subtype.ext
    rw [← hx, ← hy]
    apply (ZMod.intCast_eq_intCast_iff x y (p^j)).mpr
    apply Int.modEq_iff_dvd.mpr
    rw [hpow]
    convert dvd_sub hycong hxcong using 1; ring
  · intro u
    obtain ⟨x, hx⟩ := ZMod.intCast_surjective u.val
    have hxroot : (p : ℤ) ∣ x^2-a :=
      (quadratic_root_iff p a x).mp (hx ▸ u.property)
    obtain ⟨r, hr, hrx, _⟩ := quadratic_root_unique_lift p hp hp2 a ha x hxroot j hj
    refine ⟨⟨(r : ZMod (p^j)), (quadratic_root_iff (p^j) a r).mpr ?_⟩, ?_⟩
    · simpa only [hpow] using hr
    · apply Subtype.ext
      change ZMod.castHom _ (ZMod p) (r : ZMod (p^j)) = u.val
      rw [map_intCast, ← hx]
      apply (ZMod.intCast_eq_intCast_iff r x p).mpr
      apply Int.modEq_iff_dvd.mpr
      simpa only [neg_sub] using hrx.neg_right

theorem oddPrimeUnitRootCount : OddPrimeUnitRootCount := by
  classical
  intro p hp hp2 j hj a ha
  let : Fact p.Prime := ⟨hp⟩
  have hcount : quadraticRootCount (p^j) a = quadraticRootCount p a :=
    Nat.card_eq_of_bijective _ (quadratic_root_reduction_bijective p hp hp2 j hj a ha)
  rw [hcount]
  have hformula : (quadraticRootCount p a : ℤ) = P203Specs.Ch02.legendreSymbol a p + 1 := by
    change (Nat.card ↥{x : ZMod p | x^2 = (a : ZMod p)} : ℤ) = _
    rw [Nat.card_eq_card_toFinset]
    rw [show P203Specs.Ch02.legendreSymbol a p = legendreSym p a from symbol_eq_mathlib p a]
    exact legendreSym.card_sqrts p hp2 a
  unfold P203Specs.Ch02.legendreSymbol at *
  rw [ite_eq_right ha] at *
  split_ifs at * <;> omega

/-- The count depends only on the residue class of the right hand side. -/
theorem quadraticRootCount_congr (m : ℕ) (a b : ℤ)
    (h : (a : ZMod m) = (b : ZMod m)) :
    quadraticRootCount m a = quadraticRootCount m b := by
  unfold quadraticRootCount QuadraticRoots
  rw [h]

theorem twoUnitRootCount : TwoUnitRootCount := by
  intro a ha
  have ha0 : (a : ZMod 2) ≠ 0 := by
    exact fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp h)
  have ha1 : (a : ZMod 2) = 1 := by
    have h : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact h _ ha0
  rw [quadraticRootCount_congr 2 a 1 (by simpa using ha1)]
  change Nat.card {y : ZMod 2 // y^2 = (1 : ℤ)} = 1
  rw [Nat.card_eq_fintype_card]
  decide

theorem fourUnitRootCount : FourUnitRootCount := by
  classical
  intro a ha
  have ha2 : (a : ZMod 2) ≠ 0 := by
    exact fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp h)
  have hred : (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) (a : ZMod 4) ≠ 0 := by
    simpa only [map_intCast] using ha2
  have hcases : (a : ZMod 4) = 1 ∨ (a : ZMod 4) = 3 := by
    have h : ∀ x : ZMod 4,
        (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) x ≠ 0 → x = 1 ∨ x = 3 := by decide
    exact h _ hred
  have hcong : a ≡ 1 [ZMOD 4] ↔ (a : ZMod 4) = 1 := by
    simpa using (ZMod.intCast_eq_intCast_iff a 1 4).symm
  simp only [hcong]
  rcases hcases with h | h
  · rw [ite_eq_left h, quadraticRootCount_congr 4 a 1 (by simpa using h)]
    change Nat.card {y : ZMod 4 // y^2 = (1 : ℤ)} = 2
    rw [Nat.card_eq_fintype_card]
    decide
  · have hne : (a : ZMod 4) ≠ 1 := by rw [h]; decide
    rw [ite_eq_right hne, quadraticRootCount_congr 4 a 3 (by simpa using h)]
    change Nat.card {y : ZMod 4 // y^2 = (3 : ℤ)} = 0
    rw [Nat.card_eq_fintype_card]
    decide

/-- Squaring the two-power parametrization removes its sign. -/
private theorem twoPowerExpression_sq (k a b : ℕ) :
    (twoPowerExpression k a b)^2 = (5 : ZMod (2^k))^(2*b) := by
  unfold twoPowerExpression
  rw [mul_pow, ← pow_mul, Nat.mul_comm a 2, pow_mul,
    neg_one_sq, one_pow, one_mul, ← pow_mul, Nat.mul_comm b 2]

/-- Within the bounded exponent interval there are exactly two exponents
annihilated by doubling. This includes k = 3, when the interval has length two. -/
private theorem exponent_square_one (k : ℕ) (hk : 3 ≤ k)
    (b : Fin (2^(k-2))) :
    (5 : ZMod (2^k))^(2*b.val) = 1 ↔ b.val = 0 ∨ b.val = 2^(k-3) := by
  rw [← orderOf_dvd_iff_pow_eq_one, twoPowerFiveOrder k hk]
  have hpow : 2^(k-2) = 2 * 2^(k-3) := by
    rw [show k-2 = k-3+1 by omega, pow_succ, Nat.mul_comm]
  conv_lhs => lhs; rw [hpow]
  rw [Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)]
  have hb : b.val < 2 * 2^(k-3) := lt_of_lt_of_eq b.isLt hpow
  constructor
  · rintro ⟨c, hc⟩
    have hpos : 0 < 2^(k-3) := by positivity
    have hc2 : c < 2 := by nlinarith
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> simp_all
  · rintro (h | h) <;> rw [h]; simp

private def kernelParameter (k : ℕ) (hk : 3 ≤ k)
    (q : Fin 2 × Fin 2) : QuadraticRoots (2^k) 1 :=
  ⟨twoPowerExpression k q.1.val (q.2.val * 2^(k-3)), by
    rw [twoPowerExpression_sq, Int.cast_one]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [twoPowerFiveOrder k hk]
    have hpow : 2^(k-2) = 2 * 2^(k-3) := by
      rw [show k-2 = k-3+1 by omega, pow_succ, Nat.mul_comm]
    rw [hpow]
    exact ⟨q.2.val, by ring⟩⟩

/-- The four square roots of one, expressed by the two sign choices and
the two exponent choices in the established unit parametrization. -/
theorem twoPower_roots_one (k : ℕ) (hk : 3 ≤ k) :
    quadraticRootCount (2^k) 1 = 4 := by
  have hpow : 2^(k-2) = 2 * 2^(k-3) := by
    rw [show k-2 = k-3+1 by omega, pow_succ, Nat.mul_comm]
  have hpos : 0 < 2^(k-3) := by positivity
  have hbound (c : Fin 2) : c.val * 2^(k-3) < 2^(k-2) := by
    rw [hpow]
    exact Nat.mul_lt_mul_of_pos_right c.isLt hpos
  have hf : Function.Bijective (kernelParameter k hk) := by
    constructor
    · intro q r hqr
      have he := congrArg Subtype.val hqr
      have hh := expression_injective k hk
        (a₁ := (q.1, ⟨q.2.val * 2^(k-3), hbound q.2⟩))
        (a₂ := (r.1, ⟨r.2.val * 2^(k-3), hbound r.2⟩)) he
      refine Prod.ext ?_ ?_
      · exact congrArg (fun z : Fin 2 × Fin (2^(k-2)) => z.1) hh
      · apply Fin.ext
        have h := congrArg (fun p : Fin 2 × Fin (2^(k-2)) => p.2.val) hh
        exact Nat.eq_of_mul_eq_mul_right hpos h
    · intro x
      have hx : x.val*x.val = 1 := by simpa only [pow_two, Int.cast_one] using x.property
      let u : (ZMod (2^k))ˣ := Units.mkOfMulEqOne x.val x.val hx
      obtain ⟨⟨a,b⟩, hab, _⟩ := twoPowerUniqueRepresentation k hk u
      have hxrep : twoPowerExpression k a.val b.val = x.val := hab
      have hb : b.val = 0 ∨ b.val = 2^(k-3) := by
        apply (exponent_square_one k hk b).mp
        rw [← twoPowerExpression_sq, hxrep]
        simpa using x.property
      rcases hb with hb | hb
      · refine ⟨(a,0), Subtype.ext ?_⟩
        change twoPowerExpression k a.val (0 * 2^(k-3)) = x.val
        simpa only [zero_mul, hb] using hxrep
      · refine ⟨(a,1), Subtype.ext ?_⟩
        change twoPowerExpression k a.val (1 * 2^(k-3)) = x.val
        simpa only [one_mul, hb] using hxrep
  have hcard := Nat.card_eq_of_bijective _ hf
  simpa only [quadraticRootCount, Nat.card_prod, Nat.card_fin] using hcard.symm

/-- Multiplication by a given unit square root identifies its fibre with
the square roots of one. -/
private def rootFibreEquivOne (m : ℕ) (a : ℤ) (r : (ZMod m)ˣ)
    (hr : (r : ZMod m)^2 = (a : ZMod m)) :
    QuadraticRoots m a ≃ QuadraticRoots m 1 where
  toFun x := ⟨x.val * (↑r⁻¹ : ZMod m), by
    rw [mul_pow, x.property, ← hr, ← mul_pow]
    simp⟩
  invFun x := ⟨x.val * (r : ZMod m), by
    rw [mul_pow, x.property, Int.cast_one, one_mul, hr]⟩
  left_inv x := by apply Subtype.ext; simp [mul_assoc]
  right_inv x := by apply Subtype.ext; simp [mul_assoc]

private theorem eight_dvd_two_pow (k : ℕ) (hk : 3 ≤ k) : 8 ∣ 2^k :=
  show 2^3 ∣ 2^k from pow_dvd_pow 2 hk

/-- A class equal to one modulo eight has a unit square root modulo every
higher power of two. No simple-root lifting at the prime two is used. -/
theorem twoPower_square_of_one_mod_eight (k : ℕ) (hk : 3 ≤ k) (a : ℤ)
    (ha : a ≡ 1 [ZMOD 8]) :
    ∃ r : (ZMod (2^k))ˣ, (r : ZMod (2^k))^2 = (a : ZMod (2^k)) := by
  have ha8 : (a : ZMod 8) = 1 := by
    simpa using (ZMod.intCast_eq_intCast_iff a 1 8).mpr ha
  have ha4 : (a : ZMod 4) = 1 := by
    have h := congrArg (ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4)) ha8
    simpa only [map_intCast, map_one] using h
  have hx4 : (ZMod.cast (a : ZMod (2^k)) : ZMod 4) = 1 := by
    change ZMod.castHom (show 4 ∣ 2^k from pow_dvd_pow 2 (by omega : 2 ≤ k))
      (ZMod 4) (a : ZMod (2^k)) = 1
    simpa only [map_intCast] using ha4
  obtain ⟨b, hb⟩ := (twoPowerFiveExhaustion k hk (a : ZMod (2^k))).mp hx4
  have hb8 : (5 : ZMod 8)^b.val = 1 := by
    have h := congrArg (ZMod.castHom (eight_dvd_two_pow k hk) (ZMod 8)) hb
    simpa only [map_intCast, map_pow, map_ofNat, ha8] using h.symm
  have heven : 2 ∣ b.val := by
    have h := orderOf_dvd_iff_pow_eq_one.mpr hb8
    have ho : orderOf (5 : ZMod 8) = 2 := by
      simpa using twoPowerFiveOrder 3 (by decide)
    rwa [ho] at h
  let u : (ZMod (2^k))ˣ := ZMod.unitOfCoprime 5 (by
    apply Nat.Coprime.pow_right
    decide)
  refine ⟨u^(b.val/2), ?_⟩
  change ((u : ZMod (2^k))^(b.val/2))^2 = _
  rw [show (u : ZMod (2^k)) = 5 from rfl, ← pow_mul, Nat.div_mul_cancel heven]
  exact hb.symm

/-- A root of an odd integer must reduce to an odd square modulo eight. -/
theorem twoPower_root_implies_one_mod_eight (k : ℕ) (hk : 3 ≤ k)
    (a : ℤ) (ha : ¬(2 : ℤ) ∣ a) (x : QuadraticRoots (2^k) a) :
    a ≡ 1 [ZMOD 8] := by
  let y : ZMod 8 := ZMod.castHom (eight_dvd_two_pow k hk) (ZMod 8) x.val
  have hy : y^2 = (a : ZMod 8) := by
    have h := congrArg (ZMod.castHom (eight_dvd_two_pow k hk) (ZMod 8)) x.property
    simpa only [map_pow, map_intCast] using h
  have ha2 : (a : ZMod 2) ≠ 0 :=
    fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp h)
  have hy2 : ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) (y^2) ≠ 0 := by
    rw [hy, map_intCast]
    exact ha2
  have hfinite : ∀ z : ZMod 8,
      ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) (z^2) ≠ 0 → z^2 = 1 := by decide
  have ha8 : (a : ZMod 8) = 1 := hy.symm.trans (hfinite y hy2)
  exact (ZMod.intCast_eq_intCast_iff a 1 8).mp (by simpa using ha8)

theorem twoPowerUnitRootCount : TwoPowerUnitRootCount := by
  classical
  intro j hj a ha
  by_cases h : a ≡ 1 [ZMOD 8]
  · rw [ite_eq_left h]
    obtain ⟨r, hr⟩ := twoPower_square_of_one_mod_eight j hj a h
    calc
      quadraticRootCount (2^j) a = quadraticRootCount (2^j) 1 :=
        Nat.card_congr (rootFibreEquivOne (2^j) a r hr)
      _ = 4 := twoPower_roots_one j hj
  · rw [ite_eq_right h]
    have : IsEmpty (QuadraticRoots (2^j) a) :=
      ⟨fun x => h (twoPower_root_implies_one_mod_eight j hj a ha x)⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

end UnitQuadratic

theorem oddPrimeUnitRootCount : OddPrimeUnitRootCount :=
  UnitQuadratic.oddPrimeUnitRootCount

theorem twoUnitRootCount : TwoUnitRootCount :=
  UnitQuadratic.twoUnitRootCount

theorem fourUnitRootCount : FourUnitRootCount :=
  UnitQuadratic.fourUnitRootCount

theorem twoPowerUnitRootCount : TwoPowerUnitRootCount :=
  UnitQuadratic.twoPowerUnitRootCount

end P203.Ch02
