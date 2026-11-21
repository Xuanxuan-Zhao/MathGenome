import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.LinearDiophantine
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch01.GcdBezoutLcm
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace P203.Ch01

theorem linearSolvability : P203Specs.Ch01.LinearSolvability := by
  intro a b c
  constructor
  · rintro ⟨x,y,rfl⟩
    exact Int.dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left a b) x)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right a b) y)
  · rintro ⟨k, hk⟩
    obtain ⟨u,v,huv⟩ := (gcdBezout a b).2.2.2.2.1
    refine ⟨u*k,v*k,?_⟩
    rw [hk, huv]
    ring

/-- Dividing a Bézout identity by a nonzero gcd yields a primitive pair.
Using that identity directly avoids any exception when a coefficient is zero. -/
theorem primitiveKernel (A B X Y : ℤ) (h : Int.gcd A B = 1)
    (heq : A*X+B*Y=0) : ∃ t : ℤ, X=B*t ∧ Y= -A*t := by
  have huv := Int.gcd_eq_gcd_ab A B
  rw [h] at huv
  norm_num only [Nat.cast_one] at huv
  refine ⟨Int.gcdB A B*X-Int.gcdA A B*Y, ?_, ?_⟩
  · linear_combination X*huv + Int.gcdA A B*heq
  · linear_combination Y*huv + Int.gcdB A B*heq

theorem linearSolutions : P203Specs.Ch01.LinearSolutions := by
  intro a b c x₀ y₀ hd h₀ x y
  let d : ℤ := Int.gcd a b
  have ha : a/d*d=a := Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
  have hb : b/d*d=b := Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hcop : Int.gcd (a/d) (b/d) = 1 :=
    Int.gcd_ediv_gcd_ediv_gcd (by exact_mod_cast hd)
  constructor
  · intro hxy
    have heq : (a/d)*(x-x₀)+(b/d)*(y-y₀)=0 := by
      apply mul_left_cancel₀ hd0
      calc
        d*((a/d)*(x-x₀)+(b/d)*(y-y₀)) = a*x+b*y-(a*x₀+b*y₀) := by
          linear_combination (x-x₀)*ha + (y-y₀)*hb
        _ = d*0 := by rw [hxy,h₀]; ring
    obtain ⟨t,htx,hty⟩ := primitiveKernel (a/d) (b/d) (x-x₀) (y-y₀) hcop heq
    exact ⟨t, by dsimp [d] at htx ⊢; linear_combination htx,
      by dsimp [d] at hty ⊢; linear_combination hty⟩
  · rintro ⟨t,rfl,rfl⟩
    change a*(x₀+(b/d)*t)+b*(y₀-(a/d)*t)=c
    have hcross : a*(b/d)=b*(a/d) := by
      calc
        a*(b/d) = (a/d*d)*(b/d) := by rw [ha]
        _ = (b/d*d)*(a/d) := by ring
        _ = b*(a/d) := by rw [hb]
    linear_combination h₀ + t*hcross

theorem zeroLinearEquation : P203Specs.Ch01.ZeroLinearEquation := by
  intro a b h
  have ha : a = 0 := by
    have := Int.gcd_dvd_left a b
    simpa [h] using this
  have hb : b = 0 := by
    have := Int.gcd_dvd_right a b
    simpa [h] using this
  refine ⟨ha,hb,?_⟩
  simp [ha,hb,eq_comm]

/-- The sign in the congruence convention is absorbed into the second witness. -/
theorem congruence_iff_equation (a b m x : ℤ) :
    (m ∣ a*x-b) ↔ ∃ y : ℤ, a*x+m*y=b := by
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨-k, by linear_combination hk⟩
  · rintro ⟨y,hy⟩
    exact ⟨-y, by linear_combination hy⟩

theorem congruenceSolvability : P203Specs.Ch01.CongruenceSolvability := by
  intro a b m _
  simpa only [congruence_iff_equation] using linearSolvability a m b

theorem congruenceSolutions : P203Specs.Ch01.CongruenceSolutions := by
  intro a b m x₀ hm h₀ x
  obtain ⟨y₀,hy₀⟩ := (congruence_iff_equation a b m x₀).mp h₀
  have hd : 0 < (Int.gcd a m : ℤ) := by
    exact_mod_cast Int.gcd_pos_of_ne_zero_right a (ne_of_gt hm)
  rw [congruence_iff_equation]
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨t,ht,_⟩ := (linearSolutions a m b x₀ y₀ hd hy₀ x y).mp hy
    exact ⟨t,ht⟩
  · rintro ⟨t,rfl⟩
    refine ⟨y₀-(a/(Int.gcd a m : ℤ))*t, ?_⟩
    exact (linearSolutions a m b x₀ y₀ hd hy₀ _ _).mpr ⟨t,rfl,rfl⟩

/-- Parameter congruence for an arithmetic progression of step k and modulus k*d. -/
theorem progression_modulus (m d k x₀ t s : ℤ) (hk : k*d=m) (hk0 : k ≠ 0) :
    (m ∣ (x₀+k*t)-(x₀+k*s)) ↔ d ∣ t-s := by
  rw [show (x₀+k*t)-(x₀+k*s) = k*(t-s) by ring, ← hk]
  exact ⟨Int.dvd_of_mul_dvd_mul_left hk0, fun h => mul_dvd_mul_left k h⟩

/-- In the canonical interval of residues, congruence is equality. -/
theorem fin_congruent_iff (d : ℕ) (i j : Fin d) :
    ((d : ℤ) ∣ (i.val : ℤ)-j.val) ↔ i=j := by
  constructor
  · intro h
    have heq : (i.val : ℤ) % d = (j.val : ℤ) % d :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h)
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast i.isLt),
      Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast j.isLt)] at heq
    exact Fin.ext (by exact_mod_cast heq)
  · rintro rfl
    simp

theorem congruenceClassCount : P203Specs.Ch01.CongruenceClassCount := by
  intro a b m hm hsol
  obtain ⟨x₀,h₀⟩ := hsol
  let d : ℤ := Int.gcd a m
  let k : ℤ := m/d
  have hd : 0 < d := by
    change 0 < (Int.gcd a m : ℤ)
    exact_mod_cast Int.gcd_pos_of_ne_zero_right a (ne_of_gt hm)
  have hk : k*d=m := Int.ediv_mul_cancel (Int.gcd_dvd_right a m)
  have hk0 : k ≠ 0 := by
    intro h
    rw [h,zero_mul] at hk
    omega
  let reps : Fin (Int.gcd a m) → ℤ := fun i => x₀+k*i.val
  refine ⟨reps, ?_, ?_, ?_⟩
  · intro i
    exact (congruenceSolutions a b m x₀ hm h₀ _).mpr ⟨i.val,rfl⟩
  · intro i j
    exact (progression_modulus m d k x₀ i.val j.val hk hk0).trans
      (fin_congruent_iff (Int.gcd a m) i j)
  · intro x hx
    obtain ⟨t,ht⟩ := (congruenceSolutions a b m x₀ hm h₀ x).mp hx
    have ht0 : 0 ≤ t % d := Int.emod_nonneg t (ne_of_gt hd)
    have htlt : t % d < d := Int.emod_lt_of_pos t hd
    let i : Fin (Int.gcd a m) := ⟨(t % d).toNat, by dsimp [d] at *; omega⟩
    have hi : (i.val : ℤ) = t % d := Int.toNat_of_nonneg ht0
    refine ⟨i, ?_⟩
    change m ∣ x-(x₀+k*i.val)
    rw [ht]
    apply (progression_modulus m d k x₀ t i.val hk hk0).mpr
    rw [hi]
    exact Int.dvd_self_sub_emod

end P203.Ch01
