import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.FareyMediants
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Farey sets and the determinant-one mediant lemma from `paper.tex`,
§5 Farey fractions. The finite pair encoding is bridged to ordinary rational
numbers by `fareyRationalMembership` and `reducedInjectivity`. -/
namespace P203.Ch05
open P203Specs.Ch05

def farey : FareyType := P203Specs.Ch05.farey

def orderedNeighbors : OrderedNeighborsType := P203Specs.Ch05.orderedNeighbors

lemma fraction_lt_iff {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d) :
    fractionValue (a,b) < fractionValue (c,d) ↔ a*d < c*b := by
  unfold fractionValue
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hb' hd']
  exact_mod_cast (Iff.rfl : a*d < c*b ↔ a*d < c*b)

theorem fareyMembership : FareyMembership := by
  intro N x
  rcases x with ⟨a,b⟩
  simp only [P203Specs.Ch05.farey, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_Icc, Reduced, fractionValue]
  constructor
  · rintro ⟨⟨⟨ha, haN⟩, hb, hbN⟩, hab, hg⟩
    have hb' : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
    refine ⟨⟨by omega, hg⟩, div_nonneg (by exact_mod_cast ha) hb'.le, ?_, hbN⟩
    rw [div_le_one hb']
    exact_mod_cast hab
  · rintro ⟨⟨hb, hg⟩, ha, hab, hbN⟩
    have hb' : (0 : ℚ) < b := by exact_mod_cast hb
    have ha0 : 0 ≤ a := by
      have ha' : (0 : ℚ) ≤ a := by simpa using (le_div_iff₀ hb').mp ha
      exact_mod_cast ha'
    have hab' : a ≤ b := by exact_mod_cast ((div_le_one hb').mp hab)
    exact ⟨⟨⟨ha0, le_trans hab' hbN⟩, by omega, hbN⟩, hab', hg⟩

theorem fareyRationalMembership : FareyRationalMembership := by
  intro N r
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hred, hlo, hhi, hN⟩ := (fareyMembership N x).mp hx
    have hden : ((fractionValue x).den : ℤ) = x.2 :=
      Rat.den_div_eq_of_coprime hred.1 hred.2
    exact ⟨hlo, hhi, by rwa [hden]⟩
  · rintro ⟨hlo, hhi, hN⟩
    have hval : fractionValue (r.num, (r.den : ℤ)) = r := by
      simpa [fractionValue] using Rat.num_div_den r
    have hred : Reduced (r.num, (r.den : ℤ)) := by
      refine ⟨by dsimp; exact_mod_cast r.den_pos, ?_⟩
      simpa only [Int.gcd_def, Int.natAbs_natCast] using r.reduced
    refine ⟨(r.num, (r.den : ℤ)), (fareyMembership N _).mpr ?_, hval⟩
    exact ⟨hred, by rwa [hval], by rwa [hval], hN⟩

theorem fareyEndpoints : FareyEndpoints := by
  intro N hN
  simp [P203Specs.Ch05.farey, hN, show (0 : ℤ) ≤ N by omega]

theorem reducedInjectivity : ReducedInjectivity := by
  intro x y hx hy h
  obtain ⟨ha,hb⟩ := Rat.div_int_inj hx.1 hy.1 hx.2 hy.2 h
  exact Prod.ext ha hb

theorem mediantDeterminants : MediantDeterminants := by
  intro a b c d h
  constructor <;> nlinarith

theorem mediantReduced : MediantReduced := by
  intro a b c d hb hd h
  refine ⟨by dsimp; omega, ?_⟩
  have hdiv : (Int.gcd (a+c) (b+d) : ℤ) ∣ 1 := by
    rw [← (mediantDeterminants a b c d h).1]
    exact dvd_sub
      (dvd_mul_of_dvd_right (Int.gcd_dvd_left (a+c) (b+d)) b)
      (dvd_mul_of_dvd_right (Int.gcd_dvd_right (a+c) (b+d)) a)
  have hdiv' : Int.gcd (a+c) (b+d) ∣ 1 := by exact_mod_cast hdiv
  exact Nat.dvd_one.mp hdiv'

theorem mediantInterior : MediantInterior := by
  intro a b c d hb hd h
  have hbd : 0 < b+d := by omega
  constructor
  · rw [fraction_lt_iff hb hbd]
    nlinarith
  · rw [fraction_lt_iff hbd hd]
    nlinarith

theorem interiorDenominator : InteriorDenominator := by
  intro a b c d p q hb hd hq hdet hleft hright
  -- The positive integer basis coefficients from the source proof.
  have hv : 1 ≤ b*p-a*q := by
    have := (fraction_lt_iff hb hq).mp hleft
    nlinarith
  have hu : 1 ≤ c*q-d*p := by
    have := (fraction_lt_iff hq hd).mp hright
    nlinarith
  have hqrep : q = (c*q-d*p)*b+(b*p-a*q)*d := by
    calc
      q = q*(b*c-a*d) := by rw [hdet]; ring
      _ = _ := by ring
  have hprep : p = (c*q-d*p)*a+(b*p-a*q)*c := by
    calc
      p = p*(b*c-a*d) := by rw [hdet]; ring
      _ = _ := by ring
  have hub : 0 ≤ (c*q-d*p-1)*b := mul_nonneg (by omega) hb.le
  have hvd : 0 ≤ (b*p-a*q-1)*d := mul_nonneg (by omega) hd.le
  refine ⟨by nlinarith [hqrep], ?_⟩
  constructor
  · intro heq
    have hub0 : (c*q-d*p-1)*b = 0 := by nlinarith [hqrep]
    have hvd0 : (b*p-a*q-1)*d = 0 := by nlinarith [hqrep]
    have hu1 : c*q-d*p = 1 := by
      have := (mul_eq_zero.mp hub0).resolve_right (ne_of_gt hb)
      omega
    have hv1 : b*p-a*q = 1 := by
      have := (mul_eq_zero.mp hvd0).resolve_right (ne_of_gt hd)
      omega
    exact ⟨by rw [hu1, hv1] at hprep; simpa using hprep, heq⟩
  · exact And.right

theorem mediantUniqueMinimum : MediantUniqueMinimum := by
  intro a b c d hab hcd hlt hdet
  have hred := mediantReduced a b c d hab.1 hcd.1 hdet
  have hint := mediantInterior a b c d hab.1 hcd.1 hdet
  refine ⟨(a+c,b+d), ⟨hred, hint.1, hint.2, ?_⟩, ?_⟩
  · intro y hy hyl hyr
    exact (interiorDenominator a b c d y.1 y.2 hab.1 hcd.1 hy.1 hdet hyl hyr).1
  · intro x hx
    have hbound := interiorDenominator a b c d x.1 x.2 hab.1 hcd.1 hx.1.1 hdet hx.2.1 hx.2.2.1
    have heq : x.2 = b+d := le_antisymm (hx.2.2.2 _ hred hint.1 hint.2) hbound.1
    obtain ⟨ha,hb⟩ := hbound.2.mp heq
    exact Prod.ext ha hb

end P203.Ch05
